package fr.irisa.circag.tchecker

import collection.JavaConverters._
import collection.convert.ImplicitConversions._
import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.ListBuffer
import scala.collection.mutable.Buffer
import scala.sys.process._
import scala.io
import scala.collection.mutable.StringBuilder
import scala.collection.mutable.HashMap

import java.io.File
import java.io.InputStream
import java.nio.file._
import java.io.PrintWriter
import java.io.ByteArrayInputStream

import net.automatalib.automata.Automaton
import net.automatalib.automata.fsa.FiniteStateAcceptor

import fr.irisa.circag.{LTS, DLTS, Trace, HOA}
/** 
 *  Light parser that reads TChecker TA from given file, and stores the tuple (events,
  * eventsOfProcesses, core, syncs) where 
  * - events is the list of all events,
  * - eventsOfProcesses maps process names to events that they include, 
  * - core is the list of lines of the input file except for the system name, events, and sync instructions,
  * - syncs contains lists of tuples encoding the syncs
  */
class TA (
  var systemName : String = "",
  var alphabet: Set[String] = Set(),
  var internalAlphabet: Set[String] = Set(),
  var core: String = "",
  var eventsOfProcesses : HashMap[String, Set[String]] = HashMap[String, Set[String]](),
  var syncs : List[List[(String, String)]] = List[List[(String, String)]]()){

  def getProcessNames() : List[String] = {
    eventsOfProcesses.keys().toList
  }

  override def toString(): String = {
    val sb = StringBuilder()
    sb.append(s"system:${systemName}\n\n")
    for sigma <- alphabet do {
      sb.append(s"event:${sigma}\n")
    }
    sb.append("\n")
    sb.append(core)
    for sync <- syncs do {
      sb.append("sync:" + sync.map(_ + "@" + _).mkString(":") + "\n")
    }
    sb.toString()
  }

}

object TA{
  def fromFile(inputFile: java.io.File) : TA = {
    val ta = TA()
    val lines = scala.io.Source.fromFile(inputFile).getLines().toList
    val regEvent = "\\s*event:([^ ]*).*".r
    val regSync = "\\s*sync:(.*)\\s*".r
    val regProcess = "\\s*process:(.*)\\s*".r
    val regEdge = "\\s*edge:[^:]*:[^:]*:[^:]*:([^{]*).*".r
    val regSystem = "\\s*system:([^ ]*).*".r
    // System.out.println("File: " + inputFile.toString)
    ta.alphabet = lines.flatMap({
      case regEvent(event) if !event.startsWith("_") => Some(event.strip())
      case _               => None
    }).toSet
    ta.internalAlphabet = lines.flatMap({
      case regEvent(event) if event.startsWith("_") => Some(event.strip())
      case _               => None
    }).toSet
    ta.syncs = lines.flatMap({
      case regSync(syncs) =>
        Some(
          syncs
            .split(":")
            .toList
            .map(
              { l =>
                val elts = l.split("@").map(_.strip()).toArray
                (elts(0), elts(1))
              }
            )
        )
      case _ => None
    })

    ta.eventsOfProcesses = HashMap[String, Set[String]]()
    var currentProcess = ""
    lines.foreach {
      case regProcess(monitorProcessName) =>
        currentProcess = monitorProcessName
        ta.eventsOfProcesses += (monitorProcessName -> Set[String]())
      // System.out.println("Now reading process: " + monitorProcessName)
      case regEdge(sync) =>
        ta.eventsOfProcesses.put(currentProcess,
          (ta.eventsOfProcesses(currentProcess) + sync))
      // System.out.println("Adding sync: " + sync)
      case _ => ()
    }
    ta.core = lines.filter({
      case regSystem(name) => ta.systemName = name; false
      case regEvent(event) => false
      case regSync(event) => false
      case _               => true
    }).mkString("\n")
    return ta
  }

  def fromLTS(dlts : LTS[? <: FiniteStateAcceptor[?, String] with Automaton[?, String, ?]], acceptingLabelSuffix : Option[String] = None) : TA = {
    val ta = TA(dlts.name, dlts.alphabet.toSet)
    ta.eventsOfProcesses += (dlts.name -> ta.alphabet )
    val strStates = StringBuilder()  
    val strTransitions = StringBuilder()
    val initStates = dlts.dfa.getInitialStates().asScala
    strStates.append("process:" + dlts.name + "\n")
    dlts.dfa
      .getStates()
      .asScala
      .foreach(state =>
        {
          strStates
            .append("location:%s:q%s{".format(dlts.name, state.toString))
          val attributes = ArrayBuffer[String]()
          if (initStates.contains(state)) then {
            attributes.append("initial:")
          }
          if (dlts.dfa.isAccepting(state)) {
            acceptingLabelSuffix match {
              case Some(l) => attributes.append(s"labels:${dlts.name + l}")
              case _ => ()
            }
          }
          strStates.append(attributes.mkString(":"))
          strStates.append("}\n")
          for (sigma <- ta.alphabet) {
            val succs = dlts.dfa.getSuccessors(state, sigma);
            if (!succs.isEmpty()) then {
              for (succ <- succs) {
                strTransitions.append(
                  "edge:%s:q%s:q%s:%s\n".format(
                    dlts.name,
                    state.toString,
                    succ.toString,
                    sigma
                  )
                )
              }
            }
          }
        }
      )
      // If there is no accepting states, add a dummy accepting state
      if !dlts.dfa.getStates().exists({s => dlts.dfa.isAccepting(s)}) then {
        acceptingLabelSuffix match {
          case Some(l) =>
            strStates
              .append(s"location:${dlts.name}:_dummy_state_{labels:${dlts.name + l}}\n")
          case _ => ()
        }        
      }
      val taB = StringBuilder()
      if dlts.comments != "" then {
        dlts.comments.split("\n").foreach({ x => taB.append(s"# ${x}")})
      }
      taB.append(ta.core)
      taB.append("\n")
      taB.append(strStates.append(strTransitions.toString).toString)
    ta.core = taB.toString()
    ta
  }
    def fromHOA(automatonString : String, acceptingLabel : Option[String]) : TA = {
        TA.fromLTS(HOA.toLTS(automatonString), acceptingLabel)
    }

  /**
    * @param ta timed automaton
    * @param dlts list of DLTSs with which sync product is to be computed
    * @param acceptingLabelSuffix if Some(suffix), then accepting states of each DLTS are labeled by name_suffix.
    * @pre ta.systemName and dlts.name's are pairwise distinct
    * @return
    */
  def synchronousProduct(ta : TA, dlts : List[DLTS], acceptingLabelSuffix : Option[String] = None) : TA = {
    val allNames = dlts.map(_.name) ++ ta.eventsOfProcesses.keys().toList
    if allNames.size > allNames.distinct.size then {
      throw Exception("Attempting synchronous product of processes of the same name")
    }
    //if dlts.map(_.name).distinct.size < dlts.size || dlts.map(_.name).contains(ta.systemName) then {
    val dltsTA = dlts.map({d => this.fromLTS(d, acceptingLabelSuffix)})
    val jointAlphabet = ta.alphabet | dlts.foldLeft(Set[String]())( (alph, d) => alph | d.alphabet)
    val sb = StringBuilder()
    val systemName = s"_premise_${ta.systemName}"
    sb.append(ta.core)
    dltsTA.foreach({d => sb.append(d.core); sb.append("\n")})
    val eventsOfProcesses = HashMap[String,Set[String]]()
    dlts.foreach({d => eventsOfProcesses += (d.name -> d.alphabet.toSet)})
    ta.eventsOfProcesses.foreach({(p,e) => eventsOfProcesses += (p -> e)})
    val allProcesses = eventsOfProcesses.keys.toList
    val syncs = jointAlphabet.map(
      sigma => 
        allProcesses.filter(eventsOfProcesses(_).contains(sigma))
        .map({process => (process,sigma)})
    ).toList.filter(_.size > 1)
    TA(systemName, jointAlphabet, ta.internalAlphabet, sb.toString(), eventsOfProcesses, syncs)
  }

  def synchronousProduct(tas : List[TA]) : TA = {
    require(tas.size > 0)
    val allProcesses = (tas.map(_.eventsOfProcesses.keys().toSet)).foldLeft(Set[String]())({(a,b) => a | b}).toList
    val processCount = (tas.map(_.eventsOfProcesses.keys().size)).sum
    if allProcesses.size < processCount then {
      throw Exception("Attempting synchronous product of processes of the same name")
    }
    val jointAlphabet = tas.foldLeft(Set[String]())((alph,ta) => alph | ta.alphabet)
    val jointInternalAlphabet = tas.foldLeft(Set[String]())((alph,ta) => alph | ta.internalAlphabet)
    val sb = StringBuilder()
    val systemName = s"_product_"
    tas.foreach({d => sb.append(d.core); sb.append("\n")})
    val eventsOfProcesses = HashMap[String,Set[String]]()
    tas.foreach({_.eventsOfProcesses.foreach({(p,e) => eventsOfProcesses.put(p, e)})})
    val syncs = jointAlphabet.map(
      sigma => 
        allProcesses.filter(eventsOfProcesses(_).contains(sigma))
        .map({process => (process,sigma)})
    ).toList.filter(_.size > 1)
    TA(systemName, jointAlphabet, jointInternalAlphabet, sb.toString(), eventsOfProcesses, syncs)
  }


  /** 
   *  Given the counterexample description output by TChecker, given as a list of lines,
   *  return the trace, that is, the sequence of events in the alphabet encoded by the said counterexample.
   */
  def getTraceFromCounterExampleOutput(cexDescription : List[String], events : Set[String]) : Trace = {
      val word = ListBuffer[String]()
      val regEdge = ".*->.*vedge=\"<(.*)>\".*".r
      cexDescription.foreach({
        case regEdge(syncList) => 
          val singleSync = syncList.split(",").map(_.split("@")(1)).toSet.intersect(events)
          if (singleSync.size == 1){
            val a = singleSync.toArray
            word.append(a(0))
          } else if (singleSync.size > 1){
            throw FailedTAModelChecking("The counterexample trace has a transition with syncs containing more than one letter of the alphabet:\n" + syncList)
          } else {
            // Ignore internal transition
          }
        case _ => ()
      })
      word.toList
  }
}

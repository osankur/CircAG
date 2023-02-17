package fr.irisa.circag.tchecker

import io.AnsiColor._
import org.slf4j.Logger
import org.slf4j.LoggerFactory
import collection.JavaConverters._
import collection.convert.ImplicitConversions._
import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.ListBuffer
import scala.collection.mutable.Buffer
import scala.sys.process._
import scala.io.Source
import scala.collection.mutable.StringBuilder
import scala.collection.mutable.HashMap
import de.learnlib.util.MQUtil;
import java.io.File
import java.io.InputStream
import java.nio.file._
import java.io.PrintWriter
import java.io.ByteArrayInputStream
import de.learnlib.api.oracle.EquivalenceOracle
import de.learnlib.api.query.DefaultQuery;
import de.learnlib.api.oracle._
import de.learnlib.api.oracle.MembershipOracle
import de.learnlib.api.oracle.MembershipOracle.DFAMembershipOracle
import net.automatalib.automata.fsa.impl.compact.CompactDFA;
import net.automatalib.util.automata.builders.AutomatonBuilders;
import net.automatalib.automata.fsa.DFA
import net.automatalib.util.automata.fsa.NFAs
import net.automatalib.util.automata.fsa.DFAs
import net.automatalib.words.impl.Alphabets;
import net.automatalib.words._
import net.automatalib.util.automata.builders.AutomatonBuilders;
import net.automatalib.visualization.Visualization;
import net.automatalib.automata.fsa.impl.compact.CompactNFA;
import net.automatalib.serialization.aut.AUTSerializationProvider 
import net.automatalib.automata.fsa.NFA

import fr.irisa.circag.DLTS
import fr.irisa.circag.Trace
import fr.irisa.circag.configuration
import fr.irisa.circag.statistics

case class BadTimedAutomaton(msg: String) extends Exception(msg)
case class FailedTAModelChecking(msg: String) extends Exception(msg)

trait AssumeGuaranteeOracles[LTS, Property] {
  def checkInductivePremises(lts : LTS, assumptions : List[Property], guarantee : Property) : Option[Trace]
  def checkFinalPremise(lhs : List[Property], p : Property) : Option[Trace]
  def extendTrace(lts : LTS, word : Trace, extendedAlphabet : Set[String]) : Trace
}

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
  var events: Set[String] = Set(),
  var core: String = "",
  var eventsOfProcesses : HashMap[String, Set[String]] = HashMap[String, Set[String]](),
  var syncs : List[List[(String, String)]] = List[List[(String, String)]]()){

  def getProcessNames() : List[String] = {
    eventsOfProcesses.keys().toList
  }

  def alphabet() : Alphabet[String] = {
    Alphabets.fromList(events.toList)
  }

  override def toString(): String = {
    val sb = StringBuilder()
    sb.append(s"system:${systemName}\n\n")
    for sigma <- events do {
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
    val lines = Source.fromFile(inputFile).getLines().toList
    val regEvent = "\\s*event:([^ ]*).*".r
    val regSync = "\\s*sync:(.*)\\s*".r
    val regProcess = "\\s*process:(.*)\\s*".r
    val regEdge = "\\s*edge:[^:]*:[^:]*:[^:]*:([^{]*).*".r
    val regSystem = "\\s*system:([^ ]*).*".r
    // System.out.println("File: " + inputFile.toString)
    ta.events = lines.flatMap({
      case regEvent(event) => Some(event.strip())
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
        ta.eventsOfProcesses += (currentProcess -> (ta.eventsOfProcesses(
          currentProcess
        ) + sync))
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

  def fromDLTS(dlts : DLTS, acceptingLabelSuffix : Option[String] = None) : TA = {
    val ta = TA(dlts.name, dlts.alphabet.toSet)
    ta.eventsOfProcesses += (dlts.name -> ta.events )
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
          for (sigma <- ta.events) {
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
      val taB = StringBuilder()
      taB.append(ta.core)
      taB.append("\n")
      taB.append(strStates.append(strTransitions.toString).toString)
    ta.core = taB.toString()
    ta
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
    val dltsTA = dlts.map({d => this.fromDLTS(d, acceptingLabelSuffix)})
    val jointAlphabet = ta.events | dlts.foldLeft(Set[String]())( (alph, d) => alph | d.alphabet.toSet)
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
    TA(systemName, jointAlphabet, sb.toString(), eventsOfProcesses, syncs)

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

object TCheckerAssumeGuaranteeOracles {
  
  /**
    * 
    *
    * @param lts
    * @param assumptions List of complete DFAs
    * @param guarantee
    * @pre guarantee.alphabet <= lts.alphabet
    * @return None if the premise holds; and Some(cexTrace) otherwise
    */
  def checkInductivePremises(ta : TA, assumptions : List[DLTS], guarantee : DLTS) : Option[Trace] =
    { 
      require(guarantee.alphabet.toSet.subsetOf(ta.alphabet().toSet))
      val compG = DLTS(s"_comp_${guarantee.name}", DFAs.complement(guarantee.dfa,guarantee.alphabet), guarantee.alphabet)
      val liftedAssumptions = 
        assumptions.map({ass => DLTS.liftAndStripNonAccepting(ass, ta.alphabet(), Some(s"lifted_${ass.name}"))})
      val premiseProduct = TA.synchronousProduct(ta, compG::liftedAssumptions, Some("_accept_"))
      val trace = checkReachability(premiseProduct, s"${compG.name}_accept_")
      trace
    }

  /**
    * Check the final premise, that is, whether /\_{dtls in lhs} dtls implies property.
    *
    * @param lhs
    * @param property
    * @return None if the premise holds; and Some(cexTrace) otherwise
    */
  def checkFinalPremise(lhs : List[DLTS], property : DLTS) : Option[Trace] = {
      val compG = DLTS(s"_comp_${property.name}", DFAs.complement(property.dfa,property.alphabet), property.alphabet)
      val premiseProduct = TA.synchronousProduct(TA.fromDLTS(compG, acceptingLabelSuffix=Some("_accept_")), lhs)
      // System.out.println(premiseProduct)
      checkReachability(premiseProduct, s"${compG.name}_accept_")      
  }
  /**
    * Attempt to find a trace in ta that synchronizes with word; the returned trace has alphabet word's alphabet | ta's alphabet.
    * 
    * @param ta
    * @param word
    * @param projectionAlphabet
    * @return
    */
  def extendTrace(ta : TA, word : Trace, projectionAlphabet : Option[Set[String]]) : Option[Trace] ={
    val wordDLTS = DLTS.fromTrace(word,None)
    val productTA = TA.synchronousProduct(ta, List(wordDLTS), acceptingLabelSuffix = Some("_accept_"))
    checkReachability(productTA, s"${wordDLTS.name}_accept_") 
    // match {
    //   case None => None
    //   case Some(exWord) => 
    //     (projectionAlphabet match 
    //       case None => Some(exWord)
    //       case Some(alph) => Some(exWord.filter(alph))
    //     )
    // }
  }

  /**
    * Check whether ta contains an exec whose trace, projected to projectionAlphabet is word.
    *
    * @param ta
    * @param word
    * @param projectionAlphabet
    * @return None if no such execution exists, and Some(execution) otherwise.
    */
  def checkTraceMembership(ta : TA, word : Trace, projectionAlphabet : Option[Set[String]]) : Option[Trace] = {  
    val traceProcess = DLTS.fromTrace(word, projectionAlphabet)
    val productTA = TA.synchronousProduct(ta, List(traceProcess), Some("_accept_"))
    val label = s"${traceProcess.name}_accept_"
    this.checkReachability(productTA, label)
  }

  def checkReachability(ta : TA, label : String) : Option[Trace] = {
    val modelFile =
      Files.createTempFile(configuration.get().getTmpDirPath(), "circag-query", ".ta").toFile()
    val pw = PrintWriter(modelFile)
    pw.write(ta.toString())
    pw.close()

    val certFile =
      Files.createTempFile(configuration.get().getTmpDirPath(), "circag-cert", ".cert").toFile()
    val cmd = "tck-reach -a reach %s -l %s -C %s"
            .format(modelFile.toString, label, certFile.toString)

    if configuration.globalConfiguration.verbose_MembershipQueries then
      System.out.println(cmd)

    val output = cmd.!!
    val cex = Source.fromFile(certFile).getLines().toList

    if (!configuration.globalConfiguration.keepTmpFiles){
      modelFile.delete()
      certFile.delete()
    }    
    if (output.contains("REACHABLE false")) then {
      None
    } else if (output.contains("REACHABLE true")) then {
      Some(TA.getTraceFromCounterExampleOutput(cex, ta.events))
    } else {
      throw FailedTAModelChecking(output)
    }
  }
}



class AssumeGuaranteeVerifier[LTS, Property](ltss : List[LTS], property : Property) {
  var assumptions : Array[List[Int]] = Array()

  def simplifyAssumptions() : Unit = {
  }
  def refineAssumptionAlphabet(trace : Trace) : Unit = {}
  def check() : Option[Trace] = {
    None
  }
}

class TCheckerAssumeGuaranteeVerifier(ltsFiles : Array[File], err : String) {
  private var assumptionAlphabet : List[String] = List()
  var assumptions : Buffer[DLTS] = Buffer()

  val propertyAlphabet = Alphabets.fromList(List[String](err))
  val processes = ltsFiles.map(TA.fromFile(_))
  private val errDFA : CompactDFA[String] = {
    AutomatonBuilders
      .newDFA(propertyAlphabet)
      .withInitial("q0")
      .from("q0")
      .on(err)
      .to("q1")
      .withAccepting("q0")
      .create();
  }
  val propertyDLTS = DLTS("property", errDFA, propertyAlphabet)

  def simplifyAssumptions() : Unit = {
  }
  def refineAssumptionAlphabet(trace : Trace) : Unit = {}
  def check() : Option[Trace] = {
    None
  }
}


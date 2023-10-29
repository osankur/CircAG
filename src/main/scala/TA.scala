package fr.irisa.circag
import org.slf4j.Logger
import org.slf4j.LoggerFactory

import collection.JavaConverters._
import collection.convert.ImplicitConversions._
import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.ListBuffer
import scala.collection.mutable.Buffer
import scala.collection.immutable.Set
import scala.collection.mutable
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
import net.automatalib.automata.fsa.impl.{FastDFA, FastNFA, FastDFAState, FastNFAState}
import net.automatalib.words.impl.Alphabets;

import fr.irisa.circag._
import fr.irisa.circag.ltl.LTL

case class BadTimedAutomaton(msg: String) extends Exception(msg)
case class FailedTAModelChecking(msg: String) extends Exception(msg)

/** 
  * Timed automaton representing a process.
  * Light weight representation storing the tuple 
  * (events, eventsOfProcesses, core, syncs) where 
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

  /**
   * Check the reachability of a state labeled by label. Return such a trace if any.
   * 
   * @param label
   */
  def checkReachability(label : String) : Option[Trace] = {
    val beginTime = System.nanoTime()    
    statistics.Counters.incrementCounter("model-checking")
    val modelFile =
      Files.createTempFile(configuration.get().getTmpDirPath(), "circag-query", ".ta").toFile()
    val pw = PrintWriter(modelFile)
    pw.write(this.toString())
    pw.close()

    val certFile =
      Files.createTempFile(configuration.get().getTmpDirPath(), "circag-cert", ".cert").toFile()
    val cmd = "tck-reach -a reach %s -l %s -C symbolic -o %s"
            .format(modelFile.toString, label, certFile.toString)

    TA.logger.debug(cmd)
    // System.out.println(cmd)

    val output = cmd.!!
    val cex = scala.io.Source.fromFile(certFile).getLines().toList

    if (!configuration.globalConfiguration.keepTmpFiles){
      modelFile.delete()
      certFile.delete()
    }    
    statistics.Timers.incrementTimer("tchecker", System.nanoTime() - beginTime)
    if (output.contains("REACHABLE false")) then {
      None
    } else if (output.contains("REACHABLE true")) then {
      Some(TA.getTraceFromCounterExampleOutput(cex, this.alphabet))
    } else {
      throw FailedTAModelChecking(output)
    }
  }

  /**
    * Check whether trace|_alph is accepted by ta|_alph where alph is syncAlphabet (default is trace.toSet)
    *
    * @param trace a trace
    * @param syncAlphabet alphabet on which synchronous product is to be defined
    * @return None if no such execution exists, and Some(trace) otherwise.
    */
  def checkTraceMembership(trace : Trace, syncAlphabet : Option[Set[String]] = None) : Option[Trace] = {  
    statistics.Counters.incrementCounter("trace-membership")
    val traceAlphabet = syncAlphabet.getOrElse(trace.toSet)
    val projTrace = trace.filter(traceAlphabet.contains(_))
    val traceProcess = DLTS.fromTrace(projTrace, Some(traceAlphabet))
    val productTA = TA.synchronousProduct(this, List(traceProcess), Some("_accept_"))
    val result = productTA.checkReachability(s"${traceProcess.name}_accept_")
    result
  }

  /**
    * @brief Check whether all infinite runs of the TA satisfy the LTL formula.
    *
    * @param ltlFormula
    * @return None if the formula is satisfied, and a counterexample lasso violating the formula otherwise.
    */
  def checkLTL(ltlFormula: LTL): Option[Lasso] = {
    val accLabel = "_ltl_accept_"
    val fullAlphabet = this.alphabet | ltlFormula.alphabet
    val ta_ltl = TA.fromLTL(ltl.Not(ltlFormula).toString, Some(fullAlphabet), Some(accLabel))
    val productTA = TA.synchronousProduct(List(this, ta_ltl))
    productTA.checkBuchi(s"${ta_ltl.systemName}${accLabel}")
  }
  /** Check the reachability of a state labeled by label. Return such a trace if
    * any.
    *
    * @param ta
    * @param label
    */
  def checkBuchi(label: String): Option[Lasso] = {
    val beginTime = System.nanoTime()
    statistics.Counters.incrementCounter("model-checking")
    val modelFile =
      Files
        .createTempFile(
          configuration.get().getTmpDirPath(),
          "circag-query",
          ".ta"
        )
        .toFile()
    val pw = PrintWriter(modelFile)
    pw.write(this.toString())
    pw.close()

    val certFile =
      Files
        .createTempFile(
          configuration.get().getTmpDirPath(),
          "circag-cert",
          ".cert"
        )
        .toFile()
    val cmd = "tck-liveness -a ndfs %s -C symbolic -l %s -o %s"
      .format(modelFile.toString, label, certFile.toString)
    System.out.println(cmd)
    TA.logger.debug(cmd)

    val output = cmd.!!
    val cex = scala.io.Source.fromFile(certFile).getLines().toList

    if (!configuration.globalConfiguration.keepTmpFiles) {
      modelFile.delete()
      certFile.delete()
    }
    statistics.Timers.incrementTimer("tchecker", System.nanoTime() - beginTime)
    // System.out.println(output)
    if (output.contains("CYCLE false")) then {
      None
    } else if (output.contains("CYCLE true")) then {
      Some(TA.getLassoFromCounterExampleOutput(cex, this.alphabet))
    } else {
      throw FailedTAModelChecking(output)
    }
  }

}

object TA{
  protected val logger = LoggerFactory.getLogger("CircAG")

  /** 
   * Parser that reads TChecker TA format. 
   */
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

  /**
   * Build a TA object that represents the given LTS.
   */
  def fromLTS[S](dlts : LTS[S], acceptingLabelSuffix : Option[String] = None) : TA = {
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

  /**
   * Build TA from the NLTS corresponding to the Buchi automaton given in the HOA format.
   * @param automatonString the Buchi automaton description in the HOA format
   * @param fullAlphabet if not None, an alphabet containing all symbols that appear in automatonString
   * @param acceptingLabel if not None, the label of the accepting states in the produced TA
   */
  def fromHOA(automatonString : String, fullAlphabet : Option[Alphabet], acceptingLabel : Option[String]) : TA = {
    TA.fromLTS[FastNFAState](NLTS.fromHOA(automatonString, fullAlphabet), acceptingLabel)
  }

  /**
   * Build a TA representing an NBA that recognizes the given LTL formula.
   */
  def fromLTL(ltlString : String, fullAlphabet : Option[Alphabet], acceptingLabel : Option[String] = None) : TA = {
    val nlts = NLTS.fromLTL(ltlString, fullAlphabet)
    this.fromLTS[FastNFAState](nlts, acceptingLabel)
  }



  /**
    * @param ta timed automaton
    * @param dlts list of DLTSs with which sync product is to be computed
    * @param acceptingLabelSuffix if Some(suffix), then accepting states of each DLTS are labeled by name_suffix.
    * @pre ta.systemName and dlts.name's are pairwise distinct
    * @return Product of ta and the given DLTS
    */
  def synchronousProduct(ta : TA, dlts : List[DLTS], acceptingLabelSuffix : Option[String] = None) : TA = {
    val allNames = dlts.map(_.name) ++ ta.eventsOfProcesses.keys().toList
    if allNames.size > allNames.distinct.size then {
      throw Exception("Attempting synchronous product of processes of the same name")
    }
    //if dlts.map(_.name).distinct.size < dlts.size || dlts.map(_.name).contains(ta.systemName) then {
    val dltsTA = dlts.map({d => this.fromLTS[FastDFAState](d, acceptingLabelSuffix)})
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

  /**
    * Synchronous product of the given TAs.
    * The TAs must have distinct process and variable names.
    * 
    * @param tas
    * @return
    */
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

  private def getGraphFromCounterExampleOutput(cexDescription : List[String], events : Set[String]) : (HashMap[Int,(String,Int)], HashMap[Int,Int]) = {
      val edges = HashMap[Int,(String,Int)]()
      val parents = HashMap[Int,Int]()
      val regEdge = "\\s*([0-9]+)\\s*->\\s*([0-9]+).*vedge=\"<(.*)>\".*".r
      cexDescription.foreach({
        case regEdge(src,tgt,syncList) => 
          val singleSync = syncList.split(",").map(_.split("@")(1)).toSet.intersect(events)
          if (singleSync.size == 1){
            val a = singleSync.toArray
            // word.append(a(0))
            edges.put(src.trim.toInt, (a(0), tgt.trim.toInt))
            parents.put(tgt.trim.toInt, src.trim.toInt)
          } else if (singleSync.size > 1){
            throw FailedTAModelChecking("The counterexample trace has a transition with syncs containing more than one letter of the alphabet:\n" + syncList)
          } else {
            // Ignore internal transition
          }
        case _ => ()
      })
      (edges,parents)
  }
  /** 
   *  Given the counterexample description output by TChecker, given as a list of lines,
   *  return the trace, that is, the sequence of events in the alphabet encoded by the said counterexample.
   */
  def getTraceFromCounterExampleOutput(cexDescription : List[String], events : Set[String]) : Trace = {
      val word = ListBuffer[String]()
      val (edges, parents) = getGraphFromCounterExampleOutput(cexDescription : List[String], events : Set[String])
      if edges.size > 0 then {
        val root =
            var node = parents.keys().nextElement()
            while ( parents.contains(node)) do {
              node = parents(node)
            }
            node
        var node = root
        while( edges.contains(node)) do {
          val (sigma, next) = edges(node)
          word.append(sigma)
          node = next
        }
      }
      word.toList
  }



  /** 
   *  Given the counterexample description output by TChecker, given as a list of lines,
   *  return the trace, that is, the sequence of events in the alphabet encoded by the said counterexample.
   */
  def getLassoFromCounterExampleOutput(cexDescription : List[String], events : Set[String]) : Lasso = {
    val prefix = ListBuffer[String]()
    val cycle = ListBuffer[String]()
    val (edges, parents) = getGraphFromCounterExampleOutput(cexDescription : List[String], events : Set[String])
    if edges.size > 0 then {
      // Find root
      val root =
          var node = parents.keys().nextElement()
          while ( parents.contains(node)) do {
            node = parents(node)
          }
          node
      // Find beginning of cycle
      val beginCycle = {
        var node = root
        val seen = mutable.Set[Int]()
        while ( seen.add(node) && edges.contains(node)) do {
          node = edges(node)._2
        }
        node
      }
      var node = root
      var atPrefix = true
      // Iterate forward from root, stop at beginCycle unless this is the first time we are seeing it (atPrefix)
      while( edges.contains(node) && (node != beginCycle || atPrefix)) do {
        if node == beginCycle then {
          atPrefix = false
        }
        val (sigma, next) = edges(node)
        if atPrefix then 
          prefix.append(sigma)
        else 
          cycle.append(sigma)
        node = next
      }
    }
    
    (prefix.toList, cycle.toList)
  }
}

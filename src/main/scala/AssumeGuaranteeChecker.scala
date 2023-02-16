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
import fr.irisa.circag.configuration
import fr.irisa.circag.statistics

case class BadTimedAutomaton(msg: String) extends Exception(msg)
case class FailedTAModelChecking(msg: String) extends Exception(msg)

class CounterExample(trace : List[String], alphabet : Set[String])

trait AssumeGuaranteeOracles[LTS, Property] {
  def checkInductivePremises(lts : LTS, assumptions : List[Property], guarantee : Property) : Option[CounterExample]
  def checkFinalPremise(lhs : List[Property], p : Property) : Option[CounterExample]
  def extendTrace(lts : LTS, word : List[String], extendedAlphabet : Set[String]) : Option[List[String]] 
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
  /** Given the counterexample description output by TChecker, given as a list of lines,
   *  return the trace, that is, the sequence of events in the alphabet encoded by the said counterexample.
   */
  def getTraceFromCexDescription(cexDescription : List[String]) : List[String] = {
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


// /**
//   * Parser for a single-process TChecker files
//   */
//  class SingleProcessTA
//     (
//     var systemName : String = "",
//     var events: Set[String] = Set(),
//     var core: String = "",
//     var eventsOfProcesses : HashMap[String, Set[String]] = HashMap[String, Set[String]](),
//     var syncs : List[List[(String, String)]] = List[List[(String, String)]](),
//     var processName : String = ""
//     )
//     extends TCheckerTA(systemName, events, core, eventsOfProcesses, syncs)

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
              case Some(l) => attributes.append(s"labels:${dlts.name + "_" + l}")
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
    if dlts.map(_.name).distinct.size < dlts.size || dlts.map(_.name).contains(ta.systemName) then {
      throw Exception("Synchronous product of automata of the same name")
    }
    val dltsTA = dlts.map({d => this.fromDLTS(d, acceptingLabelSuffix)})
    val jointAlphabet = ta.events | dlts.foldLeft(Set[String]())( (alph, d) => alph | d.alphabet.toSet)
    val sb = StringBuilder()
    val systemName = s"_premise_${ta.systemName}"
    // sb.append(s"${systemName}\n\n")
    // sb.append(jointAlphabet.map(e => s"event:${e}").mkString("\n"))
    // sb.append("\n")
    sb.append(ta.core)
    dltsTA.foreach({d => sb.append(d.core); sb.append("\n")})
    val eventsOfProcesses = HashMap[String,Set[String]]()
    dlts.foreach({d => eventsOfProcesses += (d.name -> d.alphabet.toSet)})
    eventsOfProcesses += (ta.systemName -> ta.events)
    // val sync_sb = StringBuilder()
    val allProcesses = eventsOfProcesses.keys.toList
    val syncs = jointAlphabet.map(
      sigma => 
        allProcesses.filter(eventsOfProcesses(_).contains(sigma))
        .map({process => (process,sigma)})
    ).toList.filter(_.size > 1)
    TA(systemName, jointAlphabet, sb.toString(), eventsOfProcesses, syncs)
  }
}

class TCheckerAssumeGuaranteeOracles(ltsFiles : Array[File], err : String) extends AssumeGuaranteeOracles[TA, DLTS]{
  val alphaP = Alphabets.fromList(List[String](err))
  val processes = ltsFiles.map(TA.fromFile(_))
  private val errDFA : DFA[?, String] = {
    AutomatonBuilders
      .newDFA(alphaP)
      .withInitial("q0")
      .from("q0")
      .on(err)
      .to("q1")
      .withAccepting("q0")
      .create();
  }
  
  /**
    * 
    *
    * @param lts
    * @param assumptions List of complete DFAs
    * @param guarantee
    * @pre guarantee.alphabet <= lts.alphabet
    * @return
    */
  def checkInductivePremises(ta : TA, assumptions : List[DLTS], guarantee : DLTS) : Option[CounterExample] =
    { 
      require(guarantee.alphabet.toSet.subsetOf(ta.alphabet().toSet))
      // Complement guarantee
      val compG = DLTS(s"_comp_${guarantee.name}", DFAs.complement(guarantee.dfa,guarantee.alphabet), guarantee.alphabet)
      // For each automaton A in assumptions:
      //   Extend alphabet, and remove all transitions from non-accepting states
      val liftedAssumptions = 
        assumptions.map({ass => DLTS.liftAndStripNonAccepting(ass, ta.alphabet(), Some(s"lifted_${ass.name}"))})
      val premiseProduct = TA.synchronousProduct(ta, compG::liftedAssumptions, Some("_accept_"))
      System.out.println(premiseProduct)
      checkReachability(premiseProduct, s"${compG.name}__accept_")
    }
  def checkFinalPremise(lhs : List[DLTS], p : DLTS) : Option[CounterExample] = {
    None
  }
  def extendTrace(lts : TA, word : List[String], extendedAlphabet : Set[String]) : Option[List[String]] ={
    None
  }

  def checkReachability(ta : TA, label : String) : Option[CounterExample] = {
    None
  }
}



class AssumeGuaranteeVerifier[LTS, Property](ltss : List[LTS], property : Property, agOracles : AssumeGuaranteeOracles[LTS, Property]) {
  var assumptionAlphabet : List[String] = List()
  var assumptions : Array[List[Int]] = Array()

  def simplifyAssumptions() : Unit = {
  }
  def refineAssumptionAlphabet(trace : List[String]) : Unit = {}
  def check() : Option[CounterExample] = {
    None
  }
}


/** Class providing functions to generate products of the given timed automaton `ta` with traces or DFAs
 *  on the common `alphabet`. The monitors are obtained by adding a monitor process in the given TA description,
 *  and adding synchronizations on all events in the alphabet.
 *  If acceptingLabel is None, then it is assumed that all locations of the TA are accepting. Otherwise, only those
 *  locations with the said label are accepting.
 */
class TCheckerMonitorMaker (
    ta: TA,
    alphabet: Alphabet[String],
    acceptingLabel : Option[String],
    monitorProcessName: String = "_crtmc_mon"
)  {
  val tmpDirPath = FileSystems.getDefault().getPath(configuration.get().tmpDirName);
  tmpDirPath.toFile().mkdirs()

  private val acceptingLocations = {
    val accLocs = ArrayBuffer[(String,String)]()
    val regLoc = "\\s*location:(.*):(.*)\\{(.*)\\}\\s*".r
    ta.core.split("\n").foreach( _ match {
      case regLoc(proc,loc,attr) =>
        acceptingLabel match {
          case None => accLocs.append((proc,loc))
          case Some(lab) => 
            if (attr.contains(s"labels:$lab")){
              accLocs.append((proc,loc))
            }
        }
      case _ => ()
    }
    )
    accLocs
  }

  /** Textual declaration of sync labels where the monitor process participates
    * in all synchronized edges with a label in alphabet + 
    * the monitor synchronizes on the letters of the alphabet with all processes
    * which use that action without declaring any sync.
    */
  val productTASyncs: String = {
    val strB = StringBuilder()
    val alphabetSet = alphabet.asScala.toSet
      // The monitor shall join all syncs on letters of the alphabet
    ta.syncs.foreach { syncLine =>
      val newSyncLine =
        syncLine.map(_._2).toSet.intersect(alphabetSet).toList match {
          case Nil          => syncLine
          case event :: Nil => (monitorProcessName, event) :: syncLine
          case _ =>
            throw BadTimedAutomaton(
              "Timed automaton must not have synchronized transitions on multiple external sync labels"
            )
        }
      strB.append("sync:")
      strB.append(newSyncLine.map(_ + "@" + _).mkString(":"))
      strB.append("\n")
    }
    // For each process, store the set of letters that appear in a sync instruction
    val syncEventsOfProcesses = HashMap[String, Set[String]]()
    ta.syncs.foreach { syncLine =>
      val newSyncLine =
        syncLine.filter(alphabetSet.contains(_)).foreach(
          (proc, event) => {
            val currentSet = syncEventsOfProcesses.getOrElse(proc,Set[String]())
            syncEventsOfProcesses += proc -> currentSet
          }
        )
    }
    strB.append("\n")
    // The monitor shall join all previously asynchronous transitions on the letters of the alphabet
    ta.eventsOfProcesses.foreach(
      (proc, syncEvents) => 
        syncEvents.intersect(alphabet.toSet).diff(syncEventsOfProcesses.getOrElse(proc, Set[String]())).foreach(
          e => strB.append("sync:%s@%s:%s@%s\n".format(monitorProcessName,e,proc,e))
        )
    )
    strB.result()
  }
  /** Accepting label for the monitor when all states of the TA are accepting (when acceptingLabel == None)*/
  def monitorAcceptLabel = "_crtmc_monitor_accept"

  /** Accepting label for the monitor when acceptingLabel != None. The monitor still contains locations
    labelled with monitorAcceptLabel, but the intersection is marked by productAcceptLabel. */
  def productAcceptLabel = "_crtmc_joint_accept"

  /** Returns textual description of a TA made of the product of the TA, and a
    * monitor that reads a given word. The monitorAcceptLabel is reachable iff the
    * intersection is non-empty.
    * 
    */
  def makeWordIntersecter(word: Buffer[String]): String = {
    // Build product automaton
    val strB = StringBuilder()
    strB.append(ta.core)
    strB.append("\nprocess:%s\n".format(monitorProcessName))
    for (i <- 0 to word.length) {
      strB.append("location:%s:q%d".format(monitorProcessName, i))
      val attributes = ArrayBuffer[String]()
      if (i == 0){
        attributes.append("initial:")
      }
      if (i == word.length){
        attributes.append("labels:%s".format(monitorAcceptLabel))
      }
      strB.append("{%s}\n".format(attributes.mkString(":")))
    }
    word.zipWithIndex.foreach { (label, i) =>
      strB.append(
        "edge:%s:q%d:q%d:%s\n".format(monitorProcessName, i, i + 1, label)
      )
    }
    strB.append("\n")
    strB.append(productTASyncs.mkString)

    acceptingLabel match {
      case None => 
        // All locations of the TA are accepting; so we will check for monitorAcceptLabel
        strB.toString
      case Some(errlabel) =>
        // TA has designated accepting locations, we will add a new accepting location labeled productAcceptLabel
        strB.append("\nevent:%s\n".format(productAcceptLabel))
        // For each process with an accepting location, add a new joint accepting state
        acceptingLocations.map(_._1).toSet.foreach{
          proc => strB.append("location:%s:%s{labels:%s}\n".format(proc, productAcceptLabel, productAcceptLabel))
          strB.append("sync:%s@%s:%s@%s\n".format(proc, productAcceptLabel, monitorProcessName, productAcceptLabel))
        }
        // Add edges from accepting locations to this new error states
        acceptingLocations.foreach{
          (proc,loc) =>
            strB.append("edge:%s:%s:%s:%s\n".format(proc,loc, productAcceptLabel, productAcceptLabel))
        }
        strB.append("edge:%s:q%s:q%s:%s\n".format(monitorProcessName, word.length, word.length, productAcceptLabel))
        strB.toString
    }
  }

  /** Returns textual description of TA made of the product of given TA, and the
    * the given DFA. The monitorAcceptLabel is reachable if the intersection is non-empty.
    * When complement is set to true, the returned automaton represents TA /\ comp(DFA), so the emptiness
    * of this intersection is equivalent to inclusion of TA in DFA.
    * 
    * The accepting label is to be checked is monitorAcceptLabel if all locations of the TA are accepting (acceptingLabel == None),
    * and productAcceptLabel otherwise. These cases are handled by the checkEmpty function.
    * FIXME there should be a unique accepting label in both cases.
    * 
    * @param complement whether given DFA should be complemented.
    */
  def makeDFAIntersecter(hypothesis: DFA[_, String], complement : Boolean = false): String = {
    val strStates = StringBuilder()
    val strTransitions = StringBuilder()
    // val alphabetSet = alphabet.asScala.toSet
    val initStates = hypothesis.getInitialStates().asScala
    strStates.append("process:" + monitorProcessName + "\n")
    // Add a dummy accepting node in case there is no accepting state at the end (this prevents tchecker from complaining)
    strStates.append("location:%s:dummy{labels:%s}\n".format(monitorProcessName,monitorAcceptLabel))
    hypothesis
      .getStates()
      .asScala
      .foreach(state =>
        {
          strStates
            .append("location:%s:q%s{".format(monitorProcessName, state.toString))
          val attributes = ArrayBuffer[String]()
          if (initStates.contains(state)) then {
            attributes.append("initial:")
          }
          // revert accepting and non-accepting states
          if (!complement && hypothesis.isAccepting(state) || complement && !hypothesis.isAccepting(state)) {
            attributes.append("labels:%s".format(monitorAcceptLabel))
          }
          strStates.append(attributes.mkString(":"))
          strStates.append("}\n")
          for (sigma <- alphabet.toList) {
            val succs = hypothesis.getSuccessors(state, sigma);
            if (!succs.isEmpty()) then {
              for (succ <- succs) {
                strTransitions.append(
                  "edge:%s:q%s:q%s:%s\n".format(
                    monitorProcessName,
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
      taB.append("\n")
      taB.append(productTASyncs)
      taB.append("\n")
      acceptingLabel match {
        case None => 
          // All locations of the TA are accepting; so we will check for monitorAcceptLabel
          taB.toString
        case Some(errlabel) =>
          // TA has designated accepting locations, we will add a new accepting location labeled productAcceptLabel
          taB.append("\nevent:%s\n".format(productAcceptLabel))
          // For each process with an accepting location, add a new joint accepting state
          acceptingLocations.map(_._1).toSet.foreach{
            proc => taB.append("location:%s:%s{labels:%s}\n".format(proc, productAcceptLabel, productAcceptLabel))
            taB.append("sync:%s@%s:%s@%s\n".format(proc, productAcceptLabel, monitorProcessName, productAcceptLabel))
          }
          // Add edges from accepting locations to this new error states
          acceptingLocations.foreach{
            (proc,loc) =>
              taB.append("edge:%s:%s:%s:%s\n".format(proc,loc, productAcceptLabel, productAcceptLabel))
          }
          hypothesis.getStates().asScala.foreach(state =>
            if (!complement && hypothesis.isAccepting(state) || complement && !hypothesis.isAccepting(state)) {
              taB.append("edge:%s:q%s:q%s:%s\n".format(monitorProcessName, state.toString, state.toString, productAcceptLabel))
            }
          )
          taB.toString
      }
    }
  }
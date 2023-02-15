

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
import net.automatalib.automata.fsa.NFA
import net.automatalib.util.automata.fsa.DFAs
import net.automatalib.words.impl.Alphabets;
import net.automatalib.words._
import net.automatalib.util.automata.builders.AutomatonBuilders;
import net.automatalib.visualization.Visualization;
import net.automatalib.automata.fsa.impl.compact.CompactNFA;
import net.automatalib.serialization.aut.AUTSerializationProvider 
import net.automatalib.automata.fsa.NFA

import fr.irisa.circag.configuration
import fr.irisa.circag.statistics

case class BadTimedAutomaton(msg: String) extends Exception(msg)
case class FailedTAModelChecking(msg: String) extends Exception(msg)

class CounterExample(trace : List[String], alphabet : Set[String])

trait AGOracles[LTS, Property] {
  def checkInductivePremises(lts : LTS, assumptions : List[Property], guarantee : Property) : Option[CounterExample]
  def checkFinalPremise(lhs : List[Property], p : Property) : Option[CounterExample]
  def extendTrace(lts : LTS, word : List[String], extendedAlphabet : Set[String]) : Option[List[String]] 
}

/** A light parser that reads TChecker TA from given file, and stores the tuple (events,
  * eventsOfProcesses, core, syncs) where 
  * - events is the list of all events,
  * - eventsOfProcesses maps process names to events that they include, 
  * - core is the list of lines of the input file except for the sync instructions,
  * - syncs contains lists of tuples encoding the syncs
  * - externEvents is a subset of events and is the set of events tagged _extern_
  */
class TCheckerTA(inputFile: java.io.File) {
  var events: Set[String] = Set()
  var externEvents : List[String] = List()
  var eventsOfProcesses = HashMap[String, Set[String]]()
  var syncs = List[List[(String, String)]]()
  var core: String = ""
  private val logger = LoggerFactory.getLogger(classOf[TCheckerTA])

  {
    val lines = Source.fromFile(inputFile).getLines().toList
    val regEvent = "\\s*event:([^ ]*).*".r
    val regExternEvent = "\\s*event:([^ ]*).*_extern_.*".r
    val regSync = "\\s*sync:(.*)\\s*".r
    val regProcess = "\\s*process:(.*)\\s*".r
    val regEdge = "\\s*edge:[^:]*:[^:]*:[^:]*:([^{]*).*".r
    // System.out.println("File: " + inputFile.toString)
    this.events = lines.flatMap({
      case regEvent(event) => Some(event.strip())
      case _               => None
    }).toSet
    externEvents = lines.flatMap({
      case regExternEvent(event) => Some(event.strip())
      case _               => None
    })
    syncs = lines.flatMap({
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

    eventsOfProcesses = HashMap[String, Set[String]]()
    var currentProcess = ""
    lines.foreach {
      case regProcess(monitorProcessName) =>
        currentProcess = monitorProcessName
        eventsOfProcesses += (monitorProcessName -> Set[String]())
      // System.out.println("Now reading process: " + monitorProcessName)
      case regEdge(sync) =>
        eventsOfProcesses += (currentProcess -> (eventsOfProcesses(
          currentProcess
        ) + sync))
      // System.out.println("Adding sync: " + sync)
      case _ => ()
    }
    core = lines.filter(line => !line.startsWith("sync:")).mkString("\n")
  }

  /** Given the counterexample description output by TChecker, given as a list of lines,
   *  return the trace, that is, the sequence of events in the alphabet encoded by the said counterexample.
   */
  def getTraceFromCexDescription(cexDescription : List[String]) : List[String] = {
      val alphabetSet = events.toSet
      val word = ListBuffer[String]()
      val regEdge = ".*->.*vedge=\"<(.*)>\".*".r
      cexDescription.foreach({
        case regEdge(syncList) => 
          val singleSync = syncList.split(",").map(_.split("@")(1)).toSet.intersect(alphabetSet)
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

  /** Decompose given TChecker model into several components
   */
  def decompose() : List[TCheckerTA] = {
    throw Exception("Not yet implemented")
  }

}


class TCheckerDFAOracles extends AGOracles[TCheckerTA, TCheckerTA]{
  def checkInductivePremises(lts : TCheckerTA, assumptions : List[TCheckerTA], guarantee : TCheckerTA) : Option[CounterExample] =
    {
      None
    }
  def checkFinalPremise(lhs : List[TCheckerTA], p : TCheckerTA) : Option[CounterExample] = {
    None
  }
  def extendTrace(lts : TCheckerTA, word : List[String], extendedAlphabet : Set[String]) : Option[List[String]] ={
    None
  }

}



class AGVerifier[LTS, Property](ltss : List[LTS], property : Property, agOracles : AGOracles[LTS, Property]) {
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
    ta: TCheckerTA,
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


  abstract class Answer
  case object Empty extends Answer
  case class NonEmpty(cexDescription : String) extends Answer

  /** Given a string description of a product automaton, check emptiness.
   * @param generateWitness returns the actual counterexample if set to true, and an empty string otherwise.
   * @return Empty if the given automaton is empty, and NonEmpty with a trace otherwise.
   */
  def checkEmpty(monitorDescription : String, generateWitness : Boolean) : Answer = {
    val label = if acceptingLabel == None then monitorAcceptLabel else productAcceptLabel
    val productFile =
      Files.createTempFile(tmpDirPath, "product", ".ta").toFile()
    val pw = PrintWriter(productFile)
    pw.write(monitorDescription)
    pw.close()

    // Model check product automaton
    var certFile : java.io.File = null
    
    val cmd = 
        if (generateWitness){
          certFile = Files.createTempFile(tmpDirPath, "cert", ".ta").toFile()
          "tck-reach -a reach %s -l %s -C %s"
            .format(productFile.toString, label,certFile.toString)
        } else {
          "tck-reach -a covreach %s -l %s"
            .format(productFile.toString, label)
        }
    if configuration.get().verbose_MembershipQueries then
      System.out.println(cmd)
    // var beginTime = System.nanoTime()
    val output = cmd.!!
    // this._elapsed = this._elapsed + (System.nanoTime() - beginTime)
    // System.out.println(output)

    if (!configuration.get().keepTmpFiles){
      productFile.delete()
    }    
    if (output.contains("REACHABLE false")) then {
      if (generateWitness && !configuration.get().keepTmpFiles){
        certFile.delete()
      }
      Empty
    } else if (output.contains("REACHABLE true")) then {
      if (generateWitness){
        // val parts = output.split("Counterexample trace:").map(_.strip()).filter(_.length>0)      
        // val timedCex = parts(1)
        val timedCex = Source.fromFile(certFile).getLines.mkString("\n")
        if (!configuration.get().keepTmpFiles){
          certFile.delete()
        }
        // System.out.println(timedCex)
        NonEmpty(timedCex)
      } else {
        NonEmpty("")
      }
    } else {
      if (generateWitness && !configuration.get().keepTmpFiles){
        certFile.delete()
      }      
      throw FailedTAModelChecking(output)
    }
  }

}
abstract class TAMembershipOracle extends DFAMembershipOracle[String]{
  /**
   * Query TChecker whether the given untimed word prefix.suffix is accepted by the timed automaton.
   * @return Returns witness timed trace if the given word is in the untimed language; None otherwise.
   */
  def answerQuery(
      prefix: Word[String],
      suffix: Word[String],
      generateWitness : Boolean
  ): Option[String]

  def systemElapsedTime : Long
  def nbQueries : Long
}

class TCheckerMembershipOracle(
    ta : TCheckerTA,
    alphabet: Alphabet[String],
    acceptingLabel : Option[String] = None
) extends TAMembershipOracle {
  private val logger = LoggerFactory.getLogger(classOf[TCheckerTA])
  private val taMonitorMaker = TCheckerMonitorMaker(ta, alphabet, acceptingLabel)

  private var _elapsed : Long = 0
  private var _nbQueries : Long = 0
  override def systemElapsedTime : Long ={
    _elapsed
  }
  override def nbQueries : Long ={
    _nbQueries
  }

  override def processQueries(
      queries: java.util.Collection[
        ? <: de.learnlib.api.query.Query[String, java.lang.Boolean]
      ]
  ): Unit = {
    MQUtil.answerQueries(this, queries);
  }

  override def answerQuery(
      prefix: Word[String],
      suffix: Word[String]
  ): java.lang.Boolean = {
    val pr = prefix.asList.asScala
    val su = suffix.asList.asScala
    // System.out.println(pr.toList.mkString(" ") + " ||| " + su.mkString(" "))
    answerQuery(prefix,suffix, false) match {
      case None => false
      case _ => true
    }
  }

  /**
   * Returns witness timed trace if the given word is in the untimed language
   */
  override def answerQuery(
      prefix: Word[String],
      suffix: Word[String],
      generateWitness : Boolean
  ): Option[String] = {
    statistics.Counters.incrementCounter("taMembershipOracle")

    val trace = prefix.asList().asScala ++ suffix.asList().asScala
    this._nbQueries += 1
    val monitorDescription = taMonitorMaker.makeWordIntersecter(trace)
    val verdict = taMonitorMaker.checkEmpty(monitorDescription, generateWitness)
    if configuration.get().verbose_MembershipQueries then
      System.out.print(BLUE + "Membership query: " + trace + RESET)
    verdict match {
      case taMonitorMaker.Empty =>
        if configuration.get().verbose_MembershipQueries then
          System.out.println(RED + " (false)" + RESET)
        statistics.negQueries = statistics.negQueries + trace.mkString(" ")
        None
      case taMonitorMaker.NonEmpty(cex) =>
        statistics.posQueries = statistics.posQueries + trace.mkString(" ")
        if configuration.get().verbose_MembershipQueries then
          System.out.println(GREEN + " (true)" + RESET)
        Some(cex)
    }
  }
}

/** Oracle to check whether the language of the TA is included in that of the hypothesis H, i.e.
 *                              T <= H ? 
 *  assuming that all locations of the TA are accepting.
 */
class TCheckerInclusionOracle(
    ta: TCheckerTA,
    alphabet: Alphabet[String]
) extends EquivalenceOracle.DFAEquivalenceOracle[String] {
  private val logger = LoggerFactory.getLogger(classOf[TCheckerInclusionOracle])
  private val taMonitorMaker = TCheckerMonitorMaker(ta, alphabet, None)
  private val alphabetSet = alphabet.asScala.toSet

  val tmpDirPath = FileSystems.getDefault().getPath(configuration.get().tmpDirName);
  tmpDirPath.toFile().mkdirs()

  override def findCounterExample(
      hypothesis: DFA[_, String],
      inputs: java.util.Collection[? <: String]
  ): DefaultQuery[String, java.lang.Boolean] = {
    statistics.Counters.incrementCounter("taInclusionOracle")
    
    val productFile =
      Files.createTempFile(tmpDirPath, "productEq", ".ta").toFile()
    val pw = PrintWriter(productFile)
    pw.write(taMonitorMaker.makeDFAIntersecter(hypothesis, true))
    pw.close()

    var certFile = Files.createTempFile(tmpDirPath, "cert", ".ta").toFile()

    // Model check product automaton
    if (configuration.get().verbose)
      System.out.println(YELLOW + "Inclusion query (|DFA| = " + hypothesis.size + ")" + RESET)
    val cmd = "tck-reach -a reach %s -l %s -C %s" 
      .format(productFile.toString, taMonitorMaker.monitorAcceptLabel, certFile)
    if (configuration.get().verbose)
      System.out.println(cmd)
    val output = cmd.!!
    // System.out.println(output)
    if (!configuration.get().keepTmpFiles){
      productFile.delete()
    }    
    if (output.contains("REACHABLE false")) then {
      System.out.println(GREEN + "TA Inclusion holds: hypothesis with " + hypothesis.size + " states found" + RESET)
      null
    } else if (output.contains("REACHABLE true")) then {
      // val parts = output.split("Counterexample trace:").map(_.strip()).filter(_.length>0)
      // val cexLines = parts(1).split("\n").toList
      val cexLines = Source.fromFile(certFile).getLines.toList
      if (!configuration.get().keepTmpFiles){
        certFile.delete()
      }
      val word = ta.getTraceFromCexDescription(cexLines).filter(alphabet.contains(_))
      val query =  DefaultQuery[String, java.lang.Boolean](Word.fromArray[String](word.toArray,0,word.length), java.lang.Boolean.TRUE)
      if (configuration.get().verbose){
        System.out.println(ta.getTraceFromCexDescription(cexLines))
        System.out.println(MAGENTA + "CEX requested alphabet: " + inputs + RESET)
        System.out.println(RED + "Counterexample to inclusion (accepted by TA but not by hypothesis): " + query + RESET)
      }
      statistics.posQueries = statistics.posQueries + word.mkString(" ")

      // Visualization.visualize(hypothesis, alphabet);
      return query
    } else {
      throw FailedTAModelChecking(output)
    }
  }

}

/*
 * Oracle to compute interpolant automata from a given word that is not in the language.
 */
class TCheckerInterpolationOracle(
    ta: File,
    alphabet: List[String]
) {

  abstract class Answer
  case class Empty(nfa : CompactNFA[String]) extends Answer
  case class NonEmpty(cexDescription : String) extends Answer

  /**
   * Use TChecker to check whether word is in the untimed language of the given ta.
   * @return NonEmpty if the word is accepted (and a witness execution a string);
   *   Empty(nfa) where nfa is an interpolant automaton otherwise.
   */
  def checkWord(word : List[String]) : Answer = {
    val wordArg = "\"%s\"".format(word.mkString(" "))
    val alphabetArg = "\"%s\"".format(alphabet.mkString(" "))

    val cmd = "tck-tar %s -t %s -a %s".format(ta.toString, wordArg, alphabetArg)
    val output = cmd.!!
    System.out.println(cmd)
    System.out.println(output)
    if (output.contains("REACHABLE true")){
      NonEmpty(output)
    } else {
      val parts = output.split("Interpolant Automaton:")
      if (parts.length != 2){
        throw Exception("Unexpected output from tck-tar:\n" + output)
      }
      val regNbStates = "nb_states:\\s*([0-9]*)\\s*".r
      var nbStates = 0
      parts(1).split("\n").foreach{
        case regNbStates(n) => nbStates = Integer.parseInt(n)
        case _ => ()
      }
      if (nbStates == 0){
        throw Exception("Could not parse number of states in interpolant automaton:\n" + parts(1))
      }
      val nfa = AutomatonBuilders.newNFA(Alphabets.fromList(alphabet)).create()
      for (i <- 1 to nbStates){
        nfa.addState()
      }
      val regTrans = "\\(([0-9]*),(.*),([0-9]*)\\)".r
      val regInit = "init:\\s*(.*)".r
      val regAccept = "accepting: (.*)".r
      parts(1).split("\n").foreach{
          case regTrans(p, sigma, q) =>
            nfa.addTransition(Integer.parseInt(p.strip()), sigma.strip(), Integer.parseInt(q.strip()))
          case regInit(p) =>
            nfa.setInitial(Integer.parseInt(p), true)
          case regAccept(p) =>
            nfa.setAccepting(Integer.parseInt(p), true)
          case _ => ()
      }
      Empty(nfa)
    }
  }
}


/** Oracle to check whether the language of the hypothesis H is included in that of the TA:
 *                              H <= T ? 
 *  Here, all locations of the TA is assumed to be accepting.
 * 
 *  FIXME Checking the emptiness of H /\ complement(T)  does not imply the above inclusiom on untimed traces!
 */
class TCheckerContainmentOracle(
    taFile: File,
    alphabet: Alphabet[String]
) extends EquivalenceOracle.DFAEquivalenceOracle[String] {

  private val logger = LoggerFactory.getLogger(classOf[TCheckerContainmentOracle])

  private val tmpDirPath = FileSystems.getDefault().getPath(configuration.get().tmpDirName);
  tmpDirPath.toFile().mkdirs()

  /** TCheckerTA which represents the complement of the given TA,
   *  with accepting label _complement_accept. */
  
  private val complementTA = {
    val f = Files.createTempFile(tmpDirPath, "complement", ".ta").toFile()
    val cmd = s"tck-convert -c ${taFile.toString} -o ${f.toString}"
    System.out.println(cmd)
    if (cmd.! != 0) then{
      logger.error("tck-convert returned an error")
      throw FailedTAModelChecking("Could not compute complement")
    }
    TCheckerTA(f)
  }
  val taMonitorMaker = TCheckerMonitorMaker(complementTA, alphabet, Some("_complement_accept"))
  
  override def findCounterExample(
      hypothesis: DFA[_, String],
      inputs: java.util.Collection[? <: String]
    ): DefaultQuery[String, java.lang.Boolean] = {
    statistics.Counters.incrementCounter("taContainmentOracle")

    val productTA = taMonitorMaker.makeDFAIntersecter(hypothesis, false)
    taMonitorMaker.checkEmpty(productTA, generateWitness=true) match {
      case taMonitorMaker.Empty => null // Containment holds
      case taMonitorMaker.NonEmpty(cexDescription) => // Containment fails
      val word = complementTA.getTraceFromCexDescription(cexDescription.split("\n").toList).filter(alphabet.contains(_))
      val query =  DefaultQuery[String, java.lang.Boolean](Word.fromArray[String](word.toArray,0,word.length), java.lang.Boolean.FALSE)
      System.out.println(RED + "Counterexample to containment (accepted by hypothesis but not by timed automaton): " + query + RESET)
      statistics.negQueries = statistics.negQueries + word.mkString(" ")
      query
    }      
  }
}


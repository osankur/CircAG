package fr.irisa.circag.tchecker

import io.AnsiColor._

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

import de.learnlib.util.MQUtil;
import de.learnlib.api.oracle.EquivalenceOracle
import de.learnlib.api.query.DefaultQuery;
import de.learnlib.api.oracle._
import de.learnlib.api.oracle.MembershipOracle
import de.learnlib.api.oracle.MembershipOracle.DFAMembershipOracle
import net.automatalib.automata.fsa.impl.compact.CompactDFA;
import net.automatalib.util.automata.builders.AutomatonBuilders;
import net.automatalib.automata.fsa.DFA
import net.automatalib.automata.fsa.impl.FastDFA
import net.automatalib.automata.fsa.impl.FastDFAState
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
import fr.irisa.circag.ConstraintManager
import com.microsoft.z3

case class BadTimedAutomaton(msg: String) extends Exception(msg)
case class FailedTAModelChecking(msg: String) extends Exception(msg)

trait AssumeGuaranteeOracles[LTS, Property] {
  def checkInductivePremise(lts : LTS, assumptions : List[Property], guarantee : Property) : Option[Trace]
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

  def fromDLTS(dlts : DLTS, acceptingLabelSuffix : Option[String] = None) : TA = {
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

object TCheckerAssumeGuaranteeOracles {
  
  /**
    * ta |= lhs |> guarantee
    *
    * @param lts
    * @param assumptions List of complete DFAs
    * @param guarantee
    * @pre guarantee.alphabet <= lts.alphabet (checked by assertion)
    * @pre All reachable states of the assumptions and ta are accepting (not checked by assertion)
    * @return None if the premise holds; and Some(cexTrace) otherwise
    */
  def checkInductivePremise(ta : TA, assumptions : List[DLTS], guarantee : DLTS) : Option[Trace] =
    { 
      statistics.Counters.incrementCounter("inductive-premise")
      var beginTime = System.nanoTime()
      require(guarantee.alphabet.toSet.subsetOf(ta.alphabet))
      // require(assumptions.forall({dlts => !dlts.dfa.getStates().forall(_.isAccepting())}))
      if configuration.get().verbose then {
        System.out.println(s"Checking inductive premise for ${ta.systemName}")
      }
      val guaranteeAlphabet = Alphabets.fromList(guarantee.alphabet.toList)
      val compG = DLTS(
        s"_comp_${guarantee.name}", 
        DFAs.complement(guarantee.dfa, guaranteeAlphabet, FastDFA(guaranteeAlphabet)),
        guarantee.alphabet)
      // Visualization.visualize(compG.dfa, Alphabets.fromList(guarantee.alphabet.toList))
      val liftedAssumptions = 
        assumptions.map({ass => DLTS.liftAndStripNonAccepting(ass, ta.alphabet, Some(s"lifted_${ass.name}"))})
      val premiseProduct = TA.synchronousProduct(ta, compG::liftedAssumptions, Some("_accept_"))
      statistics.Timers.incrementTimer("inductive-premise", System.nanoTime() - beginTime)
      checkReachability(premiseProduct, s"${compG.name}_accept_")
    }

  /**
    * Check the final premise, that is, whether /\_{dtls in lhs} dtls implies property.
    *
    * @param lhs
    * @param property
    * @pre All states of the automata in lhs are accepting
    * @return None if the premise holds; and Some(cexTrace) otherwise
    */
  def checkFinalPremise(lhs : List[DLTS], property : DLTS) : Option[Trace] = {
      statistics.Counters.incrementCounter("final-premise")

      // Check precondition
      for dlts <- lhs do {
        val dfa = dlts.dfa
        dfa.getStates().foreach({s =>
          for a <- dlts.alphabet do {
            dfa.getSuccessors(s,a).foreach({
              sn =>
                assert(dfa.isAccepting(sn))
              })
          }
        })
      }
      val alph = Alphabets.fromList(property.alphabet.toList)
      val compG = DLTS(s"_comp_${property.name}", DFAs.complement(property.dfa, alph, FastDFA(alph)), property.alphabet)
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
  }

  /**
    * 
    * @param ta
    * @param word
    * @param projectionAlphabet
    * @return
    */
  def attemptToExtendTraceToAllProcesses(tas : Array[TA], word : Trace, projectionAlphabet : Option[Set[String]]) : Trace = {
    var currentTrace = word
    for ta <- tas do {
      val wordDLTS = DLTS.fromTrace(currentTrace,None)
      val productTA = TA.synchronousProduct(ta, List(wordDLTS), acceptingLabelSuffix = Some("_accept_"))
      checkReachability(productTA, s"${wordDLTS.name}_accept_") match {
        case None => ()
        case Some(newTrace) => currentTrace = newTrace
      }
    }
    currentTrace
  }

  /**
    * Check whether ta contains an exec whose trace, projected to projectionAlphabet is word.
    *
    * @param ta
    * @param word
    * @param projectionAlphabet
    * @return None if no such execution exists, and Some(execution) otherwise.
    */
  def checkTraceMembership(ta : TA, word : Trace, projectionAlphabet : Option[Set[String]] = None) : Option[Trace] = {  
    statistics.Counters.incrementCounter("trace-membership")

    val traceProcess = DLTS.fromTrace(word, projectionAlphabet)
    val productTA = TA.synchronousProduct(ta, List(traceProcess), Some("_accept_"))
    val label = s"${traceProcess.name}_accept_"
    this.checkReachability(productTA, label)
  }

  /**
   * Check the reachability of a state labeled by label. Return such a trace if any.
   * 
   * @param ta
   * @param label
   */
  def checkReachability(ta : TA, label : String) : Option[Trace] = {
    val beginTime = System.nanoTime()    
    statistics.Counters.incrementCounter("model-checking")
    val modelFile =
      Files.createTempFile(configuration.get().getTmpDirPath(), "circag-query", ".ta").toFile()
    val pw = PrintWriter(modelFile)
    pw.write(ta.toString())
    pw.close()

    val certFile =
      Files.createTempFile(configuration.get().getTmpDirPath(), "circag-cert", ".cert").toFile()
    val cmd = "tck-reach -a reach %s -l %s -c %s"
            .format(modelFile.toString, label, certFile.toString)

    if configuration.get().verbose then
      System.out.println(cmd)

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
      Some(TA.getTraceFromCounterExampleOutput(cex, ta.alphabet))
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



abstract class AGIntermediateResult extends Exception
class AGSuccess extends AGIntermediateResult
class AGContinue extends AGIntermediateResult
case class AGFalse(cex : Trace) extends AGIntermediateResult

/**
  * AG Proof skeleton that specifies which the dependencies for each premise of the N-way AG rule,
  * and the alphabets to be used for the assumption DFA of each TA.
  * 
  * @param processDependencies the set of process indices on which the proof of process(i) must depend.
  * @param propertyDependencies
  * @param assumptionAlphabets
  */
class AGProofSkeleton(var processDependencies : Buffer[Set[Int]],
                      var propertyDependencies : Set[Int],
                      var assumptionAlphabets : Buffer[Set[String]]) {
  require(processDependencies.size > 0)
  require(processDependencies.size == assumptionAlphabets.size)
  def update(processAlphabets : Buffer[Set[String]], propertyAlphabet : Set[String], newAssumptionAlphabet : Set[String]) : Unit = {
    require(processDependencies.size == processAlphabets.size)
    val nbProcesses = processDependencies.size
    // Compute simplified sets of assumptions for the new alphabet
    // adj(i)(j) iff (i = j) or (i and j have a common symbol) or (i has a common symbol with k such that adj(k)(j))
    // Index nbProcesses represents the property.
    var adj = Buffer.tabulate(nbProcesses+1)({_ => Buffer.fill(nbProcesses+1)(false)})
    for i <- 0 until nbProcesses do {
      adj(i)(i) = true
      for j <- 0 until i do {
        adj(i)(j) = !processAlphabets(i).intersect(processAlphabets(j)).isEmpty
        adj(j)(i) = adj(i)(j)
      }
    }
    adj(nbProcesses)(nbProcesses) = true
    for j <- 0 until nbProcesses do {
        adj(nbProcesses)(j) = !propertyAlphabet.intersect(processAlphabets(j)).isEmpty
        adj(j)(nbProcesses) = adj(nbProcesses)(j)
    }
    for k <- 0 until nbProcesses+1 do {
      for i <- 0 until nbProcesses+1 do {
        for j <- 0 until nbProcesses+1 do {
          if(adj(i)(k) && adj(k)(j)) then {
            adj(i)(j) = true
          }
        }
      }
    }
    for i <- 0 until nbProcesses do {
      processDependencies(i) = adj(i).zipWithIndex.filter({(b,i) => b}).map(_._2).toSet
    }
    propertyDependencies = adj(nbProcesses).zipWithIndex.filter({(b,i) => b}).map(_._2).toSet
  }
}

class TCheckerAssumeGuaranteeVerifier(ltsFiles : Array[File], err : String, useAlphabetRefinement : Boolean = false) {
  val nbProcesses = ltsFiles.size
  val propertyAlphabet = Set[String](err)
  val processes = ltsFiles.map(TA.fromFile(_)).toBuffer

  val wholeAlphabet = processes.foldLeft(propertyAlphabet)({(alph, pr) => alph | pr.alphabet})
  val propertyDLTS = {
    val errDFA = {
      val alph= Alphabets.fromList(propertyAlphabet.toList)
      AutomatonBuilders
        .forDFA(FastDFA(alph))
        .withInitial("q0")
        .from("q0")
        .on(err)
        .to("q1")
        .withAccepting("q0")
        .create();
    }
    DLTS("property", errDFA, propertyAlphabet)
  }

  // Set of symbols that appear in the property alphabet, or in at least two processes
  val interfaceAlphabet =
    // Consider only symbols that appear at least in two processes (union of J_i's in CAV16)
    val symbolCount = HashMap[String, Int]()
    processes.foreach{p => p.alphabet.foreach{
      sigma => symbolCount.put(sigma,symbolCount.getOrElse(sigma,0)+1)
    }}
    symbolCount.filterInPlace((sigma,count) => count >= 2)
    propertyAlphabet | symbolCount.map({(sigma,_) => sigma}).toSet

  // Intersection of local alphabets with the interface alphabet: when all 
  // assumptions use these alphabets, the AG procedure is complete.
  // i.e. alpha_F = alphaM_i /\ alphaP cup J_i
  val completeAlphabets = processes.map({ 
    pr => interfaceAlphabet.intersect(pr.alphabet)
  }).toBuffer

  /**
    * Current alphabet for assumptions: the alphabet of each assumption for ta is ta.alphabet & assumptionAlphabet.
    */
  private var assumptionAlphabet = 
    if useAlphabetRefinement then {
      propertyAlphabet
    } else {
      interfaceAlphabet
    }

  /**
    * The assumption DLTS g_i for each process i.
    */
  var assumptions : Buffer[DLTS] = {
    (0 until ltsFiles.size)
    .map(
      { i =>
        val alph = assumptionAlphabet.intersect(processes(i).alphabet)
        val dfa = FastDFA(Alphabets.fromList(alph.toList))
        val state = dfa.addState(true)
        for sigma <- alph do {
          dfa.addTransition(state, sigma, state)
        }
        // Visualization.visualize(dfa, Alphabets.fromList(processes(i).alphabet.toList))

        DLTS(s"g_${i}", dfa, alph)
      }).toBuffer
  }


  val proofSkeleton = 
    val processDependencies : Buffer[Set[Int]] = 
      (0 until ltsFiles.size)
      .map({i =>(0 until ltsFiles.size).toSet - i})
      .toBuffer
    val propertyDependencies : Set[Int] = 
      (0 until ltsFiles.size)
      .toSet
    AGProofSkeleton(processDependencies, propertyDependencies, assumptions.map(_.alphabet))
  val constraintManager = ConstraintManager(proofSkeleton)

  /**
    * Updates assumptionAlphabet, and consequently processDependencies, propertyDependencies, and resets constraint manager.
    *
    * @param newAlphabet
    */
  private def updateAssumptionAlphabet(newAssumptionAlphabet : Set[String]) : Unit = {
    require(assumptionAlphabet.subsetOf(newAssumptionAlphabet))
    proofSkeleton.update(processes.map(_.alphabet), propertyAlphabet, newAssumptionAlphabet)
    constraintManager.reset()
  }

  def generateAssumptions() : Unit = {
  }

  def updateConstraints(process : Int, cexTrace : Trace) : Unit = {
    constraintManager.addConstraint(process, cexTrace, 34)
  }

  def applyAG() : AGIntermediateResult = {
    try{
      for (ta,i) <- processes.zipWithIndex do {
        TCheckerAssumeGuaranteeOracles.checkInductivePremise(ta, proofSkeleton.processDependencies(i).map(assumptions(_)).toList, assumptions(i))
        match {
          case None =>
            System.out.println(s"${GREEN}Premise ${i} passed${RESET}")
          case Some(cexTrace) => 
            System.out.println(s"${RED}Premise ${i} failed with cex: ${cexTrace}${RESET}")
            if (configuration.cex(i).contains(cexTrace)) then {
              for j <- proofSkeleton.processDependencies(i) do {
                System.out.println(s"Dependency ${assumptions(j).name}")
                Visualization.visualize(assumptions(j).dfa, Alphabets.fromList(assumptions(j).alphabet.toList))
              }
              throw Exception("Repeated CEX")
            } else {
              configuration.cex(i) = configuration.cex(i) + cexTrace
            }
            updateConstraints(i, cexTrace)
            throw AGContinue()
        }
      }
      TCheckerAssumeGuaranteeOracles.checkFinalPremise(proofSkeleton.propertyDependencies.map(assumptions(_)).toList, propertyDLTS)
      match {
        case None => 
          System.out.println(s"${GREEN}Final premise succeeded${RESET}")
          AGSuccess()
        case Some(cexTrace) =>
          System.out.println(s"${RED}Final premise failed with cex: ${cexTrace}${RESET}")
          // If all processes contain proj(cexTrace), then return false, otherwise continue
          for (ta,i) <- processes.zipWithIndex do {
            TCheckerAssumeGuaranteeOracles.checkTraceMembership(ta, cexTrace, Some(assumptions(i).alphabet))
            match {
              case None => 
                System.out.println(s"\tCex does not apply to process ${i}. Continuing...")
                // for ass <- assumptions do {
                //   System.out.println(ass.name)
                //   Visualization.visualize(ass.dfa, Alphabets.fromList(ass.alphabet.toList))
                // }
                constraintManager.addFinalPremiseConstraint(cexTrace)
                throw AGContinue()
              case _ => ()
            }
          }
          System.out.println(s"\tConfirming cex: ${cexTrace}")
          throw AGFalse(cexTrace)
      }
    } catch {
      case ex : AGContinue => ex
      case ex : AGFalse => ex
    }
  }
  def alphabetRefine(cexTrace : Trace) : AGIntermediateResult = {
    val currentAlphabets = assumptions.map(_.alphabet)
    if ( this.completeAlphabets == currentAlphabets ) then {
      // All alphabets are complete; we can conclude
      AGFalse(cexTrace)
    } else {
      // Extend the trace to the alphabet of each TA separately (projected to the TA's external alphabet)
      val processTraces = processes.map{
        p => TCheckerAssumeGuaranteeOracles.checkTraceMembership(p, cexTrace) match {
          case Some(processTrace) => processTrace.filter(p.alphabet)
          case None => throw Exception(s"Trace $cexTrace fails the final premise but cannot be reproduced here")
        }
      }
      System.out.println(processTraces)
      // MATCH: Check if each pair of traces match when projected to common alphabet
      var tracesMatch = true
      for i <- 0 until this.processes.size do {
        for j <- 0 until i do {
          val commonAlphabet = processes(i).alphabet.intersect(processes(j).alphabet)
          if (processTraces(i).filter(commonAlphabet) != processTraces(j).filter(commonAlphabet)) then {
            tracesMatch = false
          }
        }
      }
      if (tracesMatch) then{
        AGFalse(cexTrace)
      } else {
        // Choose a symbol that appears in a process trace but not in the current alphabet
        val traceSymbols = processTraces.map(_.toSet).fold(Set[String]())({(a,b) => a | b})
        val newSymbols = traceSymbols.diff(this.assumptionAlphabet)
        assert(!newSymbols.isEmpty)
        throw Exception("inconc")
        AGContinue()
      }
    }
  }

  /**
    * Simplify propertyDependencies and processDependencies 
    */
  def simplifyDependencies() : Unit = {}
  def check() : Option[Trace] = {
    try{
      while(true) {
        this.assumptions = constraintManager.generateAssumptions(this.assumptions)

        this.applyAG() match {
          case AGFalse(cex) =>
            alphabetRefine(cex) match {
              case AGFalse(cex) => throw AGFalse(cex)
              case _ => ()
            }
          case e : AGSuccess =>
            // We are done here
            throw e
          case e : AGContinue => 
            ()
        }
      }
      None
    } catch {
      case AGFalse(cex) => Some(cex)
      case e: AGSuccess =>
        if configuration.get().visualizeDFA then {
          for (ass,i) <- assumptions.zipWithIndex do {
            System.out.println(s"${ass.name} for process ${processes(i).systemName} alphabet: ${ass.alphabet}")
            ass.visualize()
          }
        }
        None
    }
  }
}


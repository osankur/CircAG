package fr.irisa.circag.dfa

import org.slf4j.Logger
import org.slf4j.LoggerFactory

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

import net.automatalib.automata.fsa.DFA
import net.automatalib.automata.fsa.impl.{FastDFA,FastDFAState}
import net.automatalib.automata.fsa.impl.FastDFAState
import net.automatalib.util.automata.fsa.{NFAs,DFAs}
import net.automatalib.words.impl.Alphabets;

import fr.irisa.circag._
import fr.irisa.circag.DLTS
import fr.irisa.circag.Trace
import fr.irisa.circag.configuration
import fr.irisa.circag.statistics

import com.microsoft.z3
import fr.irisa.circag.isPrunedSafety

enum AGResult extends Exception:
  case Success
  case GlobalPropertyProofFail(cex: Trace)
  case GlobalPropertyViolation(cex: Trace)
  case PremiseFail(processID: Int, cex: Trace)
  case AssumptionViolation(processID: Int, cex: Trace)

class DFAUnsatisfiableConstraints extends Exception

class SystemSpec(val ltsFiles: Array[File], var property: Option[DLTS]):
  val processes = ltsFiles.map(TA.fromFile(_))
  val nbProcesses = processes.size

/** Assume-guarantee property prover which can check each inductive premise, and the final premise
  * given used-provided assumptions for the processes.
  *
  * @param system
  *   system under study
  */
class DFAVerifier(val system: SystemSpec) {

  def this(ltsFiles: Array[File], property: Option[DLTS]) = {
    this(SystemSpec(ltsFiles, property))
  }

  private val logger = LoggerFactory.getLogger("CircAG")

  val nbProcesses = system.nbProcesses
  val proofSkeleton = DFAProofSkeleton(system)

  /** The assumption DLTS g_i for each process i. Initially the universal
    * automaton on respective alphabets.
    */
  protected var assumptions: Buffer[DLTS] = {
    (0 until nbProcesses)
      .map({ i =>
        val alph = proofSkeleton
          .getInterfaceAlphabet()
          .intersect(system.processes(i).alphabet)
        val dfa = FastDFA(Alphabets.fromList(alph.toList))
        val state = dfa.addState(true)
        for sigma <- alph do {
          dfa.addTransition(state, sigma, state)
        }
        // Visualization.visualize(dfa, Alphabets.fromList(processes(i).alphabet.toList))

        DLTS(s"g_${i}", dfa, alph)
      })
      .toBuffer
  }

  def getAssumption(processID: Int): DLTS = {
    assumptions(processID)
  }
  def setAssumption(i: Int, dlts: DLTS): Unit = {
    if (
      !dlts.alphabet.containsAll(
        proofSkeleton
          .getPropertyAlphabet()
          .intersect(system.processes(i).alphabet)
      )
    ) {
      throw Exception(
        s"The assumption alphabet is ${dlts.alphabet} but it must contain the intersection of the process alphabet and the property alphabet"
      )
    }
    assumptions(i) = dlts
    proofSkeleton.setAssumptionAlphabet(i, dlts.alphabet)
  }
  def setGlobalProperty(dlts: DLTS): Unit = {
    system.property = Some(dlts)
    proofSkeleton.setPropertyAlphabet(dlts.alphabet)
  }

  /** Checks processes(processID) |= A |> G
    *
    * where A is the set of assumptions on which processID depends (according to
    * proofSkeleton), and G is processID's assumption.
    *
    * @param processID
    *   id of the process
    * @pre
    *   guarantee.alphabet <= lts.alphabet (checked by assertion)
    * @pre
    *   All reachable states of the assumptions and ta are accepting (checked by
    *   assertion)
    * @pre
    *   assumptions do not contain the assumption for the process itself (not
    *   checked)
    * @return
    *   A counterexample to the premise: None if the premise holds; and
    *   Some(cexTrace) otherwise
    */
  def checkInductivePremise(processID: Int): Option[Trace] = {
    val guarantee = this.assumptions(processID)
    val localAssumptions =
      proofSkeleton.processDependencies(processID).map(this.assumptions(_))
    val ta = system.processes(processID)
    require(guarantee.alphabet.toSet.subsetOf(ta.alphabet))
    require(assumptions.forall({ dlts => dlts.dfa.isPrunedSafety }))
    statistics.Counters.incrementCounter("inductive-premise")
    logger.debug(
      s"Checking inductive premise for ${ta.systemName} whose assumption is over alphabet: ${guarantee.alphabet}"
    )
    var beginTime = System.nanoTime()
    // require(assumptions.forall({dlts => !dlts.dfa.getStates().forall(_.isAccepting())}))
    val guaranteeAlphabet = Alphabets.fromList(guarantee.alphabet.toList)
    val compG = DLTS(
      s"_comp_${guarantee.name}",
      DFAs.complement(
        guarantee.dfa,
        guaranteeAlphabet,
        FastDFA(guaranteeAlphabet)
      ),
      guarantee.alphabet
    )
    val liftedAssumptions =
      assumptions.map({ ass =>
        DLTS.liftAndStripNonAccepting(
          ass,
          ta.alphabet,
          Some(s"lifted_${ass.name}")
        )
      })
    val premiseProduct = TA.synchronousProduct(
      ta,
      compG :: liftedAssumptions.toList,
      Some("_accept_")
    )
    statistics.Timers.incrementTimer(
      "inductive-premise",
      System.nanoTime() - beginTime
    )
    premiseProduct.checkReachability(s"${compG.name}_accept_")
  }

  /** Check the final premise, that is, whether /\_{dtls in assumptions} dtls ->
    * property.
    *
    * @pre
    *   All states of the automata in lhs are accepting
    * @return
    *   None if the premise holds; and Some(cexTrace) otherwise
    */
  def checkFinalPremise(): Option[Trace] = {
    statistics.Counters.incrementCounter("final-premise")
    system.property match {
      case None => None
      case Some(propertyDLTS) =>
        val lhs =
          proofSkeleton.propertyDependencies().map(assumptions(_)).toList
        // Check precondition
        for dlts <- lhs do {
          val dfa = dlts.dfa
          dfa
            .getStates()
            .foreach({ s =>
              for a <- dlts.alphabet do {
                dfa
                  .getSuccessors(s, a)
                  .foreach({ sn =>
                    assert(dfa.isAccepting(sn))
                  })
              }
            })
        }
        val alph = Alphabets.fromList(propertyDLTS.alphabet.toList)
        val compG = DLTS(
          s"_comp_${propertyDLTS.name}",
          DFAs.complement(propertyDLTS.dfa, alph, FastDFA(alph)),
          propertyDLTS.alphabet
        )
        val premiseProduct = TA.synchronousProduct(
          TA.fromLTS[FastDFAState](
            compG,
            acceptingLabelSuffix = Some("_accept_")
          ),
          lhs
        )
        premiseProduct.checkReachability(s"${compG.name}_accept_")
    }
  }

  /** Check whether all processes accept the given trace
    */
  def checkCounterExample(trace: Trace): Boolean = {
    var returnValue = true
    class Break extends Exception
    try {
      for (ta, i) <- system.processes.zipWithIndex do {
        ta.checkTraceMembership(trace, Some(assumptions(i).alphabet)) match {
          case None => // ta rejects
            throw Break()
          case _ => // ta accepts
            ()
        }
      }
    } catch {
      case _: Break =>
        returnValue = false
    }
    returnValue
  }

  /** Apply AG rule with given assumptions and proof skeleton: Checks inductive
    * premises for all processes, then checks the final premise if
    * proveGlobalProperty is true.
    * @return
    */
  def applyAG(proveGlobalProperty: Boolean = true): AGResult = {
    // A proof for a process must not depend on itself
    logger.debug(s"applying Assume-Guarantee rule with alphabets: ${assumptions.map(_.alphabet)}")
    try {
      for (ta, i) <- system.processes.zipWithIndex do {
        // DFAAssumeGuaranteeVerifier.checkInductivePremise(ta, proofSkeleton.processDependencies(i).map(assumptions(_)).toList, assumptions(i))
        this.checkInductivePremise(i) match {
          case None =>
            logger.info(s"${GREEN}Premise ${i} passed${RESET}")
          case Some(cexTrace) =>
            latestCex = cexTrace
            logger.info(
              s"${RED}Premise ${i} failed with cex: ${cexTrace}${RESET}"
            )
            if checkCounterExample(cexTrace) then {
              logger.info(s"\tCex to assumption ${i} confirmed: ${cexTrace}")
              throw AGResult.AssumptionViolation(i, cexTrace)
            } else throw AGResult.PremiseFail(i, cexTrace)
        }
      }
      // DFAAssumeGuaranteeVerifier.checkFinalPremise(proofSkeleton.propertyDependencies.map(assumptions(_)).toList, propertyDLTS)
      if system.property == None || !proveGlobalProperty then
        throw AGResult.Success
      this.checkFinalPremise() match {
        case None =>
          logger.info(s"${GREEN}Final premise succeeded${RESET}")
          AGResult.Success
        case Some(cexTrace) =>
          latestCex = cexTrace
          logger.info(
            s"${RED}Final premise failed with cex: ${cexTrace}${RESET}"
          )
          // If all processes contain proj(cexTrace), then return false, otherwise continue
          if checkCounterExample(cexTrace) then {
            logger.info(s"\tCex confirmed: ${cexTrace}")
            throw AGResult.GlobalPropertyViolation(cexTrace)
          } else {
            logger.info(s"\tCex *spurious*: ${cexTrace}")
            throw AGResult.GlobalPropertyProofFail(cexTrace)
          }
      }
    } catch {
      case ex: AGResult => ex
    }
  }
  // Latest cex encountered in any premise check. This is for debugging.
  protected var latestCex = List[String]()
}


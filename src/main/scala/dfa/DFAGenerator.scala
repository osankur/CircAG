package fr.irisa.circag.dfa

import scala.collection.mutable.{HashMap, Buffer, Map}
import collection.JavaConverters._
import collection.convert.ImplicitConversions._
import scala.util.control.Breaks.{break,breakable}
import org.slf4j.Logger
import org.slf4j.LoggerFactory

import io.AnsiColor._
import com.microsoft.z3

import fr.irisa.circag.statistics
import fr.irisa.circag.configuration
import fr.irisa.circag.{Trace, DLTS, Alphabet}

/** Strategy to add constraints on assumptions.
  *
  *   - Disjunctive follows the CAV16 paper; keeps disjunctive formulas and guesses the set of DFAs all at once.
  *   - DisjunctiveSeparate adds disjunctive formulae as Disjunctive, but to learn DFAs,
  *     it first extracts a satisfying assignment, and then learns separately each DFA.
  *   - Eager does the following: given a counterexample trace w for A_i |=
  *     Gamma_i |> g_i, check if for some j in Gamma_i, w|_{alpha_j} not in
  *     L(A_j), if yes then add the single constraint not(w|_{alpha_j} |=
  *     L(g_j)). Otherwise, add w_{alpha_i} |= L(g_i).
  */
enum ConstraintStrategy:
  case Bolt
  case DisjunctiveSeparate
  case Disjunctive
  case LoggingDisjunctive
  case Eager

/** Stores constraints on assumptions, and generates them by first solving these constraints. 
  *
  * @param system
  * @param proofSkeleton
  * @param dfaLearnerAlgorithm
  */
trait DFAGenerator(
    val system : SystemSpec,
    val proofSkeleton: DFAProofSkeleton
) {

  protected val nbProcesses = proofSkeleton.nbProcesses

  /** Reinitialize the solver and samples.
    */
  def reset(): Unit

  /**
    * Given a trace that violates the final premise, check the counterexample: if realizable, 
    * throw AGResult.GlobalPropertyViolation(trace), otherwise update the constraints
    *
    * @param trace that violates the final premise
    * @throws AGResult.GlobalPropertyViolation
    */
  def refineByFinalPremiseCounterexample(trace: Trace): Unit

  /**
    * Update constraints given a process id and a trace that violates its inductive premise
    *
    * @param processID process id
    * @param cexTrace a trace that violates the inductive premise of processID
    */
  def refineByInductivePremiseCounterexample(processID : Int, cexTrace : Trace) : Unit

  /** Generate assumptions satisfying the constraints, except that those
    * processes whose DLTSs are given as argument. Note that fixing some of the
    * assumptions can make the constraints unsatisfiable.
    *
    * @param fixedAssumptions
    *   process indices and their fixed assumptions
    * @return
    *   None if the constraints are unsat, and an assumption for each process
    *   otherwise.
    */
  def generateAssumptions(
      fixedAssumptions: Map[Int, DLTS] = Map()
  ): Option[Buffer[DLTS]]
}


object DFAGenerator {
  def getGenerator(
      system : SystemSpec,
      proofSkeleton: DFAProofSkeleton,
      dfaLearnerAlgorithm: DFALearningAlgorithm,
      constraintStrategy : ConstraintStrategy
    ) : DFAGenerator = {
    constraintStrategy match {
      case ConstraintStrategy.DisjunctiveSeparate => 
        DFADisjunctiveSeparateGenerator(system, proofSkeleton, dfaLearnerAlgorithm)
      case ConstraintStrategy.Disjunctive => 
        DFADisjunctiveGenerator(system, proofSkeleton, dfaLearnerAlgorithm)
      case ConstraintStrategy.Bolt => 
        DFABoltGenerator(system, proofSkeleton, dfaLearnerAlgorithm)
      case ConstraintStrategy.LoggingDisjunctive => 
        LoggingDFADisjunctiveGenerator(system, proofSkeleton, dfaLearnerAlgorithm)
      case ConstraintStrategy.Eager => DFAEagerGenerator(system, proofSkeleton, dfaLearnerAlgorithm)
    }
  }
}



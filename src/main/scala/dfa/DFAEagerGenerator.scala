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

/**
  * Eager DFA generator which keeps positive and negative samples persistently.
  *
  * @param _system
  * @param _proofSkeleton
  * @param _dfaLearnerAlgorithm
  */
class DFAEagerGenerator(
    _system : SystemSpec,
    _proofSkeleton: DFAProofSkeleton,
    dfaLearnerAlgorithm: DFALearningAlgorithm
) extends DFAGenerator(_system, _proofSkeleton) {  
  val logger = LoggerFactory.getLogger(this.getClass)


  val samples = Buffer.tabulate(nbProcesses)(_ => Buffer[Trace]())

  // Samples that were used to compute assumptions the last time. Here the prefix closure of the positive samples were added
  protected var positiveSamples = Buffer.tabulate(nbProcesses)({ _ =>
    Set[Trace]()
  })
  protected var negativeSamples = Buffer.tabulate(nbProcesses)({ _ =>
    Set[Trace]()
  })

  // a learner object per process
  protected val learners: Buffer[DFALearner] = Buffer.tabulate(
    proofSkeleton.nbProcesses
  )(i =>
    dfaLearnerAlgorithm match {
      case DFALearningAlgorithm.RPNI =>
        new RPNILearner(
          s"assumption_${i}_${system.processes(i).systemName}",
          proofSkeleton.assumptionAlphabets(i)
        )
      case DFALearningAlgorithm.SAT =>
        new SATLearner(s"assumption_${i}", proofSkeleton.assumptionAlphabets(i))
      case DFALearningAlgorithm.UFSAT =>
        new UFSATLearner(
          s"assumption_${i}",
          proofSkeleton.assumptionAlphabets(i)
        )
    }
  )

  this.reset()

  /** Reinitialize the solver and samples.
    */
  def reset(): Unit = {
    this.samples.foreach(_.clear())
    this.positiveSamples = Buffer.tabulate(nbProcesses)({ _ => Set[Trace](List[String]()) })
    this.negativeSamples = Buffer.tabulate(nbProcesses)({ _ => Set[Trace]() })
  }

  override def refineByInductivePremiseCounterexample(processID : Int, cexTrace : Trace) : Unit = {
        // Let i = processID.
        // We are here because cexTrace |= processes(i), cexTrace /|= assumption(i), forall j in Gamma_i, prefix(cexTrace) |= assumption(j).
        // If exists j in dependencies(i) such that prefix(cexTrace) /|= process(j),
        //    then add prefix(cexTrace) /|= assumption(j)
        // else add cexTrace |= assumption(i).
        breakable{
          proofSkeleton.processDependencies(processID).foreach {
            j => 
              val prefixCexTrace = cexTrace.dropRight(1)
              logger.debug(s"Checking if proj of ${prefixCexTrace} to j-th ass alphabet is accepted by process ${j}")
              if system.processes(j).checkTraceMembership(prefixCexTrace, Some(proofSkeleton.assumptionAlphabets(j))) == None then {
                logger.debug(s"Process ${j} rejects ${prefixCexTrace}: adding negative constraint for its assumption")
                negativeSamples(j) = negativeSamples(j).incl(prefixCexTrace.filter(proofSkeleton.assumptionAlphabets(j).contains(_)))
                break
              }
          }
          logger.debug(s"None of the processes have rejected prefix of ${cexTrace}. Adding positive constraint for assumption ${processID}")
          val projCexTrace = cexTrace.filter(proofSkeleton.assumptionAlphabets(processID).contains(_))          
          for i <- 0 until projCexTrace.size do {
            positiveSamples(processID) = positiveSamples(processID).incl(projCexTrace.dropRight(i))
          }
    }
  }

  override def refineByFinalPremiseCounterexample(trace: Trace): Unit = {
    breakable{
      for j <- 0 until nbProcesses do {
          logger.debug(s"Checking if proj of ${trace} to j-th ass alphabet is accepted by process ${j}")
          if system.processes(j).checkTraceMembership(trace, Some(proofSkeleton.assumptionAlphabets(j))) == None then {
            logger.debug(s"Process ${j} rejects ${trace}: adding negative constraint for its assumption")
            negativeSamples(j) = negativeSamples(j).incl(trace.filter(proofSkeleton.assumptionAlphabets(j).contains(_)))
            break
          }
      }
      throw AGResult.GlobalPropertyViolation(trace)
    }
  }


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
  override def generateAssumptions(
      fixedAssumptions: Map[Int, DLTS] = Map()
  ): Option[Buffer[DLTS]] = {
    logger.debug(s"Learning DFA for following assumptions")
    for i <- 0 until nbProcesses do {
      logger.debug(s"\tPos($i) = ${positiveSamples(i)}")
      logger.debug(s"\tNeg($i) = ${negativeSamples(i)}")
    }
    Some(
        Buffer.tabulate(proofSkeleton.nbProcesses)(i =>
          if fixedAssumptions.contains(i) then fixedAssumptions(i)
          else {
            learners(i).setPositiveSamples(positiveSamples(i))
            learners(i).setNegativeSamples(negativeSamples(i))
            val dlts = learners(i).getDLTS()
            logger.debug(s"DLTS${i} has size ${dlts.dfa.size()}")
            // Test
            for trace <- positiveSamples(i) do  {
              assert(dlts.dfa.accepts(trace))
            }
            for trace <- negativeSamples(i) do  {
              assert(!dlts.dfa.accepts(trace))
            }
            dlts
          }
        )
      )
    }
}

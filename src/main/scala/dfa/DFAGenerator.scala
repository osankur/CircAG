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
  *   - Disjunctive follows the CAV16 paper; it often adds a disjunctive formula.
  *   - Eager does the following: given a counterexample trace w for A_i |=
  *     Gamma_i |> g_i, check if for some j in Gamma_i, w|_{alpha_j} not in
  *     L(A_j), if yes then add the single constraint not(w|_{alpha_j} |=
  *     L(g_j)). Otherwise, add w_{alpha_i} |= L(g_i).
  */
enum ConstraintStrategy:
  case Disjunctive
  case Eager

/** Stores constraints on assumptions, and generates them by first solving these constraints. 
  *
  * @param system
  * @param proofSkeleton
  * @param dfaLearnerAlgorithm
  */
trait DFAGenerator(
    val system : SystemSpec,
    val proofSkeleton: DFAProofSkeleton,
    val dfaLearnerAlgorithm: DFALearningAlgorithm =
      DFALearningAlgorithm.RPNI
) {

  protected val nbProcesses = proofSkeleton.nbProcesses

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
          s"assumption_${i}",
          proofSkeleton.assumptionAlphabets(i)
        )
      case DFALearningAlgorithm.SAT =>
        new SATLearner(s"assumption_${i}", proofSkeleton.assumptionAlphabets(i))
      case DFALearningAlgorithm.UFSAT =>
        new UFSATLearner(
          s"assumption_${i}",
          proofSkeleton.assumptionAlphabets(i)
        )
      case _ => throw Exception("Not implemented yet")
    }
  )

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
      dfaLearnerAlgorithm: DFALearningAlgorithm =
        DFALearningAlgorithm.RPNI,
      constraintStrategy : ConstraintStrategy
    ) : DFAGenerator = {
    constraintStrategy match {
      case ConstraintStrategy.Disjunctive => DFADisjunctiveGenerator(system, proofSkeleton, dfaLearnerAlgorithm)
      case _ => DFAEagerGenerator(system, proofSkeleton, dfaLearnerAlgorithm)
    }
  }
}

class DFAEagerGenerator(
    _system : SystemSpec,
    _proofSkeleton: DFAProofSkeleton,
    _dfaLearnerAlgorithm: DFALearningAlgorithm =
      DFALearningAlgorithm.RPNI
) extends DFAGenerator(_system, _proofSkeleton, _dfaLearnerAlgorithm) {
  val logger = LoggerFactory.getLogger("CircAG")
  val samples = Buffer.tabulate(nbProcesses)(_ => Buffer[Trace]())
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
    None
      Some(
        Buffer.tabulate(proofSkeleton.nbProcesses)(i =>
          if fixedAssumptions.contains(i) then fixedAssumptions(i)
          else {
            learners(i).setPositiveSamples(positiveSamples(i))
            learners(i).setNegativeSamples(negativeSamples(i))
            learners(i).getDLTS()
          }
        )
      )
    }
}


class DFADisjunctiveGenerator(
    _system : SystemSpec,
    _proofSkeleton: DFAProofSkeleton,
    _dfaLearnerAlgorithm: DFALearningAlgorithm =
      DFALearningAlgorithm.RPNI,
    constraintStrategy: ConstraintStrategy = 
      ConstraintStrategy.Disjunctive
) extends DFAGenerator(_system, _proofSkeleton, _dfaLearnerAlgorithm) {
  val logger = LoggerFactory.getLogger("CircAG")
  protected val z3ctx = {
    val cfg = HashMap[String, String]()
    cfg.put("model", "true")
    z3.Context(cfg);
  }

  // Boolean variable corresponding to each pair (pr,trace)
  protected val toVars = HashMap[(Int, Trace), z3.BoolExpr]()
  protected val toIndexedTraces = HashMap[z3.BoolExpr, (Int, Trace)]()

  protected var solver = z3ctx.mkSolver()

  // Set of all samples added so far
  protected val samples = Buffer.tabulate(nbProcesses)({ _ =>
    Buffer[(Trace, z3.BoolExpr)]()
  })


  this.reset()

  /** Return the unique SAT variable to the given pair (process, trace)
    *
    * @param process
    * @param trace
    * @return
    */
  private def varOfIndexedTrace(process: Int, trace: Trace): z3.BoolExpr = {
    if (toVars.contains((process, trace))) then {
      toVars((process, trace))
    } else {
      val v = z3ctx.mkBoolConst(z3ctx.mkSymbol(s"${(process, trace)}"))
      toVars.put((process, trace), v)
      toIndexedTraces.put(v, (process, trace))
      samples(process).append((trace, v))
      updateTheoryConstraints(process, samples(process).size - 1)
      v
    }
  }

  /** Solve the constraints and generate samples that each assumption must
    * satisfy. All process index - DLTS pairs given as arguments are assumed to
    * be fixed, so we update the constraints (temporarily) so that the solution
    * respects these existing assumptions.
    */
  private def generateSamples(
      fixedAssumptions: Map[Int, DLTS] = Map()
  ): Option[(Buffer[Set[Trace]], Buffer[Set[Trace]])] = {
    var positiveSamples = Buffer.tabulate(nbProcesses)({ _ => Set[Trace]() })
    var negativeSamples = Buffer.tabulate(nbProcesses)({ _ => Set[Trace]() })

    solver.push()
    // For all processes whose assumptions are fixed, and for all samples for process i,
    // if the current assumption accepts the sample, then add this as a constraint; otherwise, add the negation.
    for (i, dlts) <- fixedAssumptions do {
      for (trace, v) <- samples(i) do {
        if dlts.dfa.accepts(trace.filter(proofSkeleton.assumptionAlphabets(i)))
        then {
          solver.add(v)
        } else {
          // System.out.println(s"Ass ${i} accepts word: ${(trace.filter(proofSkeleton.assumptionAlphabets(i)))}: ${dlts.dfa.accepts(trace.filter(proofSkeleton.assumptionAlphabets(i)))}")
          // dlts.visualize()
          solver.add(z3ctx.mkNot(v))
        }
      }
    }
    var beginTime = System.nanoTime()
    if (solver.check() == z3.Status.UNSATISFIABLE) {
      statistics.Timers.incrementTimer("z3", (System.nanoTime() - beginTime))
      for ass <- solver.getAssertions() do {
        println(ass)
      }
      solver.pop()
      None
    } else {
      val m = solver.getModel()
      // Compute sets of negative samples, and prefix-closed sets of pos samples from the valuation
      // We only make this update for
      samples.zipWithIndex.foreach({ (isamples, i) =>
        isamples.foreach({ (trace, v) =>
          m.evaluate(v, true).getBoolValue() match {
            case z3.enumerations.Z3_lbool.Z3_L_TRUE =>
              val sample = trace.filter(proofSkeleton.assumptionAlphabets(i))
              // Add all prefixes
              for k <- 0 to sample.size do {
                positiveSamples(i).add(sample.dropRight(k))
              }
            case z3.enumerations.Z3_lbool.Z3_L_FALSE =>
              negativeSamples(i).add(
                trace.filter(proofSkeleton.assumptionAlphabets(i))
              )
            case _ =>
              val sample = trace.filter(proofSkeleton.assumptionAlphabets(i))
              // Add all prefixes
              for k <- 0 to sample.size do {
                positiveSamples(i).add(sample.dropRight(k))
              }
          }
        })
      })
      statistics.Timers.incrementTimer("z3", (System.nanoTime() - beginTime))
      solver.pop()
      Some(positiveSamples, negativeSamples)
    }
  }

  /** Add boolean expression to the solver with the following property: For each pair of
    * traces w, w', if proj(w, alphabet) is a prefix of proj(w', alphabet), then
    * var(w') -> var(w). Here w ranges over samples(process)(sampleIndex..) and
    * w' ranges over samples(process)(sampleIndex-1)
    *
    * @param process
    * @param sampleIndex
    * @return
    */
  private def updateTheoryConstraints(
      process: Int,
      sampleIndex: Int = 0
  ): Unit = {
    println(s"updateTheoryConstraints(process = $process). Process alphabet: ${system.processes(process).alphabet} Ass alphabet: ${proofSkeleton.assumptionAlphabets(process)}")
    for i <- sampleIndex until samples(process).size do {
      val projTrace_i = this
        .samples(process)(i)
        ._1
        .filter(proofSkeleton.assumptionAlphabets(process).contains(_))
      val vi = this.samples(process)(i)._2
      for j <- 0 until i do {
        val projTrace_j = this
          .samples(process)(j)
          ._1
          .filter(proofSkeleton.assumptionAlphabets(process).contains(_))
        val vj = this.samples(process)(j)._2
        // System.out.println(s"Comparing ${samples(process)(i)._1} - ${samples(process)(j)._1}")
        // System.out.println(s"Whose projections are: ${projTrace_i} - ${projTrace_j}")

        if projTrace_i.startsWith(projTrace_j) then {
          solver.add(z3ctx.mkImplies(vi, vj))
          // System.out.println(s"\t $vi -> $vj (theory)")
        }
        if projTrace_j.startsWith(projTrace_i) then {
          solver.add(z3ctx.mkImplies(vj, vi))
          // System.out.println(s"\t   $vi <- $vj (theory)")
        }
      }
    }
  }

  /** Reinitialize the solver and samples.
    */
  def reset(): Unit = {
    this.solver = z3ctx.mkSolver()
    this.samples.foreach(_.clear())
    this.toVars.clear()
    this.toIndexedTraces.clear()

    this.positiveSamples = Buffer.tabulate(nbProcesses)({ _ => Set[Trace]() })
    this.negativeSamples = Buffer.tabulate(nbProcesses)({ _ => Set[Trace]() })
    // the empty word must be accepted by all
    solver.add(z3ctx.mkAnd((0 until nbProcesses).map({ i =>
      varOfIndexedTrace(i, List[String]())
    }): _*))
  }

  override def refineByInductivePremiseCounterexample(processID : Int, cexTrace : Trace) : Unit = {
    constraintStrategy match {
      case ConstraintStrategy.Disjunctive => 
        val prefixInP = system.property match{
          case None => false
          case Some(propertyDLTS) => 
            propertyDLTS.dfa.accepts(
              cexTrace.dropRight(1).filter(propertyDLTS.alphabet.contains(_))
            )
        }
        val traceInP = system.property match{
          case None => false
          case Some(propertyDLTS) => 
            propertyDLTS.dfa.accepts(cexTrace.filter(propertyDLTS.alphabet.contains(_)))
        }
        if (prefixInP && !traceInP) then {
          addDisjunctiveConstraint(processID, cexTrace, 22)
        } else if (cexTrace.size > 0 && !prefixInP && !traceInP) then {
          addDisjunctiveConstraint(processID, cexTrace, 29)
        } else {
          addDisjunctiveConstraint(processID, cexTrace, 34)
        }
      case ConstraintStrategy.Eager => 
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
                solver.add(z3ctx.mkNot(varOfIndexedTrace(j, prefixCexTrace)))
                break
              }
          }
          logger.debug(s"None of the processes have rejected prefix of ${cexTrace}. Adding positive constraint for assumption ${processID}")
          solver.add(varOfIndexedTrace(processID, cexTrace))
        }
    }
  }

  private def addDisjunctiveConstraint(process: Int, trace: Trace, constraintType: Int): Unit = {
    constraintType match {
      case 34 =>
        assert(trace.size > 0)
        val prefix = trace.dropRight(1)
        val lhs =
          if prefix.size > 0 then
            proofSkeleton
              .processDependencies(process)
              .map({ j =>
                z3ctx.mkNot(varOfIndexedTrace(j, prefix))
              })
              .toSeq
          else {
            Seq(z3ctx.mkFalse())
          }

        val newConstr =
          z3ctx.mkOr(z3ctx.mkOr(lhs: _*), varOfIndexedTrace(process, trace))
        logger.debug(s"New constraint ${newConstr}")
        solver.add(newConstr)
      case 22 =>
        val prefix = trace.dropRight(1)
        val term1 =
          z3ctx.mkOr(
            proofSkeleton
              .processDependencies(process)
              .map({ j =>
                z3ctx.mkNot(varOfIndexedTrace(j, prefix))
              })
              .toSeq: _*
          )
        val term2 =
          z3ctx.mkAnd(
            varOfIndexedTrace(process, trace),
            z3ctx.mkOr(
              (proofSkeleton.propertyDependencies() - process)
                .map({ j =>
                  z3ctx.mkNot(varOfIndexedTrace(j, trace))
                })
                .toSeq: _*
            )
          )
        val newConstr = z3ctx.mkOr(term1, term2)
        solver.add(newConstr)
        logger.debug(s"Adding ${newConstr}")
      case 29 =>
        val prefix = trace.dropRight(1)
        val term1 =
          z3ctx.mkOr(
            proofSkeleton
              .processDependencies(process)
              .map({ j =>
                z3ctx.mkNot(varOfIndexedTrace(j, prefix))
              })
              .toSeq: _*
          )
        val term2 =
          z3ctx.mkAnd(
            varOfIndexedTrace(process, trace),
            z3ctx.mkOr(
              (proofSkeleton.propertyDependencies() -- proofSkeleton
                .processDependencies(process) - process)
                .map({ j =>
                  z3ctx.mkNot(varOfIndexedTrace(j, trace))
                })
                .toSeq: _*
            )
          )
        val newConstraint = z3ctx.mkOr(term1, term2)
        solver.add(newConstraint)
        logger.debug(s"New constraint default ${newConstraint}")
    }
  }

  override def refineByFinalPremiseCounterexample(trace: Trace): Unit = {
    breakable{
      for j <- 0 until nbProcesses do {
          logger.debug(s"Checking if proj of ${trace} to j-th ass alphabet is accepted by process ${j}")
          if system.processes(j).checkTraceMembership(trace, Some(proofSkeleton.assumptionAlphabets(j))) == None then {
            break
          }
      }
      throw AGResult.GlobalPropertyViolation(trace)
    }
    val newConstraint = z3ctx.mkOr(
      z3ctx.mkOr(
        proofSkeleton
          .propertyDependencies()
          .map({ j => z3ctx.mkNot(varOfIndexedTrace(j, trace)) })
          .toSeq: _*
      )
    )
    logger.debug(s"Adding constraint ${newConstraint}")
    solver.add(newConstraint)
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
    generateSamples(fixedAssumptions) match {
      case None => None // Unsat
      case Some(posSamples, negSamples) =>
        Some(
          Buffer.tabulate(proofSkeleton.nbProcesses)(i =>
            if fixedAssumptions.contains(i) then fixedAssumptions(i)
            else {
              learners(i).setPositiveSamples(posSamples(i))
              learners(i).setNegativeSamples(negSamples(i))
              learners(i).getDLTS()
            }
          )
        )
    }
  }
}



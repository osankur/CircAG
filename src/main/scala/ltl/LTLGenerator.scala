package fr.irisa.circag.ltl

import org.slf4j.Logger
import org.slf4j.LoggerFactory

import scala.collection.mutable.{HashMap,Buffer}
import scala.collection.mutable
import scala.collection.immutable.Set
import collection.JavaConverters._
import collection.convert.ImplicitConversions._

import io.AnsiColor._

import com.microsoft.z3

import fr.irisa.circag.statistics
import fr.irisa.circag.configuration
import fr.irisa.circag.{Trace, Lasso, DLTS, Alphabet}
import fr.irisa.circag.{pruned, filter, suffix, semanticEquals, size}


class LTLGenerator(proofSkeleton : LTLProofSkeleton, ltlLearningAlgorithm : LTLLearningAlgorithm) {
  protected val z3ctx = {
    val cfg = mutable.HashMap[String, String]()
    cfg.put("model", "true")
    z3.Context(cfg);
  }

  protected val nbProcesses: Int = proofSkeleton.nbProcesses
  // Set of all samples added so far for each process
  protected val samples = Buffer.tabulate(nbProcesses)({_ => Buffer[(Lasso,z3.BoolExpr)]()})
  // Boolean variable corresponding to each pair (process,trace)
  protected val toVars = HashMap[(Int,Lasso), z3.BoolExpr]()
  protected val toIndexedLassos = HashMap[z3.BoolExpr, (Int,Lasso)]()

  protected var solver = z3ctx.mkSolver()

  protected var positiveSamples = Buffer.tabulate(nbProcesses)({_ => Set[Lasso]()})
  protected var negativeSamples = Buffer.tabulate(nbProcesses)({_ => Set[Lasso]()})

  // The minterm corresponding to the current assignment of the constraints
  protected var currentAssignment = z3ctx.mkFalse()

  protected val learners : Buffer[LTLLearner] = Buffer.tabulate(proofSkeleton.nbProcesses)
    (i => SATLearner(s"assumption${i}", proofSkeleton.assumptionAlphabet(i), universal = proofSkeleton.isCircular(i), ltlLearningAlgorithm))

  /**
    * Reinitialize the solver. Resets the constraints but keeps those coming from incremental traces
    */
  def reset() : Unit = {
    this.solver = z3ctx.mkSolver()
    this.samples.foreach(_.clear())
    this.toVars.clear()
    this.toIndexedLassos.clear()

    this.positiveSamples = Buffer.tabulate(nbProcesses)({_ => Set[Lasso]()})
    this.negativeSamples = Buffer.tabulate(nbProcesses)({_ => Set[Lasso]()})
  }

  /**
    * Return the unique SAT variable to the given pair (process, lasso) after possibly creating it
    *
    * @param process
    * @param trace
    * @return
    */
  private def varOfIndexedTrace(process : Int, lasso : Lasso) : z3.BoolExpr = {
    if (toVars.contains((process, lasso))) then {
      toVars((process, lasso))
    } else {
      val v = z3ctx.mkBoolConst(z3ctx.mkSymbol(s"${(process,lasso)}"))
      toVars.put((process,lasso), v)
      toIndexedLassos.put(v, (process, lasso))
      samples(process).append((lasso,v))
      // Update theory constraints for this new variable, w.r.t. previous ones
      updateTheoryConstraints(process, samples(process).size-1)
      v
    }
  } 

  /**
    * Add the constraint that for all lassos l in samples(process)(sampleIndex..), and all lassos l' in samples(process),
    * if l and l' are semantically equal when projected to process' assumption alphabet, then the respective Boolean variables are equal.
    *
    * @param process process identifier for which these constraints are to be added
    * @param sampleIndex only consider lassos l of index samplesIndex..samples.size-1; default is 0
    * @return
    */
  private def updateTheoryConstraints(process : Int, sampleIndex : Int = 0) : Unit = {
    for i <- sampleIndex until samples(process).size do {
      val projLasso_i = this.samples(process)(i)._1.filter(proofSkeleton.assumptionAlphabet(process).contains(_))
      val vi = this.samples(process)(i)._2
      for j <- 0 until i do {
        val projLasso_j = this.samples(process)(j)._1.filter(proofSkeleton.assumptionAlphabet(process).contains(_))
        val vj = this.samples(process)(j)._2
        if projLasso_i.semanticEquals(projLasso_j) then {
          solver.add(z3ctx.mkEq(vi, vj))
        }
      }
    }
  }

 
  /**
   * Solve the constraints and generate samples that each assumption must satisfy.
   * All process index - DLTS pairs given as arguments are assumed to be fixed, 
   * so we update the constraints (temporarily) so that the solution respects these existing assumptions.
   */
  private def generateSamples(fixedAssumptions : mutable.Map[Int,LTL] = mutable.Map()) : Option[(Buffer[Set[Lasso]], Buffer[Set[Lasso]])] = {
    var positiveSamples = Buffer.tabulate(nbProcesses)({_ => collection.immutable.Set[Lasso]()})
    var negativeSamples = Buffer.tabulate(nbProcesses)({_ => Set[Lasso]()})

    solver.push()
    // For all processes whose assumptions are fixed, and for all samples for process i,
    // if the current assumption accepts the sample, then add this as a constraint; otherwise, add the negation.
    for (i, ltl) <- fixedAssumptions do {
      for (lasso, v) <- samples(i) do {
        if ltl.accepts(lasso.filter(proofSkeleton.assumptionAlphabet(i))) then {
          solver.add(v)
        } else {
          solver.add(z3ctx.mkNot(v))
        }
      }
    }

    println("Generating assignment")
    // for ass <- solver.getAssertions() do
    //   println(ass)

    var beginTime = System.nanoTime()
    if(solver.check() == z3.Status.UNSATISFIABLE){
      statistics.Timers.incrementTimer("z3", (System.nanoTime() - beginTime))
      solver.pop()
      println("Constraints are unsat")
      None
    } else {
      val m = solver.getModel()
      currentAssignment = z3ctx.mkTrue()
      // Compute sets of negative samples, and sets of pos samples from the valuation
      samples.zipWithIndex.foreach({
        (isamples, i) => 
          isamples.foreach({
            (lasso, v) =>
              m.evaluate(v, true).getBoolValue() match {
                case z3.enumerations.Z3_lbool.Z3_L_TRUE =>
                  val sample = lasso.filter(proofSkeleton.assumptionAlphabet(i))
                  positiveSamples(i) = positiveSamples(i).incl(sample)
                  currentAssignment = z3ctx.mkAnd(currentAssignment, v)
                case z3.enumerations.Z3_lbool.Z3_L_FALSE => 
                  negativeSamples(i) = negativeSamples(i).incl(lasso.filter(proofSkeleton.assumptionAlphabet(i)))
                  currentAssignment = z3ctx.mkAnd(currentAssignment, z3ctx.mkNot(v))
                case _ =>
                  val sample = lasso.filter(proofSkeleton.assumptionAlphabet(i))
                  positiveSamples(i) = positiveSamples(i).incl(sample)
                  currentAssignment = z3ctx.mkAnd(currentAssignment, v)
              }
          })
      })
      println("Generated:")
      println(s"Minterm: ${currentAssignment}")
      println(s"Positive samples: ${positiveSamples}")
      println(s"Negative samples: ${negativeSamples}")

      statistics.Timers.incrementTimer("z3", (System.nanoTime() - beginTime))
      solver.pop()
      Some(positiveSamples, negativeSamples)
    }
  }

  /**
    * @brief exclude the current assignment
    */
  private def blockCurrentAssignment() : Unit = {
    solver.add(z3ctx.mkNot(currentAssignment))
  }

  /**
    * This implements the approximate refinement by adding constraints to rule out lasso.
    * 
    * @notes All the information about the query is not useful for the approximate version but will be useful in a future exact refinement version
    * in order to extract the index k_0.
    * @param lasso counterexample lasso
    * @param query premise query whose failure gave lasso
    * @param violationIndex when the query concerns a circular process, the step where the RHS of the until formula of the premise query holds.
    */
  def refineConstraintsByPremiseQuery(lasso : Lasso, query : PremiseQuery, violationIndex : Int) : Unit = {
    query match {
      case CircularPremiseQuery(_processID, noncircularDeps, circularDeps, instantaneousDeps, mainAssumption, fairness) => 
        val constraint =
          // \/_{j in nc-deps} not(rho |= phi_j)
          // val ncDeps = z3ctx.mkOr(noncircularDeps map { (i,_) => z3ctx.mkNot(getAssumptionAcceptsLassoFormula(i, lasso, violationIndex))} : _* )
          val ncDeps = z3ctx.mkOr(noncircularDeps map { (i,_) => z3ctx.mkNot(varOfIndexedTrace(i, lasso))} : _* )

          // \/_{j in c-deps} \/_{0<= k <= k0-1} not(rho, k |= phi_j')
          val cDeps = z3ctx.mkOr(
              (circularDeps map {(i,_) => 
                (0 until violationIndex) map {
                    k => z3ctx.mkNot(varOfIndexedTrace(i, lasso.suffix(k)))
                }
              }).flatten
            : _*)

          // \/_{j in inst-deps} not(rho, k0 |= phi_j')
          val instDeps = z3ctx.mkOr(instantaneousDeps map { (i,_) => z3ctx.mkNot(varOfIndexedTrace(i, lasso.suffix(violationIndex)))} : _* )
          // rho, k0 |= phi_i'
          val main = varOfIndexedTrace(_processID, lasso.suffix(violationIndex))
          z3ctx.mkOr(ncDeps, cDeps, instDeps, main)
        println(s"refineConstraintByQuery violationIndex=${violationIndex}: ${constraint}")
        solver.add(constraint)

      case NonCircularPremiseQuery(_processID, dependencies, mainAssumption, fairness) => 
        // mainAssumption 
        val main = varOfIndexedTrace(_processID, lasso)
        val deps = proofSkeleton.processDependencies(_processID).map(
          { i => 
            if !proofSkeleton.isCircular(i) then 
              // not(rho |= phi_i)
              z3ctx.mkNot(varOfIndexedTrace(i, lasso))
            else {
              // not( /\_{0<= k <= |rho|} rho,k |= phi_i' ) <=> not( rho |= G(phi_i') )
              z3ctx.mkNot(z3ctx.mkAnd(
                (0 until lasso.size) map {
                    k => varOfIndexedTrace(i, lasso.suffix(k))
                } : _*
              ))
            }
          }).toList
        val constraint = z3ctx.mkOr(main, z3ctx.mkOr(deps : _*))
        println(s"refineConstraintByQuery: ${constraint}")
        solver.add(constraint)
    }
  }
  def refineConstraintsByFinal(lasso : Lasso) : Unit = {
    val constraint = z3ctx.mkOr(
        (0 until nbProcesses).map(
          { i => 
            if !proofSkeleton.isCircular(i) then {
              z3ctx.mkNot(varOfIndexedTrace(i, lasso))
            } else {
              // not( /\_{0<= k <= |rho|} rho,k |= phi_i' ) <=> not( rho |= G(phi_i') )
              z3ctx.mkNot(z3ctx.mkAnd(
                (0 until lasso.size) map {
                    k => varOfIndexedTrace(i, lasso.suffix(k))
                } : _*
              ))
            }
          }) 
      :_*)
    println(s"refineConstraintByFinal: ${constraint}")
    solver.add(constraint)
  }


  /**
    * Generate assumptions satisfying the constraints, except that those processes 
    * whose LTL formulas are given in fixedAssumptions. Note that fixing 
    * some of the assumptions can make the constraints unsatisfiable.
    *
    * @param fixedAssumptions partial map from process indices to their fixed assumptions
    * @return None if the constraints are unsat, and an assumption for each process otherwise.
    */
  def generateAssumptions(fixedAssumptions : mutable.Map[Int,LTL] = mutable.Map()) : Option[Buffer[LTL]] = {
    class UnsatAssumption extends Exception
    def findAssumptions() : Option[Buffer[LTL]] = {
      try {
        generateSamples(fixedAssumptions) match {
          case None => None // Constraints are unsatisfiable
          case Some(posSamples, negSamples) =>
            Some(Buffer.tabulate(proofSkeleton.nbProcesses)
              (i => 
                if fixedAssumptions.contains(i) then 
                  fixedAssumptions(i)
                else {
                  learners(i).setPositiveSamples(posSamples(i))
                  learners(i).setNegativeSamples(negSamples(i))
                  learners(i).getLTL() match {
                    case None => 
                      // There is no LTL formula for separating these samples
                      // Block the current assignment, and try again with another assignment
                      println(s"No solution for ${i}. Blocking assignment ${currentAssignment}")
                      blockCurrentAssignment()
                      throw UnsatAssumption()
                    case Some(ltl) => 
                      println(s"Samples2LTL generated formula ${ltl} for ${i}")
                      ltl
                  }
                }
              )
            )
        }
      } catch {
        case _ : UnsatAssumption => findAssumptions()
        case e => throw e
      }
    }
    findAssumptions()
  }
}
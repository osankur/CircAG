package fr.irisa.circag.ltl
import org.slf4j.Logger
import org.slf4j.LoggerFactory

import scala.collection.mutable.{HashMap,Buffer}
import scala.collection.mutable
import scala.collection.immutable.Set
import collection.JavaConverters._
import collection.convert.ImplicitConversions._
import scala.sys.process._
import scala.io
import java.nio.file.StandardCopyOption.REPLACE_EXISTING
import java.nio.file.Files.copy
import java.nio.file.Paths.get
import java.io.File
import java.io.InputStream
import java.nio.file._
import java.io.PrintWriter
import java.io.ByteArrayInputStream

import io.AnsiColor._

import net.automatalib.serialization.dot.GraphDOT

import net.automatalib.automata.fsa.impl.{FastDFA, FastNFA, FastDFAState, FastNFAState}

import de.learnlib.api.oracle.EquivalenceOracle
import de.learnlib.api.query.DefaultQuery;
import de.learnlib.api.oracle._
import de.learnlib.api.oracle.MembershipOracle
import de.learnlib.algorithms.rpni.BlueFringeRPNIDFA
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


import com.microsoft.z3

import fr.irisa.circag.statistics
import fr.irisa.circag.configuration
import fr.irisa.circag.{Trace, Lasso, DLTS, Alphabet}
import fr.irisa.circag.{pruned, filter, suffix, semanticEquals, size}

enum LTLLearningAlgorithm:
  case Samples2LTL, Scarlet

  /**
  * Passive learning of LTL formulas. If learning universal formulas of the form G(phi),
  * all samples constraint phi.
  *
  * @param name name of the DLTS to be learned
  * @param alphabet alphabet of the DLTS
  * @param universal whether a universal formula is to be learned.
  */
trait LTLLearner(name : String, alphabet : Alphabet, universal : Boolean) {
  def setPositiveSamples(samples : Set[Lasso]) = {
    if positiveSamples != samples then {
      positiveSamples = samples
      dlts = None
    }
  }
  def setNegativeSamples(samples : Set[Lasso]) = {
    if negativeSamples != samples then {
      negativeSamples = samples
      dlts = None
    }
  }
  def getLTL() : Option[LTL]
  protected var dlts : Option[LTL] = None
  protected var positiveSamples : Set[Lasso] = Set()
  protected var negativeSamples : Set[Lasso] = Set()
}

/**
* Interface to Iran Gavran's samples2LTL, and Ritam et al. Scarlet tools.
*
* @param name name of the DLTS to be learned
* @param alphabet alphabet of the DLTS
*/
class SATLearner(name : String, alphabet : Alphabet, universal : Boolean, solver : LTLLearningAlgorithm) 
  extends LTLLearner(name, alphabet, universal) {

  protected val logger = LoggerFactory.getLogger("CircAG")

  def learn() : Option[LTL] = {
    println(s"Entering learn(${solver}) (universal=${universal}) samples ${positiveSamples} and ${negativeSamples}")
    // Take care of the corner case not handled by samples2LTL
    if negativeSamples.isEmpty then
      if universal then return Some(G(LTLTrue()))
      else return Some(LTLTrue())
    else if positiveSamples.isEmpty then {
      if universal then return Some(G(LTLFalse()))
      else return Some(LTLFalse())
    }

    // Map each symbol of alphabet to 1,0,0; 0,1,0; 0,0,1 etc.
    val symbol2code = mutable.Map[String, String]()    
    // Backward substitution: x0 -> a, x1 -> b, x2 -> c etc
    val bwdSubst = mutable.Map[String, String]()
    val nAlphabet = alphabet.size
    for (symbol, i) <- alphabet.toList.zipWithIndex do {
      val prefix = List.tabulate(i)(_ => "0")
      val suffix = List.tabulate(nAlphabet-i-1)(_ => "0")      
      symbol2code.put(symbol, (prefix:::(1::suffix)).mkString(","))
      bwdSubst.put(s"x${i}", symbol)
    }

    def encodeLasso(lasso : Lasso) :String = {
      val (pref, cycle) = lasso
      s"${(pref++cycle).map(symbol2code.apply).mkString(";")}::${pref.size}"
    }
    val encPos = positiveSamples.map(encodeLasso)
    val encNeg = negativeSamples.map(encodeLasso)

    val inputFile =
      Files.createTempFile(configuration.get().getTmpDirPath(), "samples2LTL-query", ".trace").toFile()
    val pw = PrintWriter(inputFile)
    for samples <- encPos do {
      pw.write(samples)  
      pw.write("\n")
    }
    pw.write("---\n")
    for samples <- encNeg do {
      pw.write(samples)  
      pw.write("\n")
    }
    // pw.write("---\n")
    // pw.write("G,F,!,|,&\n")
    pw.close()

    solver match {
      case LTLLearningAlgorithm.Samples2LTL => 
        val cmd = s"python samples2ltl/samples2LTL.py --sat --traces ${inputFile.toString}"

        println(s"${BLUE}${cmd}${RESET}")
        logger.debug(cmd)

        val stdout = StringBuilder()
        val stderr = StringBuilder()
        val beginTime = System.nanoTime()
        val output =
          try{
          cmd !! ProcessLogger(stdout append _, stderr append _)
          } catch {        
            case e => 
              logger.error(s"Unexpected return value when executing: ${cmd}")
              throw e
          }
        statistics.Timers.incrementTimer("ltl-learner", System.nanoTime() - beginTime)
        
        if output.contains("NO SOLUTION") then
          logger.debug(s"Samples2LTL returned NO SOLUTION")
          None
        else {      
          val output_ = output.replaceAll("true","1").replaceAll("false","0")
          val ltl = LTL.fromString(output_)
          val substLtl = LTL.substitute(ltl, bwdSubst) match {
            case f if universal => G(f) 
            case f => f
          }      
          logger.debug(s"Samples2LTL returned ${substLtl}")
          Some(substLtl)
        }
      case LTLLearningAlgorithm.Scarlet =>        
        Files.copy(inputFile.toPath(), Paths.get("Scarlet/_input_.trace"), REPLACE_EXISTING)
        val cmd = s"python -m Scarlet.ltllearner --i _input_.trace --timeout 120 --verbose --outputcsv _output_.csv"
        val stdout = StringBuilder()
        val stderr = StringBuilder()
        val beginTime = System.nanoTime()
        val output =
          try{
          cmd !! ProcessLogger(stdout append _, stderr append _)
          } catch {        
            case e => 
              logger.error(s"Unexpected return value when executing: ${cmd}")
              throw e
          }
        statistics.Timers.incrementTimer("ltl-learner", System.nanoTime() - beginTime)
        
        val solutions = io.Source.fromFile("Scarlet/_output_.csv").getLines().toSeq.tail
        if solutions.isEmpty then {
          None
        } else {
          // Parse alphabet
          val alphabetString = 
            val l = stderr.toString().split("\n").filter(_.contains("Alphabet: "))
            if (l.size != 1) then throw Exception(s"Cannot parse alphabet from the following output of Scarlet:\n${stderr}")
            l.head
          val rAlphabet = ".*\\[(.*)\\].*".r
          val rLetter1 = "'(.*)'".r
          val rLetter2 = "\"(.*)\"".r
          val letters = 
            alphabetString match {
              case rAlphabet(letters) => 
                letters.split(",").map({
                    sigma =>  sigma.strip() match {
                      case rLetter1(a) => a
                      case rLetter2(a) => a
                      case _ => throw Exception(s"Cannot parse letter ${sigma} in the alphabet description ${alphabetString} of Scarlet")
                    }
                  })
              case _ => throw Exception(s"Could not parse alphabet from the following line: ${alphabetString}")
            }
          // println(s"Parsed alphabet: ${letters.toList}")
          // Parse solution
          val lastSolution = solutions.last
          // println(s"Last solution is: ${lastSolution}")
          val csvTerms = lastSolution.split(",")
          if (csvTerms.size < 3) then throw Exception(s"Output file Scarlet/_output_.csv does not contain a solution")
          val ltlFormula = LTL.fromString(csvTerms(2)) match {
            case f if universal => G(f)
            case f => f
          }
          // Double substitute p -> x0 -> bwdSubst(x0)
          val subst = HashMap[String,String]()
          letters
          .zipWithIndex
          .foreach({
            (p, i) => subst.put(p, bwdSubst(s"x${i}"))
          })
          // println(s"Substitution is ${subst}")
          Some(LTL.substitute(ltlFormula, subst))
        }
    }
  }

  override def getLTL() : Option[LTL] = {
    dlts match {
      case Some(dlts) => Some(dlts)
      case None => 
        dlts = learn()
        dlts
    }
  }
}


class LTLGenerator(proofSkeleton : AGProofSkeleton, ltlLearningAlgorithm : LTLLearningAlgorithm) {
  protected val z3ctx = {
    val cfg = HashMap[String, String]()
    cfg.put("model", "true")
    z3.Context(cfg);
  }

  protected val nbProcesses = proofSkeleton.nbProcesses
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
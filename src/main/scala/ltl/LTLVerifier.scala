package fr.irisa.circag.ltl

import scala.util.boundary, boundary.break
import org.slf4j.Logger
import org.slf4j.LoggerFactory
import io.AnsiColor._

import collection.JavaConverters._
import collection.convert.ImplicitConversions._
import collection.mutable.Buffer
import collection.mutable.HashMap
import scala.sys.process._
import scala.io
import java.io.ByteArrayInputStream
import java.nio.file._
import java.io.{File, PrintWriter}
import net.automatalib.automata.fsa.MutableDFA
import net.automatalib.automata.fsa.DFA;
import net.automatalib.automata.fsa.impl.compact.CompactDFA;
import net.automatalib.automata.fsa.impl.FastDFA
import net.automatalib.automata.fsa.impl.FastDFAState
import net.automatalib.util.automata.fsa.DFAs
import net.automatalib.util.automata.fsa.NFAs
import net.automatalib.automata.fsa.impl.compact.CompactDFA;
import net.automatalib.util.automata.builders.AutomatonBuilders;
import net.automatalib.words.impl.Alphabets;

import com.microsoft.z3

import fr.irisa.circag.statistics
import fr.irisa.circag.configuration
import fr.irisa.circag._

abstract class PremiseQuery(val processID : Int)
/**
  * @brief Content of the premise query
  *
  * @param _processID
  * @param noncircularDeps pairs of process id and assumption formulas
  * @param circularDeps pairs of process id and *matrices of* assumption formulas
  * @param instantaneousDeps pairs of process id and *matrices of* assumption formulas
  * @param mainAssumption the *matrix* of the assumption of processID
  * @param fairness the formula expressing the fairness constraint
  */
case class CircularPremiseQuery (
  _processID : Int,
  noncircularDeps : List[(Int, LTL)],
  circularDeps : List[(Int, LTL)],
  instantaneousDeps : List[(Int, LTL)],
  mainAssumption : LTL,
  fairness : LTL
  ) extends PremiseQuery(_processID)

/**
  * 
  *
  * @param _processID
  * @param noncircularDeps pairs of process id and assumption formulas
  * @param mainAssumption the assumption of processID
  * @param fairness the formula expressing the fairness constraint
  */
case class NonCircularPremiseQuery(
  _processID : Int,
  dependencies : List[(Int, LTL)],
  mainAssumption : LTL,
  fairness : LTL
) extends PremiseQuery(_processID)


enum LTLAGResult extends Exception:
  case Success // Assumptions and global property proven
  case GlobalPropertyProofFail(cex : Lasso) // Global property proof fails, but lasso not realizable
  case GlobalPropertyViolation(cex : Lasso) // Global property proof fails, and lasso realizable
  case PremiseFail(processID : Int, cex : Lasso, query : PremiseQuery) // Premise proof fails, but lasso not realizable
  case AssumptionViolation(processID : Int, cex : Lasso) // Premise proof fails, and lasso realizable

class LTLUnsatisfiableConstraints extends Exception

class LTLVerifier(ltsFiles: Array[File], val property: LTL) {
  protected val logger = LoggerFactory.getLogger("CircAG")

  val nbProcesses = ltsFiles.size
  val propertyAlphabet = property.getAlphabet
  protected val processes = ltsFiles.map(TA.fromFile(_)).toBuffer
  val proofSkeleton = AGProofSkeleton(processes, property)

  // Initial assumptions: True or G(True) for circular processes
  protected var assumptions : Buffer[LTL] = Buffer.tabulate(nbProcesses){
    i => if proofSkeleton.isCircular(i) then G(LTLTrue())
         else LTLTrue()
  }
  logger.debug(s"Circularity of the assumptions: ${(0 until nbProcesses).map(proofSkeleton.isCircular(_))}")

  def setAssumption(processID : Int, formula: LTL) : Unit = {
    assumptions(processID) = formula
  }
  def getAssumption(processID : Int) : Unit = {
    assumptions(processID)
  }

  
  /**
    * Check the inductive premise for process processID:
    * - If processID is circular in the proof skeleton, then we require assumptions(processID)
    * to be universal (i.e. G _ ). This creates a circular premise query
    * according to McMillan's method: 
    *  
    *   /\\_{d in non-circular-deps} psi_d /\\ (( /\\_{d in circular-deps} phi_d' ) U ( ~phi /\\_{d in inst-deps} phi_{d}' )) /\\ fairness
    * 
    * where non-circular-deps are dependencies which are not circular. circular-deps are dependencies which are circular processes.
    * In this case, the assumption is phi_d = G(phi_d'). inst-deps are dependencies that are circular and instantaneous.
    * 
    * Last, fairness is a formula ensuring that all processes make infinite numbers of steps, namely, 
    * 
    *   fairness = /\\_{i} GF alpha_i
    *
    * where alpha_i is the alphabet of assumption i. 
    * 
    * - If processID is not circular, then this creates a noncircular premise query which encodes the following check:
    *
    *   /\\_{d in dependencies} psi_d /\ ~phi /\ fairness
    * 
    * 
    * @param processID id of the process for which the premise is to be checked
    * @param fairness whether fairness constraint is to be added to the cex check
    * @return a premise query object
    */
  protected def makePremiseQuery(processID : Int, fairness : Boolean = true) : PremiseQuery = {
    // Fairness: /\\_{i} GF alpha_i for each process i, and its alphabet alpha_i
    val fairnessConstraint =
      if fairness then {
        And(
            (0 until processes.size).map({
            i =>
              G(F(Or(proofSkeleton.assumptionAlphabet(i).toList.map(Atomic(_)))))
            })
            .toList
          )
      } else LTLTrue()
    // System.out.println(s"Fairness constraint: ${fairnessConstraint}")
    val guarantee = assumptions(processID)
    val dependencies = proofSkeleton.processDependencies(processID)
    if proofSkeleton.isCircular(processID) then {
      val guarantee_matrix = guarantee match {
        case G(matrix) => 
          LTL.asynchronousTransform(matrix, proofSkeleton.assumptionAlphabet(processID))
        case _ => throw Exception(s"Guarantee formula for circular process ${processID} must be universal: ${guarantee}")
      }
      println(s"Checking inductive premise for ${processID}")
      println(s"Guarantee matrix: ${guarantee_matrix}")
      
      // Check for CEX with an LTL formula of the form: /\_i noncircular-assumptions(i) /\ (/\_i circular-assumptions(i) U !guarantee)
      def getAsynchronousMatrix(i : Int) : LTL = {
          assumptions(i) match {
            case G(subf) => 
              val x = LTL.asynchronousTransform(subf, proofSkeleton.assumptionAlphabet(i))
              // System.out.println(s"Transformed subf: ${x}")
              x
            case _ =>
              throw Exception(
                s"Non-universal dependency for circular assumption ${processID}"
              )
          }
      }
      val circularDeps = 
        dependencies.filter(proofSkeleton.isCircular).toList
        .map(i => (i,getAsynchronousMatrix(i)))
      println(s"Assumption matrices: ${circularDeps}")

      val noncircularDeps =
          dependencies.filterNot(proofSkeleton.isCircular)
          .map({i => (i,LTL.asynchronousTransform(assumptions(i), proofSkeleton.assumptionAlphabet(i)))})
          .toList

      val instantaneousDeps = 
            proofSkeleton
            .processInstantaneousDependencies(processID).toList
            .map(i => (i,getAsynchronousMatrix(i)))
      CircularPremiseQuery(processID, noncircularDeps, circularDeps, instantaneousDeps, guarantee_matrix, fairnessConstraint)
    } else {
      // Check for CEX of the form: /\_i assumptions(i) /\ !guarantee
      val noncircularDeps =
          dependencies
          .toList
          .map({i => (i,LTL.asynchronousTransform(assumptions(i), proofSkeleton.assumptionAlphabet(i)))})
      NonCircularPremiseQuery(processID, noncircularDeps, (assumptions(processID)), fairnessConstraint)
    }
  }

  def checkInductivePremise(premise : PremiseQuery) : Option[Lasso] = {
    def andOfList(f : List[LTL]) : LTL = {
      f match{
        case List() => LTLTrue()
        case fl => And(fl.map(And(_)))
      }
    }
    println(s"Checking premise ${premise}")
    val f = premise match {
      case CircularPremiseQuery(processID, noncircularDeps, circularDeps, instantaneousDeps, mainAssumption, fairness) => 
        val noncircularLHS = andOfList(noncircularDeps.map(_._2))
        val circularLHS = andOfList(circularDeps.map(_._2))
        val instantaneousRHS = andOfList(instantaneousDeps.map(_._2))
        And( fairness, noncircularLHS, U(circularLHS, And(instantaneousRHS, Not(mainAssumption))))
      case NonCircularPremiseQuery(processID, deps, mainAssumption, fairness) => 
        val noncircularLHS = andOfList(deps.map(_._2))
        And( fairness, noncircularLHS, Not(mainAssumption))
    }
    processes(premise.processID).checkLTL(Not(f))
  }

  /**
    * @brief Given a circular premise query failed by lasso rho, find least k0 such that
    * forall 1<=k<=k0, lasso, k |= circular-deps 
    * lasso, k0 = instant-deps & ~main-assumption"
    *
    * @param lasso the cex lasso that fails the premise query
    * @param query the failed circular premise query 
    * @return
    */
  def getPremiseViolationIndex(lasso : Lasso, query : CircularPremiseQuery) : Int = {
    query match {
      case CircularPremiseQuery(_processID, noncircularDeps, circularDeps, instantaneousDeps, mainAssumption, fairness) => 
        val processAlphabet = processes(_processID).alphabet 
        val rhs = And(Not(mainAssumption) :: instantaneousDeps.map(_._2))
        val formulaAlphabet = rhs.getAlphabet
        val (p,c) = lasso
        val pc = p ++ c
        val k0 = boundary:
          for i <- 0 to pc.size do {
            val newp = pc.drop(i)
            // We make sure that the lasso and the LTL formula synchronizes every single letter
            // by setting the alphabet of the lasso to its own letters + processAlphabet + letter appearing in the formula
            val alpha = newp.toSet ++ c.toSet ++ processAlphabet ++ formulaAlphabet
            println(s"alphabet for lasso is ${alpha}")
            val dlts = DLTS.fromLasso((newp, c), alphabet = Some(alpha))
            // add symbols of the process being checked in the premise query to the alphabet of the lasso
            val lassoTA = TA.fromLTS(dlts)
            if lassoTA.checkLTL(rhs) == None then 
              break(i)
          }
          throw Exception(s"Failed to find the violation index of lasso ${lasso} and query ${query}")        
        return k0
    }
  }

  def checkInductivePremise(processID : Int, fairness : Boolean = true) : Option[Lasso] = {
    checkInductivePremise(makePremiseQuery(processID, fairness))
  }

  def checkFinalPremise(
      fairness : Boolean = true
  ) : Option[Lasso] = {
    val fairnessConstraint =
      if fairness then {
        And(
          (0 until processes.size).map({
          i =>
            G(F(proofSkeleton.assumptionAlphabet(i).foldLeft(LTLFalse() : LTL)({ (f, sigma) => Or(List(f, Atomic(sigma)))})))
          }).toList
        )
      } else {
        LTLTrue()
      }
    val assFormulas = 
      And(
        fairnessConstraint::
          (assumptions
          .zipWithIndex
          .map({(f,i) => LTL.asynchronousTransform(f, proofSkeleton.assumptionAlphabet(i))})
          ).toList
      )
    // val cexFormula = And(List(assFormulas, LTL.asynchronousTransform(Not(property), property.alphabet)))
    val cexFormula = And(List(assFormulas, Not(property)))
    System.out.println(cexFormula)
    val ta = TA.fromLTL(cexFormula.toString, None, Some("_ltl_acc_"))
    ta.checkBuchi(s"${ta.systemName}_ltl_acc_")
  }

  /**
    * Check if all processes accept (the projection of) the lasso (to their own alphabet)
    *
    * @param lasso
    * @return whether lasso is accepted by all processes
    */
  def checkCounterExample(lasso : Lasso): Boolean = {
    class Break extends Exception
    try {
      for (ta, i) <- processes.zipWithIndex do {
        // val projLasso = lasso.filter(x => assumptions(i).getAlphabet.contains(x))
        println(s"Checking if ${lasso} is accepted by process ${i} (${ta.systemName})")
        ta.checkLassoMembership(lasso, Some(ta.alphabet)) match {
          case None => // ta rejects
            println("No")
            throw Break()
          case _ => // ta accepts
            println("Yes")
            ()
        }
      }
      true
    } catch {
      case _: Break => false
    }
  }
  

  def applyAG(proveGlobalproperty : Boolean = true, fairness : Boolean = true): LTLAGResult = {
    try { 
      for i <- 0 until proofSkeleton.nbProcesses do {
        val query = makePremiseQuery(i, fairness)
        checkInductivePremise(query) match {
          case None =>
            println(s"${GREEN}Check passes${RESET}")
            ()
          case Some(lasso) => 
            println(s"${RED}Check fails with lasso: ${lasso}${RESET}")
            if checkCounterExample(lasso) then {
              throw LTLAGResult.AssumptionViolation(i, lasso)
            } else 
              throw LTLAGResult.PremiseFail(i, lasso, query)
        }
      }
      if proveGlobalproperty then {
        checkFinalPremise(fairness) match {
          case None =>
            println(s"${GREEN}Final premise passes${RESET}")
            ()
          case Some(lasso) => 
            println(s"${RED}Final premise fails with ${lasso}${RESET}")
            if checkCounterExample(lasso) then {
              throw LTLAGResult.GlobalPropertyViolation(lasso)
            } else {
              throw LTLAGResult.GlobalPropertyProofFail(lasso)
            }
        }
      }
      LTLAGResult.Success
    } catch {
      case e : LTLAGResult =>
        e
    }
  }
}


class AutomaticLTLVerifier(_ltsFiles: Array[File], _property: LTL, ltlLearningAlgorithm : LTLLearningAlgorithm = LTLLearningAlgorithm.Samples2LTL)
  extends LTLVerifier(_ltsFiles, _property){
  private val ltlGenerator = LTLGenerator(proofSkeleton, ltlLearningAlgorithm)

  /**
    * @brief Prove or disprove the fixed assumptions and the global property by learning nonfixed assumptions
    * 
    * @param proveGlobalProperty whether the given global property is to be checked
    * @param fixedAssumptions list of process ids for which the assumptions are fixed; these will not be learned
    * @return
    */
  def learnAssumptions(proveGlobalProperty : Boolean = true, fixedAssumptions : List[Int] = List()): LTLAGResult = {
    var count = 0
    val fixedAssumptionsMap = HashMap[Int, LTL]()
    fixedAssumptions.foreach(i => 
      fixedAssumptionsMap.put(i, assumptions(i))      
    )
    var doneVerification = false
    var currentState = LTLAGResult.Success
    while (!doneVerification && count < 20) {
      count += 1
      ltlGenerator.generateAssumptions(fixedAssumptionsMap) match {
        case Some(newAss) => this.assumptions = newAss
        case None         => 
          println(s"${RED}Unsat${RESET}")
          throw LTLUnsatisfiableConstraints()
      }
      println(s"${MAGENTA}Assumptions at attempt #${count}: ${assumptions}${RESET}")
      currentState = this.applyAG(proveGlobalProperty) 
      currentState match {
        case LTLAGResult.Success => 
          println("Success")
          doneVerification = true
        case LTLAGResult.AssumptionViolation(processID, cex) => 
          println(s"AssumptionViolation ${processID} ${cex}")
          doneVerification = fixedAssumptions.contains(processID)
        case LTLAGResult.GlobalPropertyViolation(cex) => 
          println(s"Gobalproperty violation ${cex}")
          doneVerification = true
        case LTLAGResult.PremiseFail(processID, cex, query) => 
          println(s"PremiseFail ${processID} ${cex}")
          query match {
            case q : NonCircularPremiseQuery => 
              ltlGenerator.refineConstraintsByPremiseQuery(cex, q, 0)
            case q : CircularPremiseQuery => 
              val k0 = getPremiseViolationIndex(cex, q)
              ltlGenerator.refineConstraintsByPremiseQuery(cex, q, k0)
          }
          // ltlGenerator.refineConstraintsByPremiseQuery(cex, query)
        case LTLAGResult.GlobalPropertyProofFail(cex) => 
          println(s"Global Proof fail ${cex}")
          ltlGenerator.refineConstraintsByFinal(cex)
      }
    }
    currentState
  }

}

package fr.irisa.circag.ltl

import org.slf4j.Logger
import org.slf4j.LoggerFactory

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

enum LTLAGResult extends Exception:
  case Success // Assumptions and global property proven
  case GlobalPropertyProofFail(cex : Lasso) // Global property proof fails, but lasso not realizable
  case GlobalPropertyViolation(cex : Lasso) // Global property proof fails, and lasso realizable
  case PremiseFail(processID : Int, cex : Lasso) // Premise proof fails, but lasso not realizable
  case AssumptionViolation(processID : Int, cex : Lasso) // Premise proof fails, and lasso realizable

class LTLUnsatisfiableConstraints extends Exception


/** LTL syntax: each event is an atomic predicate. Produce LTL formula from the
  * premise checker Use Spot to get HOA Buchi automaton, and read it back with
  * HOAParser
  *   - The automaton labels are Boolean expressions
  *   - infeasible valuations such as "a & b" appear in transitions; that's OK
  *   - Make sure acceptance condition in on states (state-acc), and it is Buchi
  *     (not gen Buchi)
  *   - Make sure there are no implicit labels 
  *   - Translate this to a TChecker
  *     automaton by using Z3 to explicitly enumerate all valuations in which a
  *     single event is true
  *   - Discard other transitions Make the product with the process TA by
  *     synchronizing on common events Use tck-liveness to model check
  */

class LTLVerifier(ltsFiles: Array[File], val property: LTL) {
  protected val logger = LoggerFactory.getLogger("CircAG")

  val nbProcesses = ltsFiles.size
  val propertyAlphabet = property.alphabet
  protected val processes = ltsFiles.map(TA.fromFile(_)).toBuffer
  protected var assumptions : Buffer[LTL] = Buffer.fill(nbProcesses)(LTLTrue())

  val proofSkeleton = AGProofSkeleton(processes, property)
  logger.debug(s"Circularity of the assumptions: ${(0 until nbProcesses).map(proofSkeleton.isCircular(_))}")

  protected abstract class PremiseQuery(val processID : Int)
  /**
    * @brief Content of the premise query
    *
    * @param _processID
    * @param noncircularDeps
    * @param circularDeps
    * @param instantaneousDeps
    * @param mainAssumption
    * @param fairness
    */
  protected case class CircularPremiseQuery (
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
    * @param noncircularDeps
    * @param mainAssumption
    * @param fairness
    */
  protected case class NonCircularPremiseQuery(
    _processID : Int,
    noncircularDeps : List[(Int, LTL)],
    mainAssumption : LTL,
    fairness : LTL
  ) extends PremiseQuery(_processID)

  def setAssumption(processID : Int, formula: LTL) : Unit = {
    assumptions(processID) = formula
  }
  def getAssumption(processID : Int) : Unit = {
    assumptions(processID)
  }

  
  /**
    * Check the inductive premise for process processID:
    * If processID is circular in the proof skeleton, then we require assumptions(processID)
    * as well as all dependency formulas to be universal (i.e. G _ ). We check for a counterexample for the premise
    * according to McMillan's method: 
    *  
    *  /\\_{d} psi_d /\\ (( /\\_{d} phi_d ) U ( ~phi /\\_{d'} phi_{d'} )) /\\ fairness
    * 
    * where the G(phi_d) are the set of all dependencies of processID, transformed for the asynchronous composition,
    * and the G(phi_{d'}) are the subset of those dependencies that are instantaneous.
    * fairness is a formula ensuring that all processes make infinite numbers of steps, namely, 
    * 
    * fairness = /\\_{i} GF alpha_i
    *
    * where alpha_i is the alphabet of assumption i. 
    * The leftmost formulas psi_d are noncircular dependencies.
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
        ta.checkLassoMembership(lasso.filter(x => assumptions(i).alphabet.contains(x)), Some(ta.alphabet)) match {
          case None => // ta rejects
            throw Break()
          case _ => // ta accepts
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
        checkInductivePremise(i,fairness) match {
          case None => ()
          case Some(lasso) => 
            if checkCounterExample(lasso) then {
              throw LTLAGResult.AssumptionViolation(i, lasso)
            } else 
              throw LTLAGResult.PremiseFail(i, lasso)
        }
      }
      if proveGlobalproperty then {
        checkFinalPremise(fairness) match {
          case None => ()
          case Some(lasso) => 
            if checkCounterExample(lasso) then {
              throw LTLAGResult.GlobalPropertyViolation(lasso)
            } else {
              throw LTLAGResult.GlobalPropertyProofFail(lasso)
            }
        }
      }
    } catch {
      case e : LTLAGResult => e
    }
    LTLAGResult.Success
  }
}


class AutomaticLTLVerifier(_ltsFiles: Array[File], _property: LTL) extends LTLVerifier(_ltsFiles, _property){
  private val ltlGenerator = LTLGenerator(proofSkeleton)
  override def applyAG(proveGlobalproperty : Boolean = true, fairness : Boolean = true): LTLAGResult = {
    LTLAGResult.Success
    // TODO make a version where constraints are updated
  }

/**
    * Apply automatic AG; retrun None on succes, and a confirmed cex otherwise.
    *
    * @param proveGlobalProperty
    * @param fixedAssumptions
    * @return
    */
  def learnAssumptions(proveGlobalProperty : Boolean = true, fixedAssumptions : List[Int] = List()): LTLAGResult = {
    val fixedAssumptionsMap = HashMap[Int, LTL]()
    fixedAssumptions.foreach(i => 
      fixedAssumptionsMap.put(i, assumptions(i))      
    )
    var doneVerification = false
    var currentState = LTLAGResult.Success
    while (!doneVerification) {
      ltlGenerator.generateAssumptions(fixedAssumptionsMap) match {
        case Some(newAss) => this.assumptions = newAss
        case None         => throw LTLUnsatisfiableConstraints()
      }
      currentState = this.applyAG(proveGlobalProperty) 
      currentState match {
        case LTLAGResult.Success => doneVerification = true
        case LTLAGResult.AssumptionViolation(processID, cex) => doneVerification = fixedAssumptions.contains(processID)
        case LTLAGResult.GlobalPropertyViolation(cex) => doneVerification = true
        case LTLAGResult.PremiseFail(processID, cex) => ()
        case LTLAGResult.GlobalPropertyProofFail(cex) => ()
      }
    }
    currentState
  }

}

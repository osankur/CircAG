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
  private val logger = LoggerFactory.getLogger("CircAG")

  val nbProcesses = ltsFiles.size
  val propertyAlphabet = property.alphabet
  private val processes = ltsFiles.map(TA.fromFile(_)).toBuffer
  private val assumptions : Buffer[LTL] = Buffer.fill(nbProcesses)(LTLTrue())

  val proofSkeleton = AGProofSkeleton(processes, property)
  logger.debug(s"Circularity of the assumptions: ${(0 until nbProcesses).map(proofSkeleton.isCircular(_))}")

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
    *  ( /\\_{d} phi_d ) U ( ~phi /\\_{d'} phi_{d'} ) /\\ fairness
    * 
    * where the G(phi_d) are the set of all dependencies of processID, transformed for the asynchronous composition,
    * and the G(phi_{d'}) are the subset of those dependencies that are instantaneous.
    * fairness is a formula ensuring that all processes make infinite numbers of steps, namely, 
    * 
    * fairness = /\\_{i} GF alpha_i
    *
    * where alpha_i is the alphabet of assumption i. 
    * 
    * @param processID id of the process for which the premise is to be checked
    * @param fairness whether fairness constraint is to be added to the cex check
    * @return
    */
  def checkInductivePremise(
      processID: Int,
      fairness : Boolean = true
  ): Option[Lasso] = {
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
      } else {
        LTLTrue()
      }
    // System.out.println(s"Fairness constraint: ${fairnessConstraint}")
    val guarantee = assumptions(processID)
    val dependencies = proofSkeleton.processDependencies(processID)
    if proofSkeleton.isCircular(processID) then {
      val guarantee_matrix = guarantee match {
        case G(matrix) => 
          LTL.asynchronousTransform(matrix, proofSkeleton.assumptionAlphabet(processID))
        case _ => throw Exception(s"Guarantee formula for circular process ${processID} must be universal: ${guarantee}")
      }
      System.out.println(s"Guarantee matrix: ${guarantee_matrix}")
      val circularDeps = dependencies.filter(proofSkeleton.isCircular)
      val noncircularDeps = dependencies.filterNot(proofSkeleton.isCircular)
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
      val assumptionMatrices = 
        circularDeps
        .toSeq
        .map(getAsynchronousMatrix)
      System.out.println(s"Assumption matrices: ${assumptionMatrices}")

      val circularLHS = 
        if assumptionMatrices.size == 0 then LTLTrue()
        else And(assumptionMatrices.toList)
        // else assumptionMatrices.tail.fold(assumptionMatrices.head)({ (a,b) => And(a,b)})
      val noncircularLHS =
        val formulas = 
          noncircularDeps
          .map({i => LTL.asynchronousTransform(assumptions(i), proofSkeleton.assumptionAlphabet(i))})
          .toList
        if formulas.size == 0 then LTLTrue()
        else And(formulas) //formulas.tail.fold(formulas.head)({ (a,b) => And(a,b)})
      val rhs = 
        if proofSkeleton.processInstantaneousDependencies(processID).isEmpty then 
          Not(guarantee_matrix)
        else {          
          val matrices = 
            proofSkeleton
            .processInstantaneousDependencies(processID)
            .map(getAsynchronousMatrix)
          System.out.println(s"RHS w/out guarantee: ${matrices}")
          And(Not(guarantee_matrix) :: matrices.toList)
        }
      // System.out.println(s"guarantee_matrix:\n${guarantee_matrix}")
      val f = noncircularLHS match {
        case LTLTrue() => 
          And(List(U(circularLHS, rhs), fairnessConstraint))
        case _ => 
          And(List(noncircularLHS,U(circularLHS, rhs), fairnessConstraint))
      }
      // System.out.println(s"LHS:\n${circularLHS}")
      // System.out.println(s"RHS:\n${rhs}")
      System.out.println(s"Checking circular inductive premise for process ${processID}: ${f} ")
      processes(processID).checkLTL(Not(f))
    } else {
      // Check for CEX of the form: /\_i assumptions(i) /\ !guarantee
      val noncircularLHS =
        val formulas = 
          dependencies
          .toSeq
          .map({i => LTL.asynchronousTransform(assumptions(i), proofSkeleton.assumptionAlphabet(i))})
        if formulas.size == 0 then LTLTrue()
        else And(formulas.toList)
      val f = And(List(noncircularLHS,Not(guarantee), fairnessConstraint))
      System.out.println(s"Checking non-circular inductive permise for process ${processID}: ${f} ")
      processes(processID).checkLTL(Not(f))
    }
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
}

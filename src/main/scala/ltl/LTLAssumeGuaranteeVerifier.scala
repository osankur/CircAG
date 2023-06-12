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

/**
 * Malformed proof skeleton, for instance, when instantaneous dependencies are circular.
 */
class BadProofSkeleton(msg : String) extends Exception(msg)

/** Proof skeleton that stores the dependencies of the proof of the assumption
  * of each process, the alphabets of these assumptions and that of the
  * property, and whether each assumption's proof is circular.
  *
  * The skeleton can be used with the default policy: in this case, given assumption and property
  * alphabets, process i depends on all processes j whose alphabets share a symbol,
  * and on all processes j depends on (recursively). This excludes i in the dependencies of i.
  * Alternatively, one can define manually all the dependencies.
  * In all cases, the circularity information is kept up to date automatically.
  * The instantaneous assumptions must be added manually.
  *
  * @param nbProcesses
  *   Number of processes
  */
class AGProofSkeleton(val nbProcesses: Int) {
  private val logger = LoggerFactory.getLogger("CircAG")

  /** For each process, the set of process indices on which the proof inductively depends
    */
  private var _processDependencies =
    Buffer.tabulate(nbProcesses)(_ => (0 to nbProcesses).toSet)

  /** For each process, the set of process indices on which the proof depends both inductively and instantaneously: this relation must be acyclic
   * Furthermore, we maintain the invariant _processInstantaneousDependencies(i) is a subset of _processDependencies
    */
  private var _processInstantaneousDependencies =
    Buffer.tabulate(nbProcesses)(_ => Set[Int]())

  /** The set of process indices on which the proof of the property depends
    */
  private var _propertyDependencies = (0 to nbProcesses).toSet

  /** Alphabet of the property
    */
  private var _propertyAlphabet: Alphabet = Set[String]()

  /** For each process, the alphabet of the assumption
    */
  private var _assumptionAlphabets =
    Buffer.tabulate(nbProcesses)(_ => Set[String]())

  /** Whether the proof of given process is circular
    */
  private var _isCircular = Buffer.tabulate(nbProcesses)(_ => false)

  def processInstantaneousDependencies(i: Int) = _processInstantaneousDependencies(i)
  def processDependencies(i: Int) = _processDependencies(i)
  def assumptionAlphabet(i: Int) = _assumptionAlphabets(i)
  def isCircular(i: Int) = _isCircular(i)
  def propertyDependencies = _propertyDependencies
  def propertyAlphabet = _propertyAlphabet

  def setProcessDependencies(i: Int, deps: Set[Int]) =
    _processDependencies(i) = deps
    updateCircularity()

  def setProcessInstantaneousDependencies(i: Int, deps: Set[Int]) =
    _processInstantaneousDependencies(i) = deps
    _processDependencies(i) |= deps
    updateCircularity()

  def setPropertyDependencies(deps: Set[Int]) =
    _propertyDependencies = deps

  def setAssumptionAlphabet(i: Int, alphabet: Alphabet) =
    _assumptionAlphabets(i) = alphabet

  def setPropertyAlphabet(alphabet: Alphabet) =
    _propertyAlphabet = alphabet

  /**
    * Initialize all process dependencies according to the default policy (@see updateByCone)
    *
    * @param assumptionAlphabets
    * @param propertyAlphabet
    */
  def this(
      assumptionAlphabets: Buffer[Alphabet],
      propertyAlphabet: Set[String]
  ) = {
    this(assumptionAlphabets.size)
    updateByCone(assumptionAlphabets, propertyAlphabet)
  }
  /**
    * Compute interface alphabet which is the set of symbols that appear in the property or at least in two different processes;
    * restrict each assumption to the interface alphabet intersected with the process' alphabet; and apply the defualt policy (@see updateByCone)
    *
    * @param processes
    * @param property
    */
  def this( processes: Buffer[TA], property : LTL ) = {
    this(processes.size)
    val propertyAlphabet = property.alphabet
    updateByCone(processes.map(_.alphabet), propertyAlphabet)
  }


  /** Update the proof skeleton from the given assumption and property alphabets.
    * Process dependencies are updated so as to include exactly all processes with which the
    * assumptions share a common symbol, or recursively, there is a third
    * process whose assumption shares a common symbol with each etc. Circularity
    * information is updated. Empties instantaneous dependencies.
    *
    * @param assumptionAlphabets
    *   alphabets of the processes
    * @param propertyAlphabet
    *   alphabet of the property
    */
  def updateByCone(
      assumptionAlphabets: Buffer[Alphabet],
      propertyAlphabet: Alphabet
  ) = {
    require(nbProcesses == assumptionAlphabets.size)
    _assumptionAlphabets = assumptionAlphabets
    _propertyAlphabet = propertyAlphabet
    generateConeDependencies()
    _processInstantaneousDependencies =
      Buffer.tabulate(nbProcesses)(_ => Set[Int]())    
    logger.debug(s"Ass alphabets: $_assumptionAlphabets")
    logger.debug(s"Prop dependencies: $_propertyDependencies")
    logger.debug(s"Process deps: $_processDependencies")
    logger.debug(s"Process instantaneous deps: $_processInstantaneousDependencies")
    logger.debug(s"Circularity: $_isCircular")
  }

  /** Update process and property dependencies so that any pair of processes
    * whose assumptions share a common symbol are in the dependencies of each
    * other, and recursively, if they share a common symbol with a third process
    * etc.
    */
  private def generateConeDependencies(): Unit = {
    val nbProcesses = _processDependencies.size
    _processDependencies = Buffer.tabulate(nbProcesses)({ _ => Set[Int]() })
    // Compute simplified sets of assumptions for the new alphabet
    // adj(i)(j) iff (i = j) or (i and j have a common symbol) or (i has a common symbol with k such that adj(k)(j))
    // Index nbProcesses represents the property.
    var adj = Buffer.tabulate(nbProcesses + 1)({ _ =>
      Buffer.fill(nbProcesses + 1)(false)
    })
    for i <- 0 until nbProcesses do {
      adj(i)(i) = true
      for j <- 0 until i do {
        adj(i)(j) =
          !_assumptionAlphabets(i).intersect(_assumptionAlphabets(j)).isEmpty
        adj(j)(i) = adj(i)(j)
      }
    }
    adj(nbProcesses)(nbProcesses) = true
    for j <- 0 until nbProcesses do {
      adj(nbProcesses)(j) =
        !_propertyAlphabet.intersect(_assumptionAlphabets(j)).isEmpty
      adj(j)(nbProcesses) = adj(nbProcesses)(j)
    }
    for k <- 0 until nbProcesses + 1 do {
      for i <- 0 until nbProcesses + 1 do {
        for j <- 0 until nbProcesses + 1 do {
          if (adj(i)(k) && adj(k)(j)) then {
            adj(i)(j) = true
          }
        }
      }
    }
    for i <- 0 until nbProcesses do {
      _processDependencies(i) = adj(i).zipWithIndex
        .filter({ (b, i) => b })
        .map(_._2)
        .toSet
        .diff(Set[Int](i, nbProcesses))
    }
    _propertyDependencies = adj(nbProcesses).zipWithIndex
      .filter({ (b, i) => b })
      .map(_._2)
      .toSet - nbProcesses
    updateCircularity()
  }

  private def updateCircularity(): Unit = {
    def isOnACycle(deps : Buffer[Set[Int]], pr: Int): Boolean = {
      val visited = Buffer.tabulate(nbProcesses)(_ => false)
      def visit(i: Int): Boolean = {
        if !visited(i) then {
          visited(i) = true
          deps(i).exists(visit(_))
        } else if i == pr then true
        else false
      }
      visit(pr)
    }
    _isCircular = Buffer.tabulate(nbProcesses)(isOnACycle(_processDependencies,_))
    val circularInstDeps = 
      Buffer.tabulate(nbProcesses)(isOnACycle(_processInstantaneousDependencies,_))
      .zipWithIndex
      .filter( (b,i) => b )
      .map(_._2)
    if (circularInstDeps.size > 0 ) then {
      throw BadProofSkeleton(s"The following instantaneous dependencies are on a cycle: ${circularInstDeps}")
    }

  }
}

class LTLAssumeGuaranteeVerifier(ltsFiles: Array[File], val property: LTL) {
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
          val matrices = proofSkeleton.processInstantaneousDependencies(processID).map(getAsynchronousMatrix)
          And(Not(guarantee_matrix) :: matrices.toList)
        }
      // System.out.println(s"guarantee_matrix:\n${guarantee_matrix}")
      val f = noncircularLHS match {
        case _ : LTLTrue => 
          And(List(U(circularLHS, rhs), fairnessConstraint))
        case _ => 
          And(List(noncircularLHS,U(circularLHS, rhs), fairnessConstraint))
      }
      // System.out.println(s"LHS:\n${circularLHS}")
      // System.out.println(s"RHS:\n${rhs}")
      System.out.println(s"Checking circular inductive premise for process ${processID}: ${f} ")
      processes(processID).checkLTL(f)
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
      processes(processID).checkLTL(f)
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

package fr.irisa.circag.tchecker.ltl

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
import net.automatalib.visualization.Visualization;
import net.automatalib.words.impl.Alphabets;

import com.microsoft.z3

import fr.irisa.circag.statistics
import fr.irisa.circag.configuration
import fr.irisa.circag._
import fr.irisa.circag.tchecker.{TA, FailedTAModelChecking}

/** LTL syntax: each event is an atomic predicate. Produce LTL formula from the
  * premise checker Use Spot to get HOA Buchi automaton, and read it back with
  * HOAParser
  *   - The automaton labels are Boolean expressions
  *   - infeasible valuations such as "a & b" appear in transitions; that's OK
  *   - Make sure acceptance condition in on states (state-acc), and it is Buchi
  *     (not gen Buchi)
  *   - Make sure there are no implicit labels Translate this to a TChecker
  *     automaton by using Z3 to explicitly enumerate all valuations in which a
  *     single event is true
  *   - Discard other transitions Make the product with the process TA by
  *     synchronizing on common events Use tck-liveness to model check
  */

// class LTLFormula(ltlString: String){
//   override def toString: String = ltlString
// }

// case class UniversalLTLFormula(matrix: String) extends LTLFormula(s"G(${matrix})") {
//   override def toString: String = super.toString
// }


/** Proof skeleton that stores the dependencies of the proof of the assumption
  * of each process, the alphabets of these assumptions and that of the
  * property, and whether each assumption's proof is circular.
  *
  * The skeleton can either be used in default mode using the update function:
  * in this case, a common assumption alphabet is specified and this will update
  * the skeleton to add dependencies between all pairs of processes that share a
  * common symbol or with a thid process. Alternatively, one can set manually
  * all these fields. In all cases, the circularity information is kept up to
  * date automatically.
  *
  * @param nbProcesses
  *   Number of processes
  */
class AGProofSkeleton(nbProcesses: Int) {
  private val logger = LoggerFactory.getLogger("AGProofSkeleton")

  /** For each process, the set of process indices on which the proof depends
    */
  private var _processDependencies =
    Buffer.tabulate(nbProcesses)(_ => Set[Int]())

  /** The set of process indices on which the proof of the property depends
    */
  private var _propertyDependencies = Set[Int]()

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

  def processDependencies(i: Int) = _processDependencies(i)
  def assumptionAlphabet(i: Int) = _assumptionAlphabets(i)
  def isCircular(i: Int) = _isCircular(i)
  def propertyDependencies = _propertyDependencies

  def setProcessDependencies(i: Int, deps: Set[Int]) =
    _processDependencies(i) = deps
    updateCircularity()

  def setPropertyDependencies(deps: Set[Int]) =
    _propertyDependencies = deps

  def setAssumptionAlphabet(i: Int, alphabet: Alphabet) =
    _assumptionAlphabets(i) = alphabet

  def setPropertyAlphabet(alphabet: Alphabet) =
    _propertyAlphabet = alphabet

  def this(
      assumptionAlphabets: Buffer[Alphabet],
      propertyAlphabet: Set[String]
  ) = {
    this(assumptionAlphabets.size)
    updateDefault(assumptionAlphabets, propertyAlphabet)
  }

  /** Update the proof skeleton from the given common assumption alphabet: the
    * alphabet of the assumption of each process becomes the intersection of the
    * propertyAlphabet with the process alphabet. Moreover, process dependencies
    * are updated so as to include exactly all processes with which the
    * assumptions share a common aymbol, or recursively, there is a third
    * process whose assumption shares a common symbol with each etc. Circularity
    * information is updated.
    *
    * @param assumptionAlphabets
    *   alphabets of the processes
    * @param propertyAlphabet
    *   alphabet of the property
    */
  def updateDefault(
      assumptionAlphabets: Buffer[Alphabet],
      propertyAlphabet: Alphabet
  ) = {
    require(nbProcesses == assumptionAlphabets.size)
    _assumptionAlphabets = assumptionAlphabets
    _propertyAlphabet = propertyAlphabet
    generateDefaultDependencies()
    if configuration.get().verbose then {
      logger.debug(s"Ass alphabets: $_assumptionAlphabets")
      logger.debug(s"Prop dependencies: $_propertyDependencies")
      logger.debug(s"Process deps: $_processDependencies")
      logger.debug(s"Circularity: $_isCircular")
    }
  }

  /** Update process and property dependencies so that any pair of processes
    * whose assumptions share a common symbol are in the dependencies of each
    * other, and recursively, if they share a common symbol with a third process
    * etc.
    */
  private def generateDefaultDependencies(): Unit = {
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
    def isOnACycle(pr: Int): Boolean = {
      val visited = Buffer.tabulate(nbProcesses)(_ => false)
      def visit(i: Int): Boolean = {
        if !visited(i) then {
          visited(i) = true
          _processDependencies(i).exists(visit(_))
        } else if i == pr then true
        else false
      }
      visit(pr)
    }
    _isCircular = Buffer.tabulate(nbProcesses)(isOnACycle)
  }
}

object LTLAssumeGuaranteeVerifier {
  private val logger = LoggerFactory.getLogger("CircAG")

  def checkLTL(ta: TA, ltlFormula: LTL): Option[Lasso] = {
    val accLabel = "_ltl_accept_"
    val ta_ltl = TA.fromLTL(ltlFormula.toString, Some(accLabel))
    val productTA = TA.synchronousProduct(List(ta, ta_ltl))
    checkBuchi(productTA, s"${ta_ltl.systemName}${accLabel}")
  }

  /** Check the reachability of a state labeled by label. Return such a trace if
    * any.
    *
    * @param ta
    * @param label
    */
  def checkBuchi(ta: TA, label: String): Option[Lasso] = {
    val beginTime = System.nanoTime()
    statistics.Counters.incrementCounter("model-checking")
    val modelFile =
      Files
        .createTempFile(
          configuration.get().getTmpDirPath(),
          "circag-query",
          ".ta"
        )
        .toFile()
    val pw = PrintWriter(modelFile)
    pw.write(ta.toString())
    pw.close()

    val certFile =
      Files
        .createTempFile(
          configuration.get().getTmpDirPath(),
          "circag-cert",
          ".cert"
        )
        .toFile()
    val cmd = "tck-liveness -a ndfs %s -l %s -o %s"
      .format(modelFile.toString, label, certFile.toString)
    System.out.println(cmd)
    logger.debug(cmd)

    val output = cmd.!!
    val cex = scala.io.Source.fromFile(certFile).getLines().toList

    if (!configuration.globalConfiguration.keepTmpFiles) {
      modelFile.delete()
      certFile.delete()
    }
    statistics.Timers.incrementTimer("tchecker", System.nanoTime() - beginTime)
    if (output.contains("CYCLE false")) then {
      None
    } else if (output.contains("CYCLE true")) then {
      Some(TA.getLassoFromCounterExampleOutput(cex, ta.alphabet))
    } else {
      throw FailedTAModelChecking(output)
    }
  }
}

class LTLAssumeGuaranteeVerifier(ltsFiles: Array[File], property: LTL) {
  private val logger = LTLAssumeGuaranteeVerifier.logger

  val nbProcesses = ltsFiles.size
  val propertyAlphabet = {
    NLTS.fromLTL(property.toString).alphabet
  }
  private val processes = ltsFiles.map(TA.fromFile(_)).toBuffer
  private val assumptions : Buffer[LTL] = Buffer.fill(nbProcesses)(LTLTrue())

  // Set of symbols that appear in the property alphabet, or in at least two processes
  val interfaceAlphabet =
    // Consider only symbols that appear at least in two processes (union of J_i's in CAV16)
    val symbolCount = HashMap[String, Int]()
    processes.foreach { p =>
      p.alphabet.foreach { sigma =>
        symbolCount.put(sigma, symbolCount.getOrElse(sigma, 0) + 1)
      }
    }
    symbolCount.filterInPlace((sigma, count) => count >= 2)
    propertyAlphabet | symbolCount.map({ (sigma, _) => sigma }).toSet

  val completeAssumptionAlphabets = processes
    .map({ pr =>
      interfaceAlphabet.intersect(pr.alphabet)
    })
    .toBuffer

  val proofSkeleton =
    AGProofSkeleton(completeAssumptionAlphabets, propertyAlphabet)
  logger.debug(s"Circularity of the assumptions: ${(0 until nbProcesses).map(proofSkeleton.isCircular(_))}")

  completeAssumptionAlphabets.zipWithIndex.foreach({ (alpha, i) =>
    proofSkeleton.setAssumptionAlphabet(i, alpha)
  })


  def setAssumption(processID : Int, formula: LTL) : Unit = {
    assumptions(processID) = formula
  }

  def checkInductivePremise(
      processID: Int
  ): Option[Lasso] = {
    val guarantee = assumptions(processID)
    val dependencies = proofSkeleton.processDependencies(processID)
    if proofSkeleton.isCircular(processID) then {
      val guarantee_matrix = guarantee match {
        case G(matrix) => matrix
        case _ => throw Exception(s"Guarantee formula for circular process ${processID} must be universal: ${guarantee}")
      }
      val circularDeps = dependencies.filter(proofSkeleton.isCircular)
      val noncircularDeps = dependencies.filterNot(proofSkeleton.isCircular)
      // Check for CEX of the form: /\_i noncircular-assumptions(i) /\ (/\_i circular-assumptions(i) U !guarantee)
      val circularLHS = 
        val matrices = 
          circularDeps
          .toSeq
          .map({ i =>
            assumptions(i) match {
              case G(subf) => subf
              case _ =>
                throw Exception(
                  s"Non-universal dependency for circular assumption ${processID}"
                )
            }
          })
        if matrices.size == 0 then LTLTrue()
        else matrices.tail.fold(matrices.head)({ (a,b) => And(a,b)})
      val noncircularLHS =
        val formulas = 
          noncircularDeps
          .map(assumptions.apply)
          .toSeq
        if formulas.size == 0 then LTLTrue()
        else formulas.tail.fold(formulas.head)({ (a,b) => And(a,b)})
      val f = noncircularLHS match {
        case _ : LTLTrue => 
          U(circularLHS, Not(guarantee_matrix))
        case _ => 
          And(noncircularLHS,U(circularLHS, Not(guarantee_matrix)))
      }
      System.out.println(s"Checking inductive premise for process ${processID}: ${f} ")
      LTLAssumeGuaranteeVerifier.checkLTL(processes(processID), f)
    } else {
      // Check for CEX of the form: /\_i assumptions(i) /\ !guarantee
      val noncircularLHS =
        val formulas = 
          dependencies
          .toSeq
          .map(assumptions.apply)
        if formulas.size == 0 then LTLTrue()
        else formulas.tail.fold(formulas.head)({ (a,b) => And(a,b)})
      val f = And(noncircularLHS,Not(guarantee))
      System.out.println(s"Checking formula: ${f} ")
      LTLAssumeGuaranteeVerifier.checkLTL(processes(processID), f)
    }
  }
}

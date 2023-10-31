package fr.irisa.circag.ltl

import org.slf4j.Logger
import org.slf4j.LoggerFactory
import collection.mutable.Buffer
import collection.mutable.HashMap

import fr.irisa.circag.{Alphabet, Symbol, TA}
/**
 * Malformed proof skeleton, for instance, when instantaneous dependencies are circular.
 */
class BadProofSkeleton(msg : String) extends Exception(msg)

/** Proof skeleton that stores the dependencies of the proof of the assumption
  * of each process, the alphabets of these assumptions and that of the
  * property, and whether each assumption's proof is circular.
  * We do not distinguish connected components but assume that all processes that are in
  * some cycle must be proven by a single induction.
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
    val propertyAlphabet = property.getAlphabet
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


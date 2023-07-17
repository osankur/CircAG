package fr.irisa.circag.dfa

import org.slf4j.Logger
import org.slf4j.LoggerFactory
import collection.mutable.Buffer
import collection.immutable.Set

import fr.irisa.circag.configuration
import scala.collection.mutable.Stack
/**
  * AG Proof skeleton specifies the dependencies for each premise of the N-way AG rule,
  * and the alphabets to be used for the assumption DFA of each TA.
  *
  * There are several modes. 
  * 
  * 1) In the manual mode, the sets of dependencies for each proof are set manually.
  * 2) updateByCone sets the dependencies of each process to all those processes
  * with which it shares a common sync label, either directly or indirectly. The dependencies of the property
  * are also computed similarly.
  * 3) A common way is to use setAssumptionAlphabetsByCommonAlphabet which sets each assumption's alphabets to
  *    the interface alphabet intersected with the given common alphabet, and applies updateByCone.
  * 
  * In short, manual proofs will mostly use 2, but the user can refine these using 1 if things get slow.
  * Automatic learning uses 2. Automatic learning with alphabet refinement uses 3.
  * 
  * In all cases, a topological order is generated. In this order, the proofs must be done left to right.
  * In fact, the proof of a process at a cluster at index i only depends on those further left.
  * 
  * @param processAlphabets
  * @param propertyAlphabet
  * @param commonAssumptionAlphabet
  */
class DFAProofSkeleton(processAlphabets : Buffer[Set[String]], private var _propertyAlphabet : Set[String], commonAssumptionAlphabet : Set[String]) {
  private val logger = LoggerFactory.getLogger("CircAG")

  val nbProcesses = processAlphabets.size

  private var _processDependencies = Buffer[Set[Int]]()
  private var _propertyDependencies = Set[Int]()
  private var _assumptionAlphabets = Buffer[Set[String]]()

  private var _clusters = Buffer[Set[Int]]()

  setAssumptionAlphabetsByCommonAlphabet(commonAssumptionAlphabet)

  def processDependencies(processID : Int) : Set[Int] = {
    _processDependencies(processID)
  }
  def propertyDependencies() : Set[Int] = {
    _propertyDependencies
  }

  def assumptionAlphabets(processID : Int) : Set[String] = {
    _assumptionAlphabets(processID)
  }
  /**
    * Return topologically ordered connected components: a process' assumption depends on assumptions on the left
    *
    * @return
    */
  def getTopologicalOrder() : Buffer[Set[Int]] = {
    _clusters
  }
  /**
    * Run Tarjan's algorithm to find SCCs in the topological order
    */
  def updateTopologicalOrder() : Unit = {
    _clusters = Buffer[Set[Int]]()
    var time = 0
    val disc = Buffer.fill(nbProcesses)(-1)
    val low = Buffer.fill(nbProcesses)(-1)
    val stackMember = Buffer.fill(nbProcesses)(false)
    val st = Stack[Int]()
    def scc(u : Int) : Unit = {
      st.push(u)
      stackMember(u) = true
      time += 1
      disc(u) = time
      low(u) = time
      _processDependencies(u).foreach(
        v => 
          if disc(v) == -1 then {
            scc(v)
            low(u) = Seq(low(u), low(v)).min
          } else if (stackMember(v)) then {
            low(u) = Seq(low(u), disc(v)).min
          }
      )
      if (low(u) == disc(u)){
        var w = 0
        var cluster = Set[Int]()
        while( st.top != u ) do {
          w = st.pop()
          stackMember(w) = false          
          cluster = cluster.incl(w)
        }
        cluster = cluster.incl(u)
        st.pop()
        _clusters.append(cluster)
      }
    }
    val topOrder = Buffer.fill(nbProcesses)(-1)
    val topVisited = Buffer.fill(nbProcesses)(false)
    var iOrder = nbProcesses-1
    def setTopOrder(u : Int) : Unit = {
      if !topVisited(u) then {
        topVisited(u) = true
        _processDependencies(u).foreach(setTopOrder)
        topOrder(iOrder) = u
        iOrder -= 1 
      }
    }
    (0 until nbProcesses).foreach(setTopOrder)
    topOrder.foreach(
      u => if disc(u) < 0 then scc(u)
    )
  }

  def setProcessDependencies(i : Int, deps : Set[Int]) : Unit = {
    require(!deps.contains(i))
    _processDependencies(i) = deps
    updateTopologicalOrder()
  }
  def setPropertyDependencies(deps : Set[Int]) : Unit = {
    _propertyDependencies = deps
  }

  def setAssumptionAlphabet(i : Int, alpha : Set[String]) : Unit = {
    _assumptionAlphabets(i) = alpha
    updateTopologicalOrder()    
  }
  def setPropertyAlphabet(alpha : Set[String]) : Unit = {
    _propertyAlphabet = alpha
  }
  def getPropertyAlphabet() : Set[String] = _propertyAlphabet

  def setAssumptionAlphabetsByCommonAlphabet(alpha : Set[String]) : Unit = {
    _assumptionAlphabets = processAlphabets.map(_.intersect(alpha))
    updateByCone()
  }

  /**
    * Update the fields from the given assumption alphabet: the dependencies of a process (or a property) are those assumptions that
    * share a common label, and those that share a common label with other dependencies.
    *
    */
  def updateByCone() = {
    _processDependencies = Buffer.tabulate(nbProcesses)({_ => Set[Int]()})
    // Compute simplified sets of assumptions for the new alphabet
    // adj(i)(j) iff (i = j) or (i and j have a common symbol) or (i has a common symbol with k such that adj(k)(j))
    // Index nbProcesses represents the property.
    var adj = Buffer.tabulate(nbProcesses+1)({_ => Buffer.fill(nbProcesses+1)(false)})
    for i <- 0 until nbProcesses do {
      adj(i)(i) = true
      for j <- 0 until i do {
        adj(i)(j) = !processAlphabets(i).intersect(processAlphabets(j)).isEmpty
        adj(j)(i) = adj(i)(j)
      }
    }
    adj(nbProcesses)(nbProcesses) = true
    for j <- 0 until nbProcesses do {
        adj(nbProcesses)(j) = !_propertyAlphabet.intersect(processAlphabets(j)).isEmpty
        adj(j)(nbProcesses) = adj(nbProcesses)(j)
    }
    for k <- 0 until nbProcesses+1 do {
      for i <- 0 until nbProcesses+1 do {
        for j <- 0 until nbProcesses+1 do {
          if(adj(i)(k) && adj(k)(j)) then {
            adj(i)(j) = true
          }
        }
      }
    }
    for i <- 0 until nbProcesses do {
      _processDependencies(i) = adj(i).zipWithIndex.filter({(b,i) => b}).map(_._2).toSet.diff(Set[Int](i, nbProcesses))
    }
    _propertyDependencies = adj(nbProcesses).zipWithIndex.filter({(b,i) => b}).map(_._2).toSet - nbProcesses

    // An assumption's proof must not depend on itself
    for i <- 0 until nbProcesses do {
      require(!processDependencies(i).contains(i))
    }
    updateTopologicalOrder()    
    logger.debug(s"Ass alphabets: $_assumptionAlphabets")
    logger.debug(s"Prop dependencies: $_propertyDependencies")
    logger.debug(s"Process deps: $_processDependencies")
  }
  
}

package fr.irisa.circag.dfa

import org.slf4j.Logger
import org.slf4j.LoggerFactory
import collection.mutable.{Buffer, Stack, HashMap}

import fr.irisa.circag.configuration
import fr.irisa.circag._

/**
  * AG Proof skeleton stores process and property alphabets, and keeps the dependencies for each premise of the N-way AG rule.
  *
  * A process can have an assumption over an alphabet that is smaller than its own alphabet. The alphabet of each process
  * can be set by the setAssumptionAlphabet method. One can also set all alphabets at once by setAssumptionAlphabetsByCommonAlphabet
  * by providing a common alphabet alpha, which will set each alphabet to the intersection of the common alphabet and the alphabet of the process.
  * The interface alphabet is the set of symbols that appear at least in two processes.
  * 
  * This class maintains the set of process and property proof dependencies in a sound manner.
  * A topological order of these dependencies is also generated: In this order, the proofs must be done left to right.
  * In fact, the proof of a process at a cluster at index i only depends on those further left. This means that
  * if one changes the assumption i, the proofs of assumptions 0...i-1 are not affected.
  * 
  */
class DFAProofSkeleton(val system : SystemSpec) {  
  private val logger = LoggerFactory.getLogger("CircAG")

  private val _processAlphabets : Buffer[Set[String]] = system.processes.map(_.alphabet).toBuffer
  private var _propertyAlphabet = system.property match{
    case None => Set[String]()
    case Some(p) => p.alphabet
  }
  val nbProcesses = _processAlphabets.size
 
  // Set of symbols that appear in the property alphabet, or in at least two processes
  private var _interfaceAlphabet = Set[String]()

  /** Intersection of local alphabets with the interface alphabet: when all
   * assumptions use these alphabets, the AG procedure is complete.
   * i.e. alpha_F = alphaM_i /\ alphaP cup J_i
   */
  protected var _completeAlphabets = Buffer.tabulate(nbProcesses)(_ => Set[String]())

  // Set of processes on which given process' proof depends
  private var _processDependencies = Buffer[Set[Int]]()
  // Set of processes on which the property's proof depends
  private var _propertyDependencies = Set[Int]()
  // Alphabet of the assumption of each process
  private var _assumptionAlphabets = Buffer[Set[String]]()

  // Clusters in the SCC decomposition of processes for the relation of "proof depends on"
  private var _clusters = Buffer[Set[Int]]()

  updateInterfaceAndCompleteAlphabets()
  setAssumptionAlphabetsByCommonAlphabet(_interfaceAlphabet)
  updateDependenciesByCone()
  updateTopologicalOrder()

  /**
    * Update _interfaceAlphabet and _completeAlphabets
    */
  private def updateInterfaceAndCompleteAlphabets() : Unit ={
    // Consider only symbols that appear at least in two processes (union of J_i's in CAV16)
    val symbolCount = HashMap[String, Int]()
    system.processes.foreach { p =>
      p.alphabet.foreach { sigma =>
        symbolCount.put(sigma, symbolCount.getOrElse(sigma, 0) + 1)
      }
    }
    symbolCount.filterInPlace((sigma, count) => count >= 2)
    _interfaceAlphabet = _propertyAlphabet | symbolCount.map({ (sigma, _) => sigma }).toSet

    _completeAlphabets = system.processes
      .map({ pr =>
        _interfaceAlphabet.intersect(pr.alphabet)
      })
      .toBuffer
  }
  
  def getPropertyAlphabet() : Set[String] = _propertyAlphabet
  def getInterfaceAlphabet(): Set[String] = _interfaceAlphabet
  def getCompleteAlphabet(processID : Int): Set[String] = _completeAlphabets(processID)
  def processDependencies(processID : Int) : Set[Int] = _processDependencies(processID)
  def propertyDependencies() : Set[Int] = _propertyDependencies
  def assumptionAlphabets(processID : Int) : Set[String] = _assumptionAlphabets(processID)
  /**
    * Return topologically ordered connected components: a process' assumption depends on assumptions on the left
    *
    * @return sequence of clusters of processes that is topologically ordered
    */
  def getTopologicalOrder() : Buffer[Set[Int]] = _clusters

  def setAssumptionAlphabet(i : Int, alpha : Set[String]) : Unit = {
    _assumptionAlphabets(i) = alpha
    update()
  }
  def setPropertyAlphabet(alpha : Set[String]) : Unit = {
    _propertyAlphabet = alpha
    update()
  }
  // Update each assumption's alphabet as alpha /\ their alphabet
  def setAssumptionAlphabetsByCommonAlphabet(alpha : Set[String]) : Unit = {
    _assumptionAlphabets = _processAlphabets.map(_.intersect(alpha))
    update()
  }

  /**
    * Update interface and complete alphabets, process and property dependencies, and the topological order.
    */
  private def update() : Unit = {
    updateInterfaceAndCompleteAlphabets()
    updateDependenciesByCone()
    updateTopologicalOrder()
  }

  /**
    * Run Tarjan's algorithm to find SCCs in the topological order
    */
  private def updateTopologicalOrder() : Unit = {
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

  /**
    * Update processDependencies: the dependencies of a process (or a property) are those assumptions that
    * share a common label, and those that share a common label with other dependencies, and so on.
    */
  def updateDependenciesByCone() = {
    _processDependencies = Buffer.tabulate(nbProcesses)({_ => Set[Int]()})
    val adj = getCones()
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

  /**
    * Return symmetric Boolean adjacency matrix adj where adj[i][j] iff i=j or i's proof must depend on j.
    *
    * @return adjacency matrix
    */
  private def getCones() : Buffer[Buffer[Boolean]] ={
    _processDependencies = Buffer.tabulate(nbProcesses)({_ => Set[Int]()})
    // Compute simplified sets of assumptions for the new alphabet
    // adj(i)(j) iff (i = j) or (i and j have a common symbol) or (i has a common symbol with k such that adj(k)(j))
    // Index nbProcesses represents the property.
    var adj = Buffer.tabulate(nbProcesses+1)({_ => Buffer.fill(nbProcesses+1)(false)})
    for i <- 0 until nbProcesses do {
      adj(i)(i) = true
      for j <- 0 until i do {
        adj(i)(j) = !_processAlphabets(i).intersect(_processAlphabets(j)).isEmpty
        adj(j)(i) = adj(i)(j)
      }
    }
    adj(nbProcesses)(nbProcesses) = true
    for j <- 0 until nbProcesses do {
        adj(nbProcesses)(j) = !_propertyAlphabet.intersect(_processAlphabets(j)).isEmpty
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
    adj
  }
}

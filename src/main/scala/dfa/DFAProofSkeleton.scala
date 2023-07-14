package fr.irisa.circag.dfa

import org.slf4j.Logger
import org.slf4j.LoggerFactory
import collection.mutable.Buffer
import collection.immutable.Set

import fr.irisa.circag.configuration
/**
  * AG Proof skeleton specifies the dependencies for each premise of the N-way AG rule,
  * and the alphabets to be used for the assumption DFA of each TA.
  * 
  * @param processDependencies the set of process indices on which the proof of process(i) must depend.
  * @param propertyDependencies the set of process indices on which the proof of the final premise must depend.
  * @param commonAssumptionAlphabet 
  */
class DFAProofSkeleton(val nbProcesses : Int, processAlphabets : Buffer[Set[String]], propertyAlphabet : Set[String]) {
  private val logger = LoggerFactory.getLogger("CircAG")

  var processDependencies = Buffer[Set[Int]]()
  var propertyDependencies = Set[Int]()
  var assumptionAlphabets = Buffer[Set[String]]()

  def setAssumptionAlphabet(i : Int, alpha : Set[String]) : Unit = {
    assumptionAlphabets(i) = alpha
    updateByCone()
  }

  def setAssumptionAlphabetsByCommonAlphabet(alpha : Set[String]) : Unit = {
    assumptionAlphabets = processAlphabets.map(_.intersect(alpha))
    updateByCone()
  }

  def this(processAlphabets : Buffer[Set[String]], propertyAlphabet : Set[String], commonAssumptionAlphabet : Set[String]) = {
    this(processAlphabets.size, processAlphabets, propertyAlphabet)
    setAssumptionAlphabetsByCommonAlphabet(commonAssumptionAlphabet)
  }
  /**
    * Update the fields from the given assumption alphabet: the dependencies of a process (or a property) are those assumptions that
    * share a common label, and those that share a common label with other dependencies.
    *
    */
  def updateByCone() = {
    processDependencies = Buffer.tabulate(nbProcesses)({_ => Set[Int]()})
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
        adj(nbProcesses)(j) = !propertyAlphabet.intersect(processAlphabets(j)).isEmpty
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
      processDependencies(i) = adj(i).zipWithIndex.filter({(b,i) => b}).map(_._2).toSet.diff(Set[Int](i, nbProcesses))
    }
    propertyDependencies = adj(nbProcesses).zipWithIndex.filter({(b,i) => b}).map(_._2).toSet - nbProcesses
    
    logger.debug(s"Ass alphabets: $assumptionAlphabets")
    logger.debug(s"Prop dependencies: $propertyDependencies")
    logger.debug(s"Process deps: $processDependencies")
  }
  
}

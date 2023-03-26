package fr.irisa.circag.tchecker.ltl

import collection.JavaConverters._
import collection.convert.ImplicitConversions._
import collection.mutable.Buffer
import collection.mutable.HashMap
import java.io.ByteArrayInputStream

import jhoafparser.consumer.HOAConsumerPrint;
import jhoafparser.parser.HOAFParser;
import jhoafparser.parser.generated.ParseException;
import jhoafparser.consumer.HOAConsumerStore
import jhoafparser.ast.BooleanExpression
import jhoafparser.ast.AtomLabel
import jhoafparser.ast.AtomAcceptance
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

import fr.irisa.circag.configuration
import fr.irisa.circag.{DLTS, NLTS, Alphabet, Trace}

/**
  * LTL syntax: each event is an atomic predicate.
  * Produce LTL formula from the premise checker
  * Use Spot to get HOA Buchi automaton, and read it back with HOAParser
  *     - The automaton labels are Boolean expressions
  *     - infeasible valuations such as "a & b" appear in transitions; that's OK
  *     - Make sure acceptance condition in on states (state-acc), and it is Buchi (not gen Buchi)
  *     - Make sure there are no implicit labels
  * Translate this to a TChecker automaton by using Z3 to explicitly enumerate all valuations in which a single event is true
  *     - Discard other transitions
  * Make the product with the process TA by synchronizing on common events
  * Use tck-liveness to model check
  */


/**
  * Proof skeleton that stores the dependencies of the proof of the assumption of each process,
  * the alphabets of these assumptions and that of the property, and whether each assumption's
  * proof is circular. 
  * 
  * The skeleton can either be used in default mode using the update function: in this case, a common assumption alphabet
  * is specified and this will update the skeleton to add dependencies between all pairs of processes that share a common
  * symbol or with a thid process. Alternatively, one can set manually all these fields. In all cases, the circularity information
  * is kept up to date automatically. 
  * 
  * @param nbProcesses Number of processes
  */
class AGProofSkeleton(nbProcesses : Int) {
  /**
   * For each process, the set of process indices on which the proof depends
  */
  private var _processDependencies = Buffer.tabulate(nbProcesses)(_ => Set[Int]())
  /**
   * The set of process indices on which the proof of the property depends
  */
  private var _propertyDependencies = Set[Int]()
  
  /**
   * Alphabet of the property
  */
  private var _propertyAlphabet : Alphabet = Set[String]()

  /**
   * For each process, the alphabet of the assumption
  */
  private var _assumptionAlphabets = Buffer.tabulate(nbProcesses)(_ => Set[String]())
  /**
    * Whether the proof of given process is circular
    */
  private var _isCircular = Buffer.tabulate(nbProcesses)(_ => false)

  def processDependencies(i : Int) = _processDependencies(i)
  def assumptionAlphabet(i : Int) = _assumptionAlphabets(i)
  def isCircular(i : Int) = _isCircular(i)
  def propertyDependencies = _propertyDependencies

  def setProcessDependencies(i : Int, deps : Set[Int]) = 
    _processDependencies(i) = deps
    updateCircularity()

  def setPropertyDependencies(deps : Set[Int]) = 
    _propertyDependencies = deps

  def setAssumptionAlphabet(i : Int, alphabet : Alphabet) = 
    _assumptionAlphabets(i) = alphabet

  def setPropertyAlphabet(alphabet : Alphabet ) = 
    _propertyAlphabet = alphabet

  def this(processAlphabets : Buffer[Alphabet], propertyAlphabet : Set[String], newAssumptionAlphabet : Set[String]) = {
    this(processAlphabets.size)
    updateDefault(processAlphabets, propertyAlphabet, newAssumptionAlphabet)
  }

  /**
    * Update the proof skeleton from the given common assumption alphabet: the alphabet of the assumption of each process becomes
    * the intersection of the propertyAlphabet with the process alphabet. Moreover, process dependencies are updated so as to include
    * exactly all processes with which the assumptions share a common aymbol, or recursively, there is a third process whose assumption
    * shares a common symbol with each etc. Circularity information is updated.
    *
    * @param processAlphabets alphabets of the processes
    * @param propertyAlphabet alphabet of the property
    * @param newAssumptionAlphabet the common assumption alphabet
    */
  def updateDefault(processAlphabets : Buffer[Alphabet], propertyAlphabet : Alphabet, commonAssumptionAlphabet : Alphabet) = {
    require(nbProcesses == processAlphabets.size)
    _assumptionAlphabets = processAlphabets.map(_.intersect(commonAssumptionAlphabet))
    _propertyAlphabet = propertyAlphabet
    generateDefaultDependencies()
    if configuration.get().verbose then {
      System.out.println(s"Ass alphabets: $_assumptionAlphabets")
      System.out.println(s"Prop dependencies: $_propertyDependencies")
      System.out.println(s"Process deps: $_processDependencies")
      System.out.println(s"Circularity: $_isCircular")
    }
  }

  /**
    * Update process and property dependencies so that any pair of processes whose assumptions share a common symbol
    * are in the dependencies of each other, and recursively, if they share a common symbol with a third process etc.
    */
  private def generateDefaultDependencies() : Unit = {
    val nbProcesses = _processDependencies.size
    _processDependencies = Buffer.tabulate(nbProcesses)({_ => Set[Int]()})
    // Compute simplified sets of assumptions for the new alphabet
    // adj(i)(j) iff (i = j) or (i and j have a common symbol) or (i has a common symbol with k such that adj(k)(j))
    // Index nbProcesses represents the property.
    var adj = Buffer.tabulate(nbProcesses+1)({_ => Buffer.fill(nbProcesses+1)(false)})
    for i <- 0 until nbProcesses do {
      adj(i)(i) = true
      for j <- 0 until i do {
        adj(i)(j) = !_assumptionAlphabets(i).intersect(_assumptionAlphabets(j)).isEmpty
        adj(j)(i) = adj(i)(j)
      }
    }
    adj(nbProcesses)(nbProcesses) = true
    for j <- 0 until nbProcesses do {
        adj(nbProcesses)(j) = !_propertyAlphabet.intersect(_assumptionAlphabets(j)).isEmpty
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
    updateCircularity()
  }

  private def updateCircularity() : Unit = {
    def isOnACycle(pr : Int ) : Boolean = {
      val visited = Buffer.tabulate(nbProcesses)(_ => false)
      def visit(i : Int) : Boolean = {
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
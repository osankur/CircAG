package fr.irisa.circag

import scala.collection.mutable.Buffer
import scala.collection.mutable.HashMap
import scala.collection.mutable.ArrayBuffer
import scala.collection.immutable.Set

import collection.convert.ImplicitConversions._

import net.automatalib.automata.fsa.DFA;
import net.automatalib.automata.fsa.impl.compact.CompactDFA;
import net.automatalib.util.automata.fsa.DFAs
import net.automatalib.automata.fsa.impl.compact.CompactDFA;
import net.automatalib.util.automata.builders.AutomatonBuilders;
import net.automatalib.visualization.Visualization;
import net.automatalib.words.Alphabet;
import net.automatalib.words.impl.Alphabets;

/**
  * Deterministic LTS used as hypotheses and properties.
  *
  * @param name
  * @param dfa
  * @param alphabet
  */
case class DLTS(val name : String, val dfa: DFA[Integer, String], val alphabet: Set[String])

type Trace = List[String]

object DLTS {

  /** Given (dfa, alphabet), compute the lifting of the dfa to extendedAlphabet
    * by copying it and adding self-loops at all states on symbols in
    * extendedAlphabet \ alphabet.
    *
    * @param dfa
    * @param alphabet
    * @param extendedAlphabet
    * @return
    */
  def lift(dlts: DLTS, extendedAlphabet: Set[String], name : Option[String] = None): DLTS = {
    val alphabet = dlts.alphabet
    val dfa = dlts.dfa

    val newAlphabet =
      (alphabet | extendedAlphabet)
    val newSymbols =
      extendedAlphabet.diff(alphabet)
    System.out.println(s"DLTS.alphabet: ${dlts.alphabet}, extendedAlphabet: ${extendedAlphabet}, newAlphabet: ${newAlphabet}")
    val liftedDFA =
      CompactDFA.Creator().createAutomaton(Alphabets.fromList(newAlphabet.toList))
    for i <- 1 to dfa.size() do {
      liftedDFA.addState()
    }
    dfa.getInitialStates().foreach(liftedDFA.setInitialState(_))
    for s <- dfa.getStates() do {
      if (dfa.isAccepting(s)) {
        liftedDFA.setAccepting(s, true)
      } else {
        liftedDFA.setAccepting(s, false)
      }
      for sigma <- newSymbols do {
        liftedDFA.addTransition(s, sigma, s)
      }
      for sigma <- alphabet do {
        for sprime <- dfa.getSuccessors(s, sigma) do {
          liftedDFA.addTransition(s, sigma, sprime)
        }
      }
    }
    // System.out.println(s"Showing lifting to ${newAlphabet}")
    // Visualization.visualize(liftedDFA, Alphabets.fromList(newAlphabet.toList))
    return DLTS(name.getOrElse(dlts.name), liftedDFA, newAlphabet)
  }

  /** Lift to extendedAlphabet as the method lift, and remove all transitions
    * from non-accepting states
    *
    * @param dlts
    * @param extendedAlphabet
    * @return
    */
  def liftAndStripNonAccepting(
      dlts: DLTS,
      extendedAlphabet: Set[String],
      name : Option[String] = None
  ): DLTS = {
    val liftedDLTS = lift(dlts, extendedAlphabet, name)
    liftedDLTS.dfa match {
      case cdfa: CompactDFA[?] =>
        cdfa
          .getStates()
          .foreach(s =>
            if !cdfa.isAccepting(s) then {
              cdfa.removeAllTransitions(s)
            }
          )
          // System.out.println(cdfa.getInputAlphabet())
        // System.out.println(s"${dlts.name} before lift-stripping for alphabet ${extendedAlphabet}")
        // Visualization.visualize(dlts.dfa, Alphabets.fromList(dlts.alphabet.toList))
        // System.out.println(s"${dlts.name} after lift-stripping")
        // Visualization.visualize(liftedDLTS.dfa, Alphabets.fromList(liftedDLTS.alphabet.toList))
        liftedDLTS
      case _ => throw Exception("Can only strip CompactDFA")
    }
  }

  /**
    * Make straight-line DLTS reading a given trace, projecte to projectionAlphabet
    *
    * @param trace
    * @param projectionAlphabet
    * @return
    */
  def fromTrace(trace: Trace, projectionAlphabet : Option[Set[String]]) : DLTS = {
    val alph = projectionAlphabet.getOrElse(trace.toSet)
    val projTrace = trace.filter(alph.contains(_))

    val dfa =
      CompactDFA.Creator().createAutomaton(Alphabets.fromList(alph.toList))
    dfa.addState()
    for i <- 1 to projTrace.size do {
      dfa.addState()
    }
    dfa.setInitialState(0)
    projTrace.zip(0 until projTrace.size).foreach({
      (sigma, i) =>
        dfa.addTransition(i, sigma, i+1)
    })
    dfa.setAccepting(projTrace.size, true)
    DLTS("_trace_", dfa, alph)
  }

  def makePrefixClosed(dfa : DFA[?, String], alphabet : Set[String]) : CompactDFA[String] = {
    val statesMap  = HashMap((dfa.getInitialState(),0))
    var index = 0
    val newDFA = CompactDFA.Creator().createAutomaton(Alphabets.fromList(alphabet.toList))
    dfa.getStates().foreach({
      state => 
        statesMap.put(state, index)
        index = index + 1
        newDFA.addState(dfa.isAccepting(state))
    })
    newDFA.setInitial(statesMap(dfa.getInitialState()), true)
    dfa.getStates().foreach(
      {s =>
        for a <- alphabet do {
          dfa.getSuccessors(s,a).foreach(
            {snext =>
              //if (newDFA.isAccepting(statesMap(s)) && newDFA.isAccepting(statesMap(snext))) then {
              newDFA.addTransition(statesMap(s), a, statesMap(snext))
              //}
            }
          )        
        }
      }
    )
    def isAcceptingReachable(s: Int) : Boolean =
      { 
        val visited = Array.fill(newDFA.size)(false)
        def dfs(s : Int) : Boolean = {
          System.out.println(s"DFS: ${s}")
          if newDFA.isAccepting(s) then {
            true
          } else if !visited(s) then {
            visited(s) = true
            // System.out.println(alphabet.toSeq.map(newDFA.getSuccessors(s, _)))
            alphabet.toSeq.map(newDFA.getSuccessors(s, _).exists({dfs(_)})).exists({x=>x})
          } else {
            false
          }
        }
        dfs(s)
      }
    // Make it prefix-closed
    if(!DFAs.isPrefixClosed(dfa,Alphabets.fromList(alphabet.toList))) then {
      newDFA.getStates().filter(!newDFA.isAccepting(_)).foreach({
        s => newDFA.setAccepting(s, isAcceptingReachable(s))
      })
      // System.out.println("Showing non-prefix-closed automaton")
      // Visualization.visualize(dfa, Alphabets.fromList(alphabet.toList))
      // System.out.println("Prefix closure:")
      // Visualization.visualize(newDFA, Alphabets.fromList(alphabet.toList))
    }
    newDFA
  }
}

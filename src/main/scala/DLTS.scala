package fr.irisa.circag

import scala.collection.mutable.Buffer
import scala.collection.mutable.HashMap
import scala.collection.mutable.ArrayBuffer
import scala.collection.immutable.Set

import collection.convert.ImplicitConversions._

import net.automatalib.automata.fsa.DFA;
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
case class DLTS(val name : String, val dfa: DFA[Integer, String], val alphabet: Alphabet[String])

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
  def lift(dlts: DLTS, extendedAlphabet: Alphabet[String], name : Option[String] = None): DLTS = {
    val alphabet = dlts.alphabet
    val dfa = dlts.dfa

    val newAlphabet =
      Alphabets.fromList((alphabet.toSet | extendedAlphabet.toSet).toBuffer)
    val newSymbols =
      Alphabets.fromList(extendedAlphabet.toSet.diff(alphabet.toSet).toBuffer)
    val liftedDFA =
      CompactDFA.Creator().createAutomaton(newAlphabet)
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
      extendedAlphabet: Alphabet[String],
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
        liftedDLTS
      case _ => throw Exception("Can only strip CompactDFA")
    }
  }

}

package fr.irisa.circag

import scala.collection.mutable.Buffer
import scala.collection.mutable.HashMap
import scala.collection.mutable.ArrayBuffer
import scala.collection.immutable.Set
import collection.convert.ImplicitConversions._
import java.io.ByteArrayInputStream
import dk.brics.automaton
import net.automatalib.brics.BricsNFA
import net.automatalib.automata.fsa.MutableDFA
import net.automatalib.automata.fsa.DFA;
import net.automatalib.automata.fsa.impl.compact.CompactDFA;
import net.automatalib.automata.fsa.impl.FastDFA
import net.automatalib.automata.fsa.impl.FastNFA
import net.automatalib.automata.fsa.impl.FastDFAState
import net.automatalib.util.automata.fsa.DFAs
import net.automatalib.util.automata.fsa.NFAs
import net.automatalib.automata.fsa.impl.compact.CompactDFA;
import net.automatalib.util.automata.builders.AutomatonBuilders;
import net.automatalib.visualization.Visualization;
import net.automatalib.words.Alphabet;
import net.automatalib.words.impl.Alphabets;
import net.automatalib.automata.Automaton
import net.automatalib.automata.fsa.FiniteStateAcceptor
import jhoafparser.consumer.HOAConsumerPrint;
import jhoafparser.parser.HOAFParser;
import jhoafparser.parser.generated.ParseException;
import jhoafparser.consumer.HOAConsumerStore
import jhoafparser.ast.BooleanExpression
import jhoafparser.ast.AtomLabel
import jhoafparser.ast.AtomAcceptance

import com.microsoft.z3

import fr.irisa.circag.statistics
import fr.irisa.circag.configuration
import fr.irisa.circag.Trace
import fr.irisa.circag.DLTS

type Symbol = String
type Alphabet = Set[Symbol]
type Trace = List[String]

/** Deterministic LTS used as hypotheses and properties.
  *
  * @param name
  * @param dfa
  * @param alphabet
  */
trait LTS[FA <: FiniteStateAcceptor[?, String] with Automaton[?, String, ?]](
    val name: String,
    val dfa: FA,
    val alphabet: Set[String]
) {
  var comments : String= ""
  def visualize() : Unit = {
    Visualization.visualize(dfa, Alphabets.fromList(alphabet.toList))
  }
}

class DLTS(
    override val name: String,
    override val dfa: FastDFA[String],
    override val alphabet: Set[String]
) extends LTS[FastDFA[String]](name, dfa, alphabet)

class NLTS(
    override val name: String,
    override val dfa: FastNFA[String],
    override val alphabet: Set[String]
) extends LTS[FastNFA[String]](name, dfa, alphabet)


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
  def lift(
      dlts: DLTS,
      extendedAlphabet: Set[String],
      name: Option[String] = None
  ): DLTS = {
    val alphabet = dlts.alphabet
    val dfa = dlts.dfa

    val newAlphabet =
      (alphabet | extendedAlphabet)
    val newSymbols =
      extendedAlphabet.diff(alphabet)

    val liftedDFA = FastDFA(Alphabets.fromList(newAlphabet.toList))
    val newStates = Buffer[FastDFAState]()
    for i <- 1 to dfa.size() do {
      newStates.append(liftedDFA.addState())
    }
    // System.out.println(s"liftedDFA size: ${liftedDFA.size}, alphabet size: ${liftedDFA.getInputAlphabet()}")
    dfa.getInitialStates().foreach({s =>liftedDFA.setInitialState(newStates(s.getId()))})
    for s <- dfa.getStates() do {
      liftedDFA.setAccepting(newStates(s.getId()), dfa.isAccepting(s))
      for sigma <- newSymbols do {
        liftedDFA.setTransition(newStates(s.getId()), sigma, newStates(s.getId()))
      }
      for sigma <- alphabet do {
        for sprime <- dfa.getSuccessors(s, sigma) do {
          // System.out.println(s"${(s,s.getId())} -> ${sprime} by ${sigma}")
          liftedDFA.setTransition(newStates(s.getId()), sigma, newStates(sprime.getId()))
        }
      }
    }
    
    // System.out.println(s"Showing lifting to ${newAlphabet}")
    // Visualization.visualize(liftedDFA, Alphabets.fromList(newAlphabet.toList))
    return DLTS(name.getOrElse(dlts.name), liftedDFA, newAlphabet)
  }

  /** Complete, lift to extendedAlphabet, and remove all transitions from
    * non-accepting states
    *
    * @param dlts
    * @param extendedAlphabet
    * @return
    */
  def liftAndStripNonAccepting(
      dlts: DLTS,
      extendedAlphabet: Set[String],
      name: Option[String] = None
  ): DLTS = {

    var beginTime = System.nanoTime()

    val alph = Alphabets.fromList(dlts.alphabet.toList)
    val tmpFastDFA = FastDFA(alph)
    val liftedDLTS = lift(
      DLTS(dlts.name,
          DFAs.complete(dlts.dfa, alph, tmpFastDFA),
          dlts.alphabet
      ),
      extendedAlphabet,
      name
    )
    liftedDLTS.dfa match {
      case cdfa: MutableDFA[?,?] =>
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
        statistics.liftingTime = statistics.liftingTime + (System.nanoTime() - beginTime)
        liftedDLTS
      // case _ => throw Exception("Can only strip CompactDFA")
    }
  }

  /** Make straight-line DLTS reading a given trace, projecte to
    * projectionAlphabet
    *
    * @param trace
    * @param projectionAlphabet
    * @return
    */
  def fromTrace(trace: Trace, alphabet : Option[Set[String]] = None): DLTS = {
    val alph = alphabet.getOrElse(trace.toSet) | trace.toSet
    val dfa = FastDFA(Alphabets.fromList(alph.toList))
    val newStates = Buffer[FastDFAState]()
    newStates.append(dfa.addState())
    for i <- 1 to trace.size do {
      newStates.append(dfa.addState(i == trace.size))
    }
    if(trace.size == 0) then{
      newStates(0).setAccepting(true)
    }
    dfa.setInitialState(newStates(0))
    trace
      .zip(0 until trace.size)
      .foreach({ (sigma, i) =>
        dfa.setTransition(newStates(i), sigma, newStates(i + 1))
      })
    // dfa.setAccepting(projTace.size, true)
    DLTS("_trace_", dfa, alph)
  }

  /**
    * Build deterministic LTS from possbly non-deterministic HOA Buchi automaton description.
    *
    * @param automatonString
    * @param acceptingLabel
    * @return
    */
  def fromHOA(automatonString : String) : DLTS = {
      val nlts = HOA.toLTS(automatonString)
      DLTS(nlts.name, NFAs.determinize(nlts.dfa, nlts.dfa.getInputAlphabet()).toFastDFA, nlts.alphabet)
  }

  def fromRegExp(name : String, regexp : String ) : DLTS = {
    var currentChar = 'a'
    val names = HashMap[Character, String]()
    val identifierReg = ".*?@([a-zA-Z0-9]+).*".r

    var modifiedRegexp = regexp
    def addIdentifier() : Boolean = {
      modifiedRegexp match {
        case identifierReg(name) => 
          // System.out.println(s"${name} -> ${currentChar}")
          names.put(currentChar, name)
          modifiedRegexp = modifiedRegexp.replaceAllLiterally(s"@${name}", s"${currentChar}")
          currentChar = (Char.char2int(currentChar) + 1).toChar
          true
        case _ => 
          false
      }
    }
    // System.out.println(s"Initial regex: ${modifiedRegexp}")
    while(addIdentifier()){}
    // System.out.println(s"Modified regex: ${modifiedRegexp}")
    val aut = BricsNFA(dk.brics.automaton.RegExp(modifiedRegexp).toAutomaton())
    val dfa = NFAs.determinize(aut, Alphabets.characters('A', 'z'))

    val alph = Alphabets.fromList(names.values.toList)
    val newDFA = FastDFA(alph)
      // CompactDFA.Creator().createAutomaton(alph)
    val newStates = Buffer[FastDFAState]()
    dfa
      .getStates()
      .foreach({ state =>
        newStates.append(newDFA.addState(dfa.isAccepting(state)))
      })
    newDFA.setInitial(newStates(dfa.getInitialState()), true)
    dfa
      .getStates()
      .foreach(
        { s =>
          for a <- names.keys do {
            dfa
              .getSuccessors(s, a)
              .foreach(
                { snext =>
                  newDFA.setTransition(newStates(s), names(a), newStates(snext))
                }
              )
          }
        }
      )
    // Visualization.visualize(newDFA, alph)
    DLTS(name, newDFA, alph.toSet)
  }

  def makePrefixClosed(
      dfa: DFA[?, String],
      alphabet: Set[String],
      removeNonAcceptingStates: Boolean = false
  ): FastDFA[String] = {
    val statesMap = HashMap((dfa.getInitialState(), FastDFAState(0,false)))
    val newDFA =
     new FastDFA(Alphabets.fromList(alphabet.toList))
    dfa
      .getStates()
      .foreach({ state =>
        statesMap.put(state, newDFA.addState(dfa.isAccepting(state)))
      })
    newDFA.setInitial(statesMap(dfa.getInitialState()), true)
    dfa
      .getStates()
      .foreach(
        { s =>
          for a <- alphabet do {
            dfa
              .getSuccessors(s, a)
              .foreach(
                { snext =>
                  // if (newDFA.isAccepting(statesMap(s)) && newDFA.isAccepting(statesMap(snext))) then {
                  newDFA.setTransition(statesMap(s), a, statesMap(snext))
                  // }
                }
              )
          }
        }
      )
    // def isAcceptingReachable(s: Int): Boolean = {
    //   val visited = Array.fill(newDFA.size)(false)
    //   def dfs(s: Int): Boolean = {
    //     if newDFA.isAccepting(s) then {
    //       true
    //     } else if !visited(s) then {
    //       visited(s) = true
    //       // System.out.println(alphabet.toSeq.map(newDFA.getSuccessors(s, _)))
    //       alphabet.toSeq
    //         .map(newDFA.getSuccessors(s, _).exists({ dfs(_) }))
    //         .exists({ x => x })
    //     } else {
    //       false
    //     }
    //   }
    //   dfs(s)
    // }
    newDFA
      .getStates()
      .filter(!newDFA.isAccepting(_))
      .foreach({ s =>
        newDFA.removeAllTransitions(s)
      })
    if (removeNonAcceptingStates) then {
      var rm = false
      for sigma <- newDFA.getInputAlphabet() do {
        newDFA
          .getStates()
          .foreach(
            { s =>
              newDFA
                .getSuccessors(s, sigma)
                .foreach({ sn =>
                  if !newDFA.isAccepting(sn) then {
                    newDFA.removeAllTransitions(s, sigma)
                    rm = true
                  }
                })
            }
          )
      }
    }
    newDFA
  }
}


extension(dfa : CompactDFA[?]){
  def toFastDFA = {
    val statesMap = HashMap((dfa.getInitialState(), FastDFAState(0,false)))
    val alphabet = dfa.getInputAlphabet()
    val newDFA =
     new FastDFA(alphabet)
    dfa
      .getStates()
      .foreach({ state =>
        statesMap.put(state, newDFA.addState(dfa.isAccepting(state)))
      })
    newDFA.setInitial(statesMap(dfa.getInitialState()), true)
    dfa
      .getStates()
      .foreach(
        { s =>
          for a <- alphabet do {
            dfa
              .getSuccessors(s, a)
              .foreach(
                { snext =>
                  newDFA.setTransition(statesMap(s), a, statesMap(snext))
                }
              )
          }
        }
      )
    newDFA
      .getStates()
      .filter(!newDFA.isAccepting(_))
      .foreach({ s =>
        newDFA.removeAllTransitions(s)
      })
    newDFA
  }
}
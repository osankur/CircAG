package fr.irisa.circag

import scala.collection.mutable.{Buffer, HashMap, ArrayBuffer}
import scala.collection.mutable.Queue
import scala.collection.immutable.Set
import scala.collection.immutable.StringOps
import collection.convert.ImplicitConversions._
import scala.sys.process._
import java.nio.file.Files
import java.io.ByteArrayInputStream
import java.io.PrintWriter
import dk.brics.automaton
import net.automatalib.brics.BricsNFA
import net.automatalib.automata.fsa.MutableDFA
import net.automatalib.automata.fsa.DFA;
import net.automatalib.automata.fsa.impl.compact.CompactDFA;
import net.automatalib.automata.fsa.impl.{FastDFA, FastNFA, FastDFAState, FastNFAState}
import net.automatalib.util.automata.fsa.{DFAs, NFAs}
import net.automatalib.automata.fsa.impl.compact.CompactDFA;
import net.automatalib.util.automata.builders.AutomatonBuilders;
import net.automatalib.visualization.Visualization;
import net.automatalib.words.impl.Alphabets;
import net.automatalib.automata.Automaton
import net.automatalib.automata.fsa.FiniteStateAcceptor
import net.automatalib.serialization.aut.AUTParser

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
import fr.irisa.circag.ltl.{LTL, MalformedLTL}
import scala.io.Source

type Symbol = String
type Alphabet = Set[Symbol]
type Trace = List[String]
type Lasso = (Trace, Trace)

/** @brief Deterministic or nondeterministic LTS used as assumptions and properties.
  *
  * @param name
  * @param dfa
  * @param alphabet
  */
trait LTS[S](
    val name: String,
    val dfa: FiniteStateAcceptor[S, String] with Automaton[S, String, S],
    val alphabet: Set[String]
) {
  var comments : String= ""
  def visualize() : Unit = {
    Visualization.visualize(dfa : Automaton[S, String, S], Alphabets.fromList(alphabet.toList))
  }
  def writeToFile(file : java.io.File) : Unit = {
    val lts = this
    new PrintWriter(file) { write(TA.fromLTS(lts).toString()); close }    
  }
}
case class DLTS(
    override val name: String,
    override val dfa: FastDFA[String],
    override val alphabet: Set[String]
) extends LTS[FastDFAState](name, dfa, alphabet)

case class NLTS(
    override val name: String,
    override val dfa: FastNFA[String],
    override val alphabet: Set[String]
) extends LTS[FastNFAState](name, dfa, alphabet)

object DLTS {

  /** @brief Given (dfa, alphabet), compute the lifting of the dfa to extendedAlphabet
    * by copying it and adding self-loops at all states on symbols in
    * extendedAlphabet \\ alphabet.
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
    return DLTS(name.getOrElse(dlts.name), liftedDFA, newAlphabet)
  }

  /** @brief Complete, lift to extendedAlphabet, and remove all transitions from
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
        liftedDLTS
    }
  }

  /** @brief Make straight-line DLTS reading a given trace, projected to
    * projectionAlphabet
    *
    * @param trace
    * @param projectionAlphabet
    * @return
    */
  def fromTrace(trace: Trace, traceAlphabet : Option[Alphabet] = None): DLTS = {
    require(trace.forall(p => p != ""))
    val alph = traceAlphabet.getOrElse(trace.toSet) | trace.toSet
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
    * Make a DLTS that reads a given lasso; and make the first state of the cycle accepting.
    *
    * @param lasso lasso
    * @param alphabet alphabet of the resulting automaton
    * @pre alphabet contains all symbols of lasso
    * @return
    */
  def fromLasso(lasso : Lasso, alphabet : Option[Alphabet] = None) : DLTS = {
    val prefix = lasso._1
    val cycle = lasso._2
    require(prefix.forall(p => p != ""))
    require(cycle.forall(p => p != ""))
    val occurringSymbols = prefix.toSet ++ cycle.toSet
    val givenAlphabet = alphabet.getOrElse(occurringSymbols)
    require{occurringSymbols.subsetOf(givenAlphabet)}
    val n = prefix.size + cycle.size
    val newDFA =
     new FastDFA(Alphabets.fromList(givenAlphabet.toList))
    val states = Buffer.tabulate(n){i => newDFA.addState(i == prefix.size)}
    newDFA.setAccepting(states(prefix.size), true)
    newDFA.setInitial(states(0), true)
    for (sigma, i) <- prefix.zipWithIndex do {
      newDFA.addTransition(states(i), sigma, states(i+1))
    }
    for (sigma, i) <- cycle.zipWithIndex do {
      newDFA.addTransition(
          states(prefix.size + i), 
          sigma, 
          states(prefix.size + ((i+1) % cycle.size))
        )
    }    
    DLTS("lasso", newDFA, givenAlphabet)
  }


  def fromErrorSymbol(symbol : Symbol, dltsName : String = "") : DLTS = {
    require(symbol != "")
    val alph = Alphabets.fromList(List(symbol))
    val errDFA = AutomatonBuilders
      .forDFA(FastDFA(alph))
      .withInitial("q0")
      .from("q0")
      .on(symbol)
      .to("q1")
      .withAccepting("q0")
      .create()
    DLTS(dltsName, errDFA, alph.toSet)
  }

  /**
    * @brief Build deterministic LTS from possbly non-deterministic HOA Buchi automaton description.
    *
    * @param automatonString
    * @param acceptingLabel
    * @return
    */
  def fromHOAString(automatonString : String, fullAlphabet : Option[Alphabet] = None) : DLTS = {
      val nlts = NLTS.fromHOA(automatonString, fullAlphabet : Option[Alphabet])
      DLTS(nlts.name, NFAs.determinize(nlts.dfa, nlts.dfa.getInputAlphabet()).toFastDFA, nlts.alphabet)
  }

  /**
    * @brief Build deterministic LTS from possbly non-deterministic HOA Buchi automaton description:
    *  this will be interpreted
    *
    * @param automatonString
    * @param acceptingLabel
    * @return
    */
  def fromHOAFile(file : java.io.File, fullAlphabet : Option[Alphabet] = None) : DLTS = {
    this.fromHOAString(scala.io.Source.fromFile(file).getLines().mkString("\n"), fullAlphabet)
  }

  def fromTCheckerFile(file : java.io.File) : DLTS = {
    val ta = TA.fromFile(file)
    if ta.syncs.length > 0 || ta.eventsOfProcesses.keys.size > 1 then {
      throw Exception("The DLTS parser only accepts single-process TA without synchronization labels")
    }    
    require(ta.alphabet.size > 0)
    val alphabet = ta.alphabet
    val statesMap = HashMap[String,FastDFAState]()
    val dfa = new FastDFA(Alphabets.fromList(alphabet.toList))

    val regProcess = "\\s*process:(.*)\\s*".r
    val regEdge = "\\s*edge:([^:]*):([^:]*):([^:]*):([^{:]*).*\\s*".r
    val regLocation = "\\s*location:([^:]*):([^{:]*).*\\s*".r
    val content = ta.core.split("\n")
    content.foreach( line =>
      line match {
        case regProcess(_) => ()
        case regEdge(pr, src, tgt, event) => ()
          // System.out.println(s"Edge ${pr} ${src} ${tgt} ${event}")
        case regLocation(pr, loc) => 
          // System.out.println(s" ${pr} ${loc} ")
          statesMap.put(loc, dfa.addState(true))
          if line.contains("initial:") then {
            dfa.setInitial(statesMap(loc), true)
          }
        case _ => ()
          // System.out.println(s"Cannot parse line: ${line}")
      }
    )
    content.foreach( line =>
      line match {
        case regProcess(_) => ()
        case regEdge(pr, src, tgt, event) =>
          if !alphabet.contains(event) then {
            throw Exception(s"DFA cannot silen transitions: $event")
          }
          dfa.addTransition(statesMap(src),event, statesMap(tgt))
        case regLocation(pr, loc) =>  ()
        case _ => ()
      }
    )
    DLTS(ta.systemName, dfa, alphabet)
  }

  /**
  * Create a regexp with the Brics library with the following syntactic sugar:
  * each event preceded by '@' is interpreted as an atomic letter.
  * Example: (~(.*@start1[^@end1]*@start1.*))&(~(.*@start2[^@end2]*@start2.*))
  *
  * @param name
  * @param regexp
  * @return
  */
  def fromRegExp(name : String, regexp : String ) : DLTS = {
    var currentChar = 'a'
    val names = HashMap[Character, String]()
    val identifierReg = ".*?@([a-zA-Z0-9]+).*".r

    var modifiedRegexp = regexp.replaceAll(" ", "")
    def addIdentifier() : Boolean = {
      modifiedRegexp match {
        case identifierReg(name) => 
          names.put(currentChar, name)
          modifiedRegexp = modifiedRegexp.replaceAllLiterally(s"@${name}", s"${currentChar}")
          currentChar = (Char.char2int(currentChar) + 1).toChar
          true
        case _ => 
          false
      }
    }
    while(addIdentifier()){}
    println(s"Modified regexp: ${modifiedRegexp}")
    val aut = BricsNFA(dk.brics.automaton.RegExp(modifiedRegexp).toAutomaton())
    val dfa = NFAs.determinize(aut, Alphabets.characters('A', 'z'))
    val alph = Alphabets.fromList(names.values.toList)

    // val localAlph = Alphabets.fromList()
    // Visualization.visualize(dfa,Alphabets.characters('a', 'b'))
    
    val newDFA = FastDFA(alph)
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
    DLTS(name, newDFA, alph.toSet)
  }

  /**
    * @brief Make the DFA prefix-closed by removing all transitions from non-accepting states;
    * and removing non-accepting states if removeNonAcceptingStates is true
    *
    * @param dfa
    * @param alphabet
    * @param removeNonAcceptingStates
    * @return
    */
  def makePrefixClosed(
      dfa: FastDFA[String],
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
                  newDFA.setTransition(statesMap(s), a, statesMap(snext))
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


extension(dfa : CompactDFA[String]){
  def toFastDFA = {
    val statesMap = HashMap((dfa.getInitialState(), FastDFAState(0,false)))
    val alphabet = dfa.getInputAlphabet()
    val newDFA =
     new FastDFA(alphabet)
    dfa
      .getStates()
      .foreach({ state =>
        val newstate = newDFA.addState(dfa.isAccepting(state))
        // System.out.println(newstate)
        statesMap.put(state, newstate)
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
  }
}

extension(lasso : Lasso){
  def filter(f : String => Boolean) : Lasso = {
    (lasso._1.filter(f), lasso._2.filter(f))
  }
  /**
    * Suffix obtained from lasso by dropping the prefix of length k
    *
    * @param k
    * @return
    */
  def suffix(k : Int) : Lasso = {
    require(k>=0)
    val (p,c) = lasso
    if k <= p.size then {
      (p.drop(k), c)
    } else {
      (List(), c.drop((k - p.size) % c.size))
    }
  }
  def size : Int = {
    lasso._1.size + lasso._2.size
  }
  /**
   * @brief Determine whether given two lassos represent the same omega-word 
   */
  def semanticEquals(lasso2 : Lasso) : Boolean = {
    def gcd(a: Int, b: Int): Int = b match {
      case 0 => a
      case n => gcd(b, a % b)
    }
    def powerOfList[A](l : List[A], k : Int) : List[A] = {
      var q = Queue[A]()
      for i <- 1 to k do {
        q ++= l
      }
      q.toList
    }
    var (p1,c1) = lasso
    var (p2,c2) = lasso2
    if p1.size != p2.size then {
      // switch them if needed to make sure p1.size < p2.size
      if (p1.size > p2.size) {
        val tmp_p = p1
        val tmp_c = c1
        p1 = p2
        c1 = c2
        p2 = tmp_p
        c2 = tmp_c
      }

      // replace p1 with p1 . c1^k . c1_{0..i}
      // replace c1 with c1_{i...c1.size} ++ c1_{0..i}
      val k = (p2.size - p1.size) / c1.size
      var q = Queue[String]()
      q ++= p1
      for _ <- 1 to k do {
        q ++= c1
      }
      val i = p2.size - q.size
      q ++= c1.slice(0, i)
      p1 = q.toList
      c1 = c1.slice(i, c1.size) ++ c1.slice(0, i) 

      assert(p1.size == p2.size)
      if p1 != p2 then
        return false      
    }
    val lcm = (c1.size * c2.size)  / gcd(c1.size, c2.size)
    val extended_c1 = powerOfList(c1, lcm / c1.size)
    val extended_c2 = powerOfList(c2, lcm / c2.size)
    extended_c1 == extended_c2
  }  
}

extension(dfa : FastDFA[String]){
  /**
    * Check if all states reachable from init are accepting
    *
    * @return
    */
  def isPrunedSafety : Boolean = {
    def isAllReachableAccepting(s: FastDFAState): Boolean = {
      val visited = Array.fill(dfa.size)(false)
      def dfs(s: FastDFAState): Boolean = {
        if !dfa.isAccepting(s) then {
          false
        } else if !visited(s.getId()) then {
          visited(s.getId()) = true
          // System.out.println(alphabet.toSeq.map(newDFA.getSuccessors(s, _)))
          dfa.getInputAlphabet().toSeq
            .map(dfa.getSuccessors(s, _).forall({ dfs(_) }))
            .forall({ x => x })
        } else {
          true
        }
      }
      dfs(s)
    }
    dfa.size == 0 || isAllReachableAccepting(dfa.getInitialState())
  }

  /**
    * Check if non-accepting states are traps (i.e. no accepting state is reachable)
    *
    * @return
    */
  def isSafety : Boolean = {
    def isAcceptingReachable(s: FastDFAState): Boolean = {
      val visited = Array.fill(dfa.size)(false)
      def checkAcceptingReachable(s: FastDFAState): Boolean = {
        if dfa.isAccepting(s) then {
          true
        } else if !visited(s.getId()) then {
          visited(s.getId()) = true
          // System.out.println(alphabet.toSeq.map(newDFA.getSuccessors(s, _)))
          dfa.getInputAlphabet().toSeq
            .map(dfa.getSuccessors(s, _).exists({ checkAcceptingReachable(_) }))
            .exists({ x => x })
        } else {
          false
        }
      }
      checkAcceptingReachable(s)
    }
    dfa.size == 0 || 
    dfa.getStates().filter(!dfa.isAccepting(_)).forall(!isAcceptingReachable(_))
  }

  /**
    * Copy the DFA by removing all non-accepting states and associated transitions
    *
    * @return non-complete DFA equivalent to given DFA with all states accepting
    */
  def pruned = {
    val statesMap = HashMap((dfa.getInitialState(), FastDFAState(0,false)))
    val alphabet = dfa.getInputAlphabet()
    val newDFA =
     new FastDFA(alphabet)
    if dfa.isAccepting(dfa.getInitialState()) then {
      dfa
        .getStates()
        .foreach({ state =>
          if dfa.isAccepting(state) then 
            statesMap.put(state, newDFA.addState(true))
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
                    if(dfa.isAccepting(s) && dfa.isAccepting(snext)) then
                      newDFA.setTransition(statesMap(s), a, statesMap(snext))
                  }
                )
            }
          }
        )
    }
    newDFA
  }
}

object NLTS {
  def copy(nlts : NLTS) : NLTS = {
    val dfa = nlts.dfa
    val statesMap = HashMap[FastNFAState,FastNFAState]()
    // val statesMap = HashMap((dfa.getInitialState(), FastNFAState(0,false)))
    val alphabet = dfa.getInputAlphabet()
    val newNFA = new FastNFA(alphabet)
    dfa
      .getStates()
      .foreach({ state =>
        val newstate = newNFA.addState(dfa.isAccepting(state))
        statesMap.put(state, newstate)
      })
    newNFA.getInitialStates().foreach(
      s => newNFA.setInitial(statesMap(s), true)
    )
    dfa
      .getStates()
      .foreach(
        { s =>
          for a <- alphabet do {
            dfa
              .getSuccessors(s, a)
              .foreach(
                { snext =>
                  newNFA.addTransition(statesMap(s), a, statesMap(snext))
                }
              )
          }
        }
      )
    NLTS(nlts.name, newNFA, nlts.alphabet)
  }
  def fromDLTS(dlts : DLTS) : NLTS = {
    val dfa = dlts.dfa
    val statesMap = HashMap((dfa.getInitialState(), FastNFAState(0,false)))
    val alphabet = dfa.getInputAlphabet()
    val newNFA = new FastNFA(alphabet)
    dfa
      .getStates()
      .foreach({ state =>
        val newstate = newNFA.addState(dfa.isAccepting(state))
        statesMap.put(state, newstate)
      })
    newNFA.setInitial(statesMap(dfa.getInitialState()), true)
    dfa
      .getStates()
      .foreach(
        { s =>
          for a <- alphabet do {
            dfa
              .getSuccessors(s, a)
              .foreach(
                { snext =>
                  newNFA.addTransition(statesMap(s), a, statesMap(snext))
                }
              )
          }
        }
      )
    NLTS(dlts.name, newNFA, dlts.alphabet)
  }

  def fromLTL(ltlString : String, fullAlphabet : Option[Alphabet]) : NLTS = {
    def printToFile(f: java.io.File)(op: java.io.PrintWriter => Unit) = {
      val p = new java.io.PrintWriter(f)
      try { op(p) } finally { p.close() }
    }    
    val tmpFile = Files.createTempFile("tmp", ".ltl").toFile()
    printToFile(tmpFile)({ (p : java.io.PrintWriter) => p.println(ltlString)})
    val output = StringBuffer()
    val proc = s"cat ${tmpFile.getAbsolutePath()}" #| "ltl2tgba -B -"
    if (proc.run(BasicIO(false,output,None)).exitValue != 0 ){
      throw (MalformedLTL(output.toString()))
    }
    fromHOA(output.toString(), fullAlphabet : Option[Alphabet])
  }

  /**
  * Build a NLTS from the string description of a Buchi automaton in the HOA format.
  * The HOA format has atomic predicates (AP), and the transitions are labeled by propositional formulas on AP.
  * We build here NLTS where each transition is labeled by a single symbol.
  * We thus enumerate all singular valuations, and keep only the transitions for these; moreover, for any transition
  * labeled by a valuation assigning false to all APs, we add transitions labeled by fullAlphabet \\ APs.
  *
  * @param automatonString description of the Buchi automaton in the HOA format
  * @param fullAlphabet the set of events on which to build the Buchi automaton; if None,
  * then the alphabet of NLTS is the set of symbols that appear in the automaton description.
  * @pre if fullAphabet is not None, then it contains all symbols that appear in the given automaton
  * @return
  */
  def fromHOA(automatonString : String, fullAlphabet : Option[Alphabet]) : NLTS = {
    val toVars = HashMap[Int, z3.BoolExpr]()
    val toSymbol = HashMap[z3.BoolExpr, Int]()
    val ctx = {
        val cfg = HashMap[String, String]()
        cfg.put("model", "true")
        z3.Context(cfg);
    }
    val solver = ctx.mkSolver()
    def varOfSymbol(symbol : Int) : z3.BoolExpr = {
        if toVars.contains(symbol) then {
            toVars(symbol)
        } else {
            val v = ctx.mkBoolConst(ctx.mkSymbol(symbol))
            toVars.put(symbol, v)
            toSymbol.put(v, symbol)
            v
        }
    }
    def toZ3(expr : BooleanExpression[AtomLabel]) : z3.BoolExpr = {
        expr.getType() match {
            case BooleanExpression.Type.EXP_TRUE => ctx.mkTrue()
            case BooleanExpression.Type.EXP_FALSE => ctx.mkFalse()
            case BooleanExpression.Type.EXP_ATOM => 
                varOfSymbol(expr.getAtom().getAPIndex())
            case BooleanExpression.Type.EXP_AND => 
                ctx.mkAnd(toZ3(expr.getLeft()), toZ3(expr.getRight()))
            case BooleanExpression.Type.EXP_OR => 
                ctx.mkOr(toZ3(expr.getLeft()), toZ3(expr.getRight()))
            case BooleanExpression.Type.EXP_NOT => 
                ctx.mkNot(toZ3(expr.getLeft()))
        }
    }
    // Register all APs and add pairwise disjointness constraint to solver
    def singletonValuations(expr : BooleanExpression[AtomLabel]) : Seq[Int] = {
        var constraints = toZ3(expr)
        var labels = Buffer[Int]()
        solver.push()
        solver.add(constraints)
        for (sigma, v) <- toVars do {
            solver.push()
            solver.add(v)
            if solver.check() == z3.Status.SATISFIABLE then {
                labels.append(sigma)
            }
            solver.pop()
        }
        solver.pop()
        labels.toSeq
    }
    // Determine whether the valuation false satisfies the expression
    def hasFalseValuation(expr : BooleanExpression[AtomLabel]) : Boolean = {
        solver.push()
        var exp = ctx.mkTrue()
        for (sigma, v) <- toVars do {
            solver.add(ctx.mkNot(v))
        }
        solver.add(toZ3(expr))
        val yes = solver.check() == z3.Status.SATISFIABLE
        solver.pop()
        yes
    }

    val autFactory = HOAConsumerStore()
    HOAFParser.parseHOA(new ByteArrayInputStream(automatonString.getBytes()), autFactory);
    val aut = autFactory.getStoredAutomaton()
    val header = aut.getStoredHeader()
    // Symbols of the given fullAlphabet that do not appear as APs in the HOA automaton
    val alphabet = header.getAPs().toBuffer
    val complementaryAlphabet = fullAlphabet match {
        case None => Set[String]()
        case Some(symbols) => 
            if symbols.containsAll(alphabet) then {
                  symbols.diff(alphabet.toSet)
            } else {
                throw Exception(s"Cannot build NLTS from HOA: Not all atomic predicates of HOA are contained in the given alphabet: ${header.getAPs()} not contained in ${symbols}")
            }
    }
    if(aut.hasEdgesImplicit()) then {
        throw Exception("Implicit edges are not accepted")
    }
    if(aut.hasUniversalBranching()) then {
        throw Exception("Universal branching is not accepted")
    }
    val accCondition = header.getAcceptanceCondition()
    if(accCondition.getType() != BooleanExpression.Type.EXP_ATOM ) then {
        throw Exception("Only Buchi acceptance is accepted")
    }
    if(accCondition.getAtom().getType() != AtomAcceptance.Type.TEMPORAL_INF) then{
        throw Exception("Only Buchi acceptance is accepted")
    }
    for (sigma,i) <- alphabet.zipWithIndex do {
        varOfSymbol(i)
    }
    for a <- 0 until header.getAPs().size
        b <- 0 until header.getAPs().size do {
            if a != b then {
                solver.add(ctx.mkAnd(ctx.mkNot(ctx.mkAnd(toVars(a), toVars(b)))))
            }
        }
        
    val nfaAlphabet = header.getAPs().toSet | complementaryAlphabet
    val nfa = FastNFA(Alphabets.fromList(nfaAlphabet.toList))
    val newStates = Buffer[FastNFAState]()
    for i <- 1 to aut.getNumberOfStates() do {
        newStates.append(nfa.addState())
    }
    header.getStartStates().foreach(_.foreach({ i => nfa.setInitial(newStates(i), true) }))
    for (s,i) <- newStates.zipWithIndex do {
        if(aut.getStoredState(i).getAccSignature() != null) then
            nfa.setAccepting(s, true)
        
        if (aut.getEdgesWithLabel(i) != null) then for edge <- aut.getEdgesWithLabel(i) do {
            assert(edge.getConjSuccessors().size == 1)
            val succ = edge.getConjSuccessors().head
            val labels = singletonValuations(edge.getLabelExpr())
            
            for sigma <- labels do {
                nfa.addTransition(s, alphabet(sigma).toString, newStates(succ))
            }                
            if (hasFalseValuation(edge.getLabelExpr())) then {
                for sigma <- complementaryAlphabet do {
                    nfa.addTransition(s, sigma, newStates(succ))
                }
            }
        }
    }
    val nlts = NLTS("_hoa_", nfa, nfa.getInputAlphabet().toSet)
    if header.getName() != null then 
      nlts.comments = header.getName()
    nlts
  }

  /**
    * Build a NLTS which recognizes traces that start with an arbitrary prefix, and then reads the given lasso.
    * The NFA is defined as the union of two parts. Either the lasso DFA, or another initial state with self-loops 
    * which can go to the initial state of the lasso dfa.
    * @param lasso
    * @param alphabet
    * @return
    */
  def fromLassoAsSuffix(lasso : Lasso, alphabet : Option[Alphabet] = None) : NLTS = {
    val nlts = NLTS.fromDLTS(DLTS.fromLasso(lasso, alphabet))
    assert(nlts.dfa.getInitialStates().size == 1)
    val lassoInit = nlts.dfa.getInitialStates().head // init state of the lasso. this remains initial
    val initState = nlts.dfa.addState(false) // new init state
    nlts.dfa.setInitial(initState, true)
    for sigma <- nlts.alphabet do {
      nlts.dfa.addTransition(
          initState,
          sigma, 
          initState
        )
      nlts.dfa.addTransition(
          initState,
          sigma, 
          lassoInit
        )
    }
    nlts
  }

}
package fr.irisa.circag.dfa

import collection.JavaConverters._
import collection.convert.ImplicitConversions._
import scala.collection.mutable
import scala.collection.mutable.{Buffer}

import org.slf4j.Logger
import org.slf4j.LoggerFactory

import de.learnlib.api.oracle.EquivalenceOracle
import de.learnlib.api.query.DefaultQuery;
import de.learnlib.api.oracle._
import de.learnlib.api.oracle.MembershipOracle
import de.learnlib.algorithms.rpni.BlueFringeRPNIDFA
import net.automatalib.automata.fsa.{DFA,NFA}
import net.automatalib.util.automata.fsa.{DFAs,NFAs}
import net.automatalib.words.impl.Alphabets;
import net.automatalib.words.Word
import net.automatalib.automata.fsa.impl.compact.CompactDFA;
import net.automatalib.util.automata.builders.AutomatonBuilders;
import net.automatalib.automata.fsa.impl.{
  FastDFA,
  FastNFA,
  FastDFAState,
  FastNFAState
}

import com.microsoft.z3

import fr.irisa.circag.{Trace, DLTS, Alphabet}
import fr.irisa.circag.pruned
import fr.irisa.circag.toFastDFA
import fr.irisa.circag.statistics

/** Algorithm to be used to learn DFA.
  */
enum DFALearningAlgorithm:
  case RPNI
  case SAT
  case UFSAT
  case JointSAT

trait DFALearner(name: String, alphabet: Alphabet) {
  def setPositiveSamples(samples: Set[Trace]) = {
    if positiveSamples != samples then {
      positiveSamples = samples
      dlts = None
    }
  }
  def setNegativeSamples(samples: Set[Trace]) = {
    if negativeSamples != samples then {
      negativeSamples = samples
      dlts = None
    }
  }
  def getDLTS(): DLTS
  protected var dlts: Option[DLTS] = None
  protected var positiveSamples: Set[Trace] = Set(List())
  protected var negativeSamples: Set[Trace] = Set()
}

class RPNILearner(name: String, alphabet: Alphabet)
    extends DFALearner(name, alphabet) {
  override def getDLTS(): DLTS = {
    this.dlts match {
      case Some(d) => d
      case None =>
        statistics.Counters.incrementCounter("RPNI-Learner")
        val learner = BlueFringeRPNIDFA(Alphabets.fromList(alphabet.toList))
        learner.addPositiveSamples(positiveSamples.map(Word.fromList(_)))
        learner.addNegativeSamples(negativeSamples.map(Word.fromList(_)))
        var beginTime = System.nanoTime()
        val initialModel = learner.computeModel() match {
          case cdfa: CompactDFA[String] => cdfa
          case _ => throw Exception("I can only work with CompactDFA")
        }
        statistics.Timers.incrementTimer(
          "rpni-learner",
          System.nanoTime() - beginTime
        )
        val dlts = DLTS(
          name,
          dfa = DLTS.makePrefixClosed(
            initialModel.toFastDFA,
            alphabet,
            removeNonAcceptingStates = true
          ),
          alphabet = alphabet
        )
        this.dlts = Some(dlts)
        // System.out.println(s"Alphabet: ${dlts.alphabet}")
        // System.out.println(s"Pos:${positiveSamples}")
        // System.out.println(s"Neg:${negativeSamples}")
        // dlts.visualize()
        dlts
    }

  }
}

/** Passive learning of DFAs with a SAT encoding using an uninterpreted function
  * to encode the transition relation.
  *
  * @param name
  *   name of the DLTS to be learned
  * @param alphabet
  *   alphabet of the DLTS
  */
class UFSATLearner(name: String, alphabet: Alphabet)
    extends DFALearner(name, alphabet) {
  val ctx = {
    val cfg = mutable.HashMap[String, String]()
    cfg.put("model", "true");
    z3.Context(cfg);
  }
  val solver = ctx.mkSolver()

  /** Learn a prefix-closed complete deterministic finite automaton satisfying
    * the positive and negative samples
    * @return
    *   the said DLTS
    */
  def computeDLTS(): DLTS = {
    var dfaSize = 2
    var satisfiable = false
    val listAlphabet = alphabet.toList
    val alphabetMap = mutable.HashMap[String, Int]()
    listAlphabet.zipWithIndex.foreach(alphabetMap.put)
    var dlts: Option[DLTS] = None
    while (!satisfiable) do {
      solver.reset()
      val qNames = Array.tabulate(dfaSize)({ i => s"q${i}" })
      val qSort = ctx.mkEnumSort("Q", qNames: _*);
      val qConsts = (0 until dfaSize).map { i => qSort.getConst(i) }
      val alphaSort = ctx.mkEnumSort("A", listAlphabet: _*)
      val alphaConsts = (0 until alphabet.size).map { i =>
        alphaSort.getConst(i)
      }
      val transDomain = Array[z3.Sort](qSort, alphaSort)
      val trans = ctx.mkFuncDecl("trans", transDomain, qSort)
      // qConsts(0) is initial and accepting
      // qConsts(-1) is rejecting, and all others are accepting
      val rejState = qConsts.last
      val initState = qConsts(0)
      // Make rejState absorbing:
      for alpha <- alphaConsts do {
        solver.add(ctx.mkEq(rejState, ctx.mkApp(trans, rejState, alpha)))
      }
      for (trace, itrace) <- positiveSamples.zipWithIndex do {
        val q = (0 to trace.size).map { i =>
          ctx.mkConst(s"p_trace_${itrace}_${i}", qSort)
        }
        solver.add(ctx.mkEq(initState, q(0)))
        for (alpha, i) <- trace.zipWithIndex do {
          solver.add(
            ctx.mkEq(
              q(i + 1),
              ctx.mkApp(trans, q(i), alphaConsts(alphabetMap(alpha)))
            )
          )
        }
        solver.add(ctx.mkNot(ctx.mkEq(q.last, rejState)))
      }

      for (trace, itrace) <- negativeSamples.zipWithIndex do {
        val q = (0 to trace.size).map { i =>
          ctx.mkConst(s"n_trace_${itrace}_${i}", qSort)
        }
        solver.add(ctx.mkEq(initState, q(0)))
        for (alpha, i) <- trace.zipWithIndex do {
          solver.add(
            ctx.mkEq(
              q(i + 1),
              ctx.mkApp(trans, q(i), alphaConsts(alphabetMap(alpha)))
            )
          )
        }
        solver.add(ctx.mkEq(q.last, rejState))
      }

      satisfiable = solver.check() == z3.Status.SATISFIABLE
      if (!satisfiable) then {
        dfaSize += 2
      } else {
        val m = solver.getModel()
        val newDFA =
          new FastDFA(Alphabets.fromList(listAlphabet))
        val states =
          (0 until dfaSize).map(i => newDFA.addState(i < dfaSize - 1))
        newDFA.setInitial(states(0), true)
        for s <- 0 until dfaSize do {
          for alpha <- listAlphabet do {
            val snext = m.eval(
              ctx.mkApp(trans, qConsts(s), alphaConsts(alphabetMap(alpha))),
              true
            )
            for t <- 0 until dfaSize do {
              if (qConsts(t) == snext) then {
                newDFA.setTransition(states(s), alpha, states(t))
              }
            }
          }
        }
        dlts = Some(DLTS(name, newDFA.pruned, alphabet))
      }
    }
    dlts.getOrElse(throw Exception("No DLTS"))
  }
  override def getDLTS(): DLTS = {
    this.dlts match {
      case Some(d) => d
      case None =>
        statistics.Counters.incrementCounter("SAT-Learner")
        var beginTime = System.nanoTime()
        this.dlts = Some(computeDLTS())
        statistics.Timers.incrementTimer(
          "sat-learner",
          System.nanoTime() - beginTime
        )
        getDLTS()
    }
  }
}

class SATLearner(name: String, alphabet: Alphabet)
    extends DFALearner(name, alphabet) {
  val ctx = {
    val cfg = mutable.HashMap[String, String]()
    cfg.put("model", "true");
    z3.Context(cfg);
  }
  val solver = ctx.mkSolver()

  /** Learn a prefix-closed complete deterministic finite automaton satisfying
    * the positive and negative samples
    * @return
    *   the said DLTS
    */
  def computeDLTS(): DLTS = {
    var dfaSize = 2
    var satisfiable = false
    val listAlphabet = alphabet.toList
    val alphabetMap = mutable.HashMap[String, Int]()
    listAlphabet.zipWithIndex.foreach(alphabetMap.put)
    var dlts: Option[DLTS] = None
    while (!satisfiable) do {
      solver.reset()
      val trans =
        Buffer.tabulate(dfaSize)({ s =>
          Buffer.tabulate(alphabet.size)({ a =>
            Buffer.tabulate(dfaSize)({ t =>
              ctx.mkBoolConst(s"trans_${s}_${a}_${t}")
            })
          })
        })
      for s <- 0 until dfaSize do {
        for a <- 0 until alphabet.size do {
          // Each trans(s)(a) has a successor
          solver.add(trans(s)(a).fold(ctx.mkFalse)({ (c, x) =>
            ctx.mkOr(c, x)
          }))
          // It has at most one successor
          (0 until dfaSize).foreach({ t =>
            solver.add(
              ctx.mkImplies(
                trans(s)(a)(t),
                ctx.mkAnd(
                  (0 until dfaSize).toSet
                    .diff(Set(t))
                    .map(trans(s)(a))
                    .map(ctx.mkNot)
                    .toList: _*
                )
              )
            )
          })
        }
      }
      // 0 is initial
      // dfaSize-1 is rejecting, and all others are accepting
      val rejState = dfaSize - 1
      // Make rejState absorbing:
      for alpha <- 0 until alphabet.size do {
        solver.add(trans(rejState)(alpha)(rejState))
      }
      // Encode executions on samples
      val samples = positiveSamples.zipWithIndex.map(x => (true, x))
        ++ negativeSamples.zipWithIndex.map(x => (false, x))
      for (isPositive, (trace, itrace)) <- samples do {
        val q = (0 to trace.size).map { i =>
          Buffer.tabulate(dfaSize)({ s =>
            ctx.mkBoolConst(s"${isPositive}_trace_${itrace}_step${i}_state${s}")
          })
        }
        // Exactly one state is true at each step
        for i <- 0 to trace.size do {
          for s <- 0 until dfaSize do {
            solver.add(
              ctx.mkImplies(
                q(i)(s),
                ctx.mkAnd(
                  (0 until dfaSize).toSet
                    .diff(Set(s))
                    .map(q(i))
                    .map(ctx.mkNot)
                    .toList: _*
                )
              )
            )
            solver.add(
              ctx.mkOr(
                q(i).toSeq: _*
              )
            )
          }
        }
        // Init state is 0
        solver.add(q(0)(0))
        // Exec satisfies transition relation
        for (alpha, i) <- trace.zipWithIndex do {
          for s <- 0 until dfaSize do {
            for t <- 0 until dfaSize do {
              solver.add(
                ctx.mkImplies(
                  ctx.mkAnd(q(i)(s), q(i + 1)(t)),
                  trans(s)(alphabetMap(alpha))(t)
                )
              )
            }
          }
        }
        if isPositive then solver.add(ctx.mkNot(q(trace.size)(rejState)))
        else solver.add(q(trace.size)(rejState))
      }

      satisfiable = solver.check() == z3.Status.SATISFIABLE
      if (!satisfiable) then {
        dfaSize += 2
      } else {
        val m = solver.getModel()
        val newDFA =
          new FastDFA(Alphabets.fromList(listAlphabet))
        val states =
          (0 until dfaSize).map(i => newDFA.addState(i < dfaSize - 1))
        newDFA.setInitial(states(0), true)
        for s <- 0 until dfaSize do {
          for alpha <- listAlphabet do {
            for t <- 0 until dfaSize do {
              m.evaluate(trans(s)(alphabetMap(alpha))(t), true)
                .getBoolValue() match {
                case z3.enumerations.Z3_lbool.Z3_L_TRUE =>
                  newDFA.setTransition(states(s), alpha, states(t))
                case _ => ()
              }
            }
          }
        }
        dlts = Some(DLTS(name, newDFA.pruned, alphabet))
      }
    }
    dlts.getOrElse(throw Exception("No DLTS"))
  }
  override def getDLTS(): DLTS = {
    this.dlts match {
      case Some(d) => d
      case None =>
        statistics.Counters.incrementCounter("SAT-Learner")
        var beginTime = System.nanoTime()
        this.dlts = Some(computeDLTS())
        statistics.Timers.incrementTimer(
          "sat-learner",
          System.nanoTime() - beginTime
        )
        val dlts = getDLTS()
        // System.out.println(s"Pos:${positiveSamples}")
        // System.out.println(s"Neg:${negativeSamples}")
        // dlts.visualize()
        // this.positiveSamples.foreach(
        //   tr => if !(dlts.dfa.accepts(tr)) then {
        //     System.out.println(s"Pos not accepted:${tr}")
        //     System.out.println(s"Pos:${positiveSamples}")
        //     System.out.println(s"Neg:${negativeSamples}")
        //     dlts.visualize()
        //     throw Exception("")
        //   }
        // )
        // this.negativeSamples.foreach(tr =>
        //   if dlts.dfa.accepts(tr) then {
        //     System.out.println(s"Neg:${tr}")
        //     System.out.println(s"Pos:${positiveSamples}")
        //     System.out.println(s"Neg:${negativeSamples}")
        //     dlts.visualize()
        //     throw Exception("")
        //   }
        // )
        dlts
    }
  }
}

abstract class JointSATLearner(name: String, alphabet: Alphabet)
    extends DFALearner(name, alphabet) {}


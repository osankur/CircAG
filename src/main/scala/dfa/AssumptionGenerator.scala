package fr.irisa.circag.tchecker.dfa

import java.util.HashMap
import scala.collection.mutable.Buffer
import scala.collection.immutable.Set
import collection.JavaConverters._
import collection.convert.ImplicitConversions._

import io.AnsiColor._


import net.automatalib.serialization.dot.GraphDOT

import net.automatalib.automata.fsa.impl.{FastDFA, FastNFA, FastDFAState, FastNFAState}

import de.learnlib.api.oracle.EquivalenceOracle
import de.learnlib.api.query.DefaultQuery;
import de.learnlib.api.oracle._
import de.learnlib.api.oracle.MembershipOracle
import de.learnlib.algorithms.rpni.BlueFringeRPNIDFA
import net.automatalib.automata.fsa.impl.compact.CompactDFA;
import net.automatalib.util.automata.builders.AutomatonBuilders;
import net.automatalib.automata.fsa.DFA
import net.automatalib.util.automata.fsa.NFAs
import net.automatalib.automata.fsa.NFA
import net.automatalib.util.automata.fsa.DFAs
import net.automatalib.words.impl.Alphabets;
import net.automatalib.words._
import net.automatalib.util.automata.builders.AutomatonBuilders;
import net.automatalib.visualization.Visualization;
import net.automatalib.automata.fsa.impl.compact.CompactNFA;
import net.automatalib.serialization.aut.AUTSerializationProvider 
import net.automatalib.automata.fsa.NFA

import com.microsoft.z3

import fr.irisa.circag.statistics
import fr.irisa.circag.configuration
import fr.irisa.circag.{Trace, DLTS, Alphabet}
import scala.collection.mutable

trait DFALearner(name : String, alphabet : Alphabet) {
  def setPositiveSamples(samples : Set[Trace]) = {
    if positiveSamples != samples then {
      positiveSamples = samples
      dlts = None
    }
  }
  def setNegativeSamples(samples : Set[Trace]) = {
    if negativeSamples != samples then {
      negativeSamples = samples
      dlts = None
    }
  }
  def getDLTS() : DLTS 
  protected var dlts : Option[DLTS] = None
  protected var positiveSamples : Set[Trace] = Set()
  protected var negativeSamples : Set[Trace] = Set()
}

class RPNILearner(name : String, alphabet : Alphabet) extends DFALearner(name, alphabet) {
  override def getDLTS(): DLTS = {
    this.dlts match {
      case Some(d) => d
      case None =>
        statistics.Counters.incrementCounter("RPNI")
        val learner = BlueFringeRPNIDFA(Alphabets.fromList(alphabet.toList))
        learner.addPositiveSamples(positiveSamples.map(Word.fromList(_)))
        learner.addNegativeSamples(negativeSamples.map(Word.fromList(_)))
        var beginTime = System.nanoTime()
        val initialModel = learner.computeModel()
        statistics.Timers.incrementTimer("rpni", System.nanoTime() - beginTime)
        val dlts = DLTS(
              name,
              dfa = DLTS.makePrefixClosed(initialModel, alphabet, removeNonAcceptingStates = true),
              alphabet = alphabet
          )
        this.dlts = Some(dlts)
        dlts
    }

  }
}

class SATLearner(name : String, alphabet : Alphabet) extends DFALearner(name, alphabet) {
  val ctx = {
    val cfg = HashMap[String, String]()
    cfg.put("model", "true");
    z3.Context(cfg);
  }
  val solver = ctx.mkSolver()

  def computeDLTS() : DLTS = {
    var dfaSize = 2
    var satisfiable = false
    val listAlphabet = alphabet.toList
    val alphabetMap = mutable.HashMap[String,Int]()
    listAlphabet.zipWithIndex.foreach(alphabetMap.put)
    var dlts : Option[DLTS] = None
    while (!satisfiable) do {
      solver.reset()
      val qNames = Array.tabulate(dfaSize)({i => s"q${i}"})
      val qSort = ctx.mkEnumSort("Q", qNames : _*);
      val qConsts = (0 until dfaSize).map{i => qSort.getConst(i)}
      val alphaSort = ctx.mkEnumSort("A", listAlphabet : _*)
      val alphaConsts = (0 until alphabet.size).map{i => alphaSort.getConst(i)}
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
      for (trace,itrace) <- positiveSamples.zipWithIndex do {
        val q = (0 to trace.size).map{i => ctx.mkConst(s"p_trace_${itrace}_${i}", qSort)}
        solver.add(ctx.mkEq(initState, q(0)))
        for (alpha, i) <- trace.zipWithIndex do {
          solver.add(ctx.mkEq(q(i+1), ctx.mkApp(trans, q(i), alphaConsts(alphabetMap(alpha)))))
        }
        solver.add(ctx.mkNot(ctx.mkEq(q.last, rejState)))
      }

      for (trace,itrace) <- negativeSamples.zipWithIndex do {
        val q = (0 to trace.size).map{i => ctx.mkConst(s"n_trace_${itrace}_${i}", qSort)}
        solver.add(ctx.mkEq(initState, q(0)))
        for (alpha, i) <- trace.zipWithIndex do {
          solver.add(ctx.mkEq(q(i+1), ctx.mkApp(trans, q(i), alphaConsts(alphabetMap(alpha)))))
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
        val states = (0 until dfaSize).map(i => newDFA.addState(i < dfaSize-1))
        newDFA.setInitial(states(0), true)
        for s <- 0 until dfaSize do {
          for alpha <- listAlphabet do {
            val snext = m.eval(ctx.mkApp(trans, qConsts(s), alphaConsts(alphabetMap(alpha))), true)
            for t <- 0 until dfaSize do {
              if (qConsts(t) == snext) then {
                newDFA.setTransition(states(s), alpha, states(t))
              }
            }
          }
        }
        dlts = Some(DLTS(name, newDFA, alphabet))
      }
    }
    dlts.getOrElse(throw Exception("No DLTS"))
  }
  override def getDLTS(): DLTS = {
    this.dlts match {
      case Some(d) => d
      case None =>
        this.dlts = Some(computeDLTS())
        getDLTS()
    }
  }
}

abstract class JointSATLearner(name : String, alphabet : Alphabet) extends DFALearner(name, alphabet) {
}

/**
  * Manages constraints and generates satisfying valuations.
  * Each atomic predicate is a pair (pr, trace) where pr is a process number, and trace is a trace 
  * with arbitrary symbols (not necessarily in the alphabet of pr).
  * 
  * @param processDependencies
  * @param propertyDependencies
  * @param assumptionAlphabets
  */
trait ConstraintManager(proofSkeleton : AGProofSkeleton, assumptionGeneratorType : AssumptionGeneratorType = AssumptionGeneratorType.RPNI) {
  val z3ctx = {
    val cfg = HashMap[String, String]()
    cfg.put("model", "true")
    z3.Context(cfg);
  }

  private val nbProcesses = proofSkeleton.nbProcesses
  
  // Set of all samples added so far
  val samples = Buffer.tabulate(nbProcesses)({_ => Buffer[(Trace,z3.BoolExpr)]()})
  // Boolean variable corresponding to each pair (pr,trace)
  private val toVars = HashMap[(Int,Trace), z3.BoolExpr]()
  private val toIndexedTraces = HashMap[z3.BoolExpr, (Int,Trace)]()
  // Those traces that can be kept when alphabet extends
  val incrementalTraces = Buffer[(Int, Trace, Int)]()

  // The constraint and theoryConstraints are kept for debugging and display. Invariant: solver contains these as assertions
  private var constraint = z3ctx.mkTrue()
  private var theoryConstraints = z3ctx.mkTrue()
  private var solver = z3ctx.mkSolver()

  // Samples that were used to compute assumptions the last time. Here the prefix closure of the positive samples were added
  private var positiveSamples = Buffer.tabulate(nbProcesses)({_ => Set[Trace]()})
  private var negativeSamples = Buffer.tabulate(nbProcesses)({_ => Set[Trace]()})
  // The above samples were based on this valuation
  private var previousValuation = HashMap[z3.BoolExpr,Boolean]()

  this.reset()

  /**
    * Return the unique SAT variable to the given pair (process, trace)
    *
    * @param process
    * @param trace
    * @return
    */
  private def varOfIndexedTrace(process : Int, trace : Trace) : z3.BoolExpr = {
    if (toVars.contains((process, trace))) then {
      toVars((process, trace))
    } else {
      val v = z3ctx.mkBoolConst(z3ctx.mkSymbol(s"${(process,trace)}"))
      toVars.put((process,trace), v)
      toIndexedTraces.put(v, (process, trace))
      samples(process).append((trace,v))
      updateTheoryConstraints(process, samples(process).size-1)
      v
    }
  }
  private def checkPrefixIndependance(pos : Set[Trace], neg : Set[Trace]) : Unit =  {
    for p <- pos do {
      for n <- neg do {
        if (p.startsWith(neg)) then {
          throw Exception(s"pos: ${p}, neg: ${n}")
        }
      }
    }
  }
  def addConstraint(process : Int, trace : Trace, constraintType : Int) : Unit = {
    constraintType match {
      case 34 =>
        assert(trace.size > 0)
        val prefix = trace.dropRight(1)
        val lhs = 
          if prefix.size > 0 then
            proofSkeleton.processDependencies(process).map(
            {
              j => z3ctx.mkNot(varOfIndexedTrace(j, prefix))
            }).toSeq
          else {
            Seq(z3ctx.mkFalse())
          }

        val newConstr = z3ctx.mkOr(
            z3ctx.mkOr(lhs : _*),
            varOfIndexedTrace(process, trace))
        if configuration.get().verbose then {
          System.out.println(s"New constraint ${newConstr}")
        }
        // constraint = z3ctx.mkAnd(constraint, newConstr)
        solver.add(newConstr)
        incrementalTraces.append((process, trace, constraintType))
      case 22 =>
        val prefix = trace.dropRight(1)
        val term1 = 
          z3ctx.mkOr(
            proofSkeleton.processDependencies(process).map(
            {
              j => z3ctx.mkNot(varOfIndexedTrace(j, prefix))
            }).toSeq : _*
          )
        val term2 = 
          z3ctx.mkAnd(
            varOfIndexedTrace(process, trace),
            z3ctx.mkOr(
              (proofSkeleton.propertyDependencies - process).map(
              {
                j => z3ctx.mkNot(varOfIndexedTrace(j, trace))
              }).toSeq : _*
            )
          )
        val newConstr = z3ctx.mkOr(term1, term2)
        // constraint = z3ctx.mkAnd(constraint, newConstr)
        solver.add(newConstr)
        if configuration.get().verbose then 
          System.out.println(s"Adding ${newConstr}")
        incrementalTraces.append((process, trace, constraintType))
      case 29 =>
        val prefix = trace.dropRight(1)
        val term1 = 
          z3ctx.mkOr(
            proofSkeleton.processDependencies(process).map(
            {
              j => z3ctx.mkNot(varOfIndexedTrace(j, prefix))
            }).toSeq : _*
          )
        val term2 = 
          z3ctx.mkAnd(
            varOfIndexedTrace(process, trace),
            z3ctx.mkOr(
              (proofSkeleton.propertyDependencies -- proofSkeleton.processDependencies(process) - process).map(
              {
                j => z3ctx.mkNot(varOfIndexedTrace(j, trace))
              }).toSeq : _*
            )
          )
        if configuration.get().verbose then 
          System.out.println(s"Adding ${z3ctx.mkOr(term1, term2)}")
        val newConstraint = z3ctx.mkOr(term1, term2)
        // constraint = z3ctx.mkAnd(constraint, newConstraint)
        solver.add(newConstraint)
        incrementalTraces.append((process, trace, constraintType))
    }
  }

  def addFinalPremiseConstraint(trace : Trace) : Unit = {
    val newConstraint = z3ctx.mkOr(
        z3ctx.mkOr(proofSkeleton.propertyDependencies.map({j => z3ctx.mkNot(varOfIndexedTrace(j, trace))}).toSeq : _*)
      )
    if configuration.get().verbose then {            
      System.out.println(s"Adding constraint ${newConstraint}")
    }
    constraint = z3ctx.mkAnd(constraint, newConstraint)
    solver.add(newConstraint)
  }

  /**
    * Reinitialize the solver. Resets the constraints but keeps those coming from incremental traces
    *
    * @param processDependencies
    * @param propertyDependencies
    * @param assumptionAlphabets
    */
  def reset() : Unit = {
    this.constraint = z3ctx.mkTrue()
    this.theoryConstraints = z3ctx.mkTrue()
    this.solver = z3ctx.mkSolver()
    this.samples.foreach(_.clear())
    this.toVars.clear()
    this.toIndexedTraces.clear()

    // the empty word must be accepted by all  
    constraint = z3ctx.mkAnd((0 until nbProcesses).map({i => varOfIndexedTrace(i, List[String]())}) : _*)
    solver.add(constraint)

    // incrementalTraces.foreach({ tr => addConstraint(tr._1, tr._2, tr._3)})
    // (0 until nbProcesses).foreach({i => updateTheoryConstraints(i)})
    this.positiveSamples = Buffer.tabulate(nbProcesses)({_ => Set[Trace]()})
    this.negativeSamples = Buffer.tabulate(nbProcesses)({_ => Set[Trace]()})
  }

  /**
    * Check if the current constraints are compatible with exp (still sat)
    *
    * @param exp
    */
  def checkValuation(exp : z3.BoolExpr) : Unit = {
    val s = z3ctx.mkSolver()
    s.add(constraint)
    s.add(theoryConstraints)
    s.add(exp)
    assert(solver.check() == z3.Status.SATISFIABLE)
  }
  def generateSamples() : Option[(Buffer[Set[Trace]], Buffer[Set[Trace]])] = {
    var positiveSamples = Buffer.tabulate(nbProcesses)({_ => collection.immutable.Set[Trace]()})
    var negativeSamples = Buffer.tabulate(nbProcesses)({_ => Set[Trace]()})
    var beginTime = System.nanoTime()
    if(solver.check() == z3.Status.UNSATISFIABLE){
      statistics.Timers.incrementTimer("z3", (System.nanoTime() - beginTime))
      None
    } else {
      val m = solver.getModel()
      // Compute sets of negative samples, and prefix-closed sets of pos samples from the valuation
      samples.zipWithIndex.foreach({
        (isamples, i) => 
          isamples.foreach({
            (trace, v) =>
              m.evaluate(v, true).getBoolValue() match {
                case z3.enumerations.Z3_lbool.Z3_L_TRUE =>
                  val sample = trace.filter(proofSkeleton.assumptionAlphabets(i))
                  // Add all prefixes
                  for k <- 0 to sample.size do {
                    positiveSamples(i) = positiveSamples(i).incl(sample.dropRight(k))
                  }
                case z3.enumerations.Z3_lbool.Z3_L_FALSE => 
                  negativeSamples(i) = negativeSamples(i).incl(trace.filter(proofSkeleton.assumptionAlphabets(i)))
                case _ =>
                  val sample = trace.filter(proofSkeleton.assumptionAlphabets(i))
                  // Add all prefixes
                  for k <- 0 to sample.size do {
                    positiveSamples(i) = positiveSamples(i).incl(sample.dropRight(k))
                  }
              }
          })
      })
      statistics.Timers.incrementTimer("z3", (System.nanoTime() - beginTime))
      Some(positiveSamples, negativeSamples)
    }
  }
  /**
    * Compute boolean expression with the following property:
    * For each pair of traces w, w', if proj(w, alphabet) is a prefix of proj(w', alphabet),
    * then var(w') -> var(w).
    * Here w ranges over samples(process)(sampleIndex..) and w' ranges over samples(process)(sampleIndex-1)
    *
    * @param process
    * @param alphabet
    * @return
    */
  private def updateTheoryConstraints(process : Int, sampleIndex : Int = 0) : Unit = {
    for i <- sampleIndex until samples(process).size do {
      val projTrace_i = this.samples(process)(i)._1.filter(proofSkeleton.assumptionAlphabets(process).contains(_))
      val vi = this.samples(process)(i)._2
      for j <- 0 until i do {
        val projTrace_j = this.samples(process)(j)._1.filter(proofSkeleton.assumptionAlphabets(process).contains(_))
        val vj = this.samples(process)(j)._2
        // System.out.println(s"VERSUS ${samples(process)(i)._1} - ${samples(process)(j)._1}")
        // System.out.println(s"PROJ VERSUS ${projTrace_i} - ${projTrace_j}")

        if projTrace_i.startsWith(projTrace_j) then{
          theoryConstraints = z3ctx.mkAnd(theoryConstraints, z3ctx.mkImplies(vi, vj))
          solver.add(z3ctx.mkImplies(vi, vj))
          // System.out.println(s"\t $projTrace_i -> $projTrace_j ")
          // System.out.println(s"\t $vi -> $vj ")
        }
        if projTrace_j.startsWith(projTrace_i) then{
          theoryConstraints = z3ctx.mkAnd(theoryConstraints, z3ctx.mkImplies(vj, vi))
          solver.add(z3ctx.mkImplies(vj, vi))
          // System.out.println(s"\t $projTrace_i <- $projTrace_j ")
          // System.out.println(s"\t   $vi <- $vj  ")
        }
      }
    }
  }

 
  def generateAssumptions() : Option[Buffer[DLTS]]
}

class RPNIGenerator(proofSkeleton : AGProofSkeleton, incrementalTraces : Option[Buffer[(Int, Trace, Int)]] = None) extends ConstraintManager(proofSkeleton) {
  val learners = Buffer.tabulate(proofSkeleton.nbProcesses)(i => RPNILearner(s"assumption_${i}", proofSkeleton.assumptionAlphabets(i)))
  incrementalTraces match {
    case Some(traces) =>
      traces.foreach({ tr => this.addConstraint(tr._1, tr._2, tr._3)})
    case _ => ()
  }
  
  def generateAssumptions() : Option[Buffer[DLTS]] = {
    generateSamples() match {
      case None => None // Unsat
      case Some(posSamples, negSamples) =>
        Some(Buffer.tabulate(proofSkeleton.nbProcesses)
          (i => 
            learners(i).setPositiveSamples(posSamples(i))
            learners(i).setNegativeSamples(negSamples(i))
            learners(i).getDLTS()
          )
        )
    }
  }
}

enum AssumptionGeneratorType:
  case RPNI
  case SAT
  case JointSAT

object ConstraintManager {
  def getAssumptionGenerator(proofSkeleton : AGProofSkeleton, t : AssumptionGeneratorType, incrementalTraces : Option[Buffer[(Int, Trace, Int)]] = None ) : ConstraintManager = {
    t match {
      case AssumptionGeneratorType.RPNI => 
        incrementalTraces match {
          case None => RPNIGenerator(proofSkeleton)
          case Some(tr) => RPNIGenerator(proofSkeleton, incrementalTraces)
        }
      case _ => throw Exception("Unsupported assumption generator")
    }
  }
}

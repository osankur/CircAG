package fr.irisa.circag.tchecker.dfa

import java.util.HashMap
import scala.collection.mutable.Buffer
import scala.collection.mutable
import collection.JavaConverters._
import collection.convert.ImplicitConversions._

import io.AnsiColor._


import net.automatalib.serialization.dot.GraphDOT


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
import fr.irisa.circag.Trace
import fr.irisa.circag.DLTS

/**
  * Manages constraints and generates satisfying valuations.
  * Each atomic predicate is a pair (pr, trace) where pr is a process number, and trace is a trace 
  * with arbitrary symbols (not necessarily in the alphabet of pr).
  * 
  * @param processDependencies
  * @param propertyDependencies
  * @param assumptionAlphabets
  */
class ConstraintManager(proofSkeleton : AGProofSkeleton){

  val z3ctx = {
    val cfg = HashMap[String, String]()
    cfg.put("model", "true")
    z3.Context(cfg);
  }

  private val nbProcesses = proofSkeleton.processDependencies.size
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
  private var positiveSamples = Buffer.tabulate(nbProcesses)({_ => mutable.Set[Trace]()})
  private var negativeSamples = Buffer.tabulate(nbProcesses)({_ => mutable.Set[Trace]()})
  // The above samples were based on this valuation
  private var previousValuation = HashMap[z3.BoolExpr,Boolean]()

  this.reset()

  def this(proofSkeleton : AGProofSkeleton, incrementalTraces : Buffer[(Int, Trace, Int)]) = {
    this(proofSkeleton)
    incrementalTraces.foreach({ tr => addConstraint(tr._1, tr._2, tr._3)})
  }

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
  private def checkPrefixIndependance(pos : mutable.Set[Trace], neg : mutable.Set[Trace]) : Unit =  {
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
    this.positiveSamples = Buffer.tabulate(nbProcesses)({_ => mutable.Set[Trace]()})
    this.negativeSamples = Buffer.tabulate(nbProcesses)({_ => mutable.Set[Trace]()})
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

  def generateAssumptions(oldAssumptions : Buffer[DLTS]) : Option[Buffer[DLTS]] = {
    var positiveSamples = Buffer.tabulate(nbProcesses)({_ => mutable.Set[Trace]()})
    var negativeSamples = Buffer.tabulate(nbProcesses)({_ => mutable.Set[Trace]()})
    var beginTime = System.nanoTime()
    // System.out.println(s"nbProcesses: ${oldAssumptions.size}")
    // System.out.println(s"Assumption alphabets: ${proofSkeleton.assumptionAlphabets}")
    // System.out.println("Constraints")
    // System.out.println(constraint)
    // System.out.println("Theroy Constraints")
    // System.out.println(theoryConstraints)
    // System.out.println(s"Displaying assertions")
    // for e <- solver.getAssertions() do {
    //   System.out.println(e)
    // }
    // solver.add(constraint)
    // solver.add(theoryConstraints)
    // System.out.println("Z3 constraints:")
    // for v <- this.toIndexedTraces.keys do {
    //   System.out.println(s"(declare-const ${v} Bool)")
    // }
    // for ass <- solver.getAssertions() do {
    //   System.out.println(s"(assert ${ass})")
    // }
    // System.out.println(samples)
    if(solver.check() == z3.Status.UNSATISFIABLE){
      if configuration.get().verbose then {
        System.out.println(constraint)
        System.out.println("Theory constraints:")
        System.out.println(theoryConstraints)
      }
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
                    positiveSamples(i).add(sample.dropRight(k))
                  }
                case z3.enumerations.Z3_lbool.Z3_L_FALSE => 
                  negativeSamples(i).add(trace.filter(proofSkeleton.assumptionAlphabets(i)))
                case _ =>
                  val sample = trace.filter(proofSkeleton.assumptionAlphabets(i))
                  // Add all prefixes
                  for k <- 0 to sample.size do {
                    positiveSamples(i).add(sample.dropRight(k))
                  }
              }
          })
      })
      statistics.Timers.incrementTimer("z3", (System.nanoTime() - beginTime))
      val newAssumptions = Buffer[DLTS]()
      for i <- 0 until nbProcesses do {
        if configuration.get().verbose then {
          System.out.println(s"#POS(${i}) = ${positiveSamples(i).size}:")
          for w <- positiveSamples(i) do {
            System.out.println(s"\t${w}")
          }
          System.out.println(s"#NEG(${i}) = ${negativeSamples(i).size}:")
          for w <- negativeSamples(i) do {
            System.out.println(s"\t${w}")
          }
        }
        // checkPrefixIndependance(positiveSamples(i), negativeSamples(i))
        if( positiveSamples(i).toSet == this.positiveSamples(i).toSet
            && negativeSamples(i).toSet == this.negativeSamples(i).toSet
            && oldAssumptions(i).alphabet == proofSkeleton.assumptionAlphabets(i)
        ){
          newAssumptions.append(oldAssumptions(i))
          if configuration.get().verbose then {
            System.out.println(s"Keeping assumption ${i}...")
          }
        } else {
          if configuration.get().verbose then {
            System.out.println(s"${BLUE}Updating assumption ${i}...${RESET} with alphabet: ${proofSkeleton.assumptionAlphabets(i).toList}")
          }
          statistics.Counters.incrementCounter("RPNI")
          val learner = BlueFringeRPNIDFA(Alphabets.fromList(proofSkeleton.assumptionAlphabets(i).toList))
          learner.addPositiveSamples(positiveSamples(i).map(Word.fromList(_)))
          learner.addNegativeSamples(negativeSamples(i).map(Word.fromList(_)))
          var beginTime = System.nanoTime()
          val initialModel = learner.computeModel()
          statistics.Timers.incrementTimer("rpni", System.nanoTime() - beginTime)
          newAssumptions.append(
            DLTS(
                oldAssumptions(i).name,
                dfa = DLTS.makePrefixClosed(initialModel, proofSkeleton.assumptionAlphabets(i), removeNonAcceptingStates = true),
                alphabet = proofSkeleton.assumptionAlphabets(i)
            )
          )
          System.out.println(s"${BLUE}Size of DFA ${newAssumptions(i).dfa.size()}...${RESET}")
          this.positiveSamples(i) = positiveSamples(i)
          this.negativeSamples(i) = negativeSamples(i)
        }
      }
      statistics.Timers.incrementTimer("generate-assumptions", System.nanoTime() - beginTime)
      Some(newAssumptions)
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
}
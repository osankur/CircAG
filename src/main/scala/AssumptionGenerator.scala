package fr.irisa.circag

import java.util.HashMap
import scala.collection.mutable.Buffer
import scala.collection.mutable
import collection.JavaConverters._
import collection.convert.ImplicitConversions._

import io.AnsiColor._

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
trait AssumptionGenerator{
  def getAssumption() : DFA[String, String]
}

abstract class LStarAssumptionGenerator extends AssumptionGenerator{
  
}
class SATAssumptionGenerator {
  def doSomething() : Unit =
    {

    }
}
abstract class IDFAAssumptionGenerator extends AssumptionGenerator



class ConstraintManager(private var processDependencies : Buffer[Set[Int]], 
                        private var propertyDependencies : Set[Int],
                        private var assumptionAlphabets : Buffer[Set[String]]
                        ){

  private val z3ctx = {
    val cfg = HashMap[String, String]()
    cfg.put("model", "true");
    z3.Context(cfg);
  }

  private val nbProcesses = processDependencies.size
  private val samples = Buffer.tabulate(nbProcesses)({_ => Buffer[(Trace,z3.BoolExpr)]()})
  private val toVars = HashMap[(Int,Trace), z3.BoolExpr]()
  private val toIndexedTraces = HashMap[z3.BoolExpr, (Int,Trace)]()
  private val incrementalTraces = Buffer[(Int, Trace, Int)]()

  private var constraint = z3ctx.mkTrue()
  private var theoryConstraints = z3ctx.mkTrue()
  private var solver = z3ctx.mkSolver()
  private var previousValuation = HashMap[z3.BoolExpr,Boolean]()

  private var positiveSamples = Buffer.tabulate(nbProcesses)({_ => Buffer[Trace]()})
  private var negativeSamples = Buffer.tabulate(nbProcesses)({_ => Buffer[Trace]()})

  // the empty word must be accepted by all
  constraint = z3ctx.mkAnd((0 until nbProcesses).map({i => varOfIndexedTrace(i, List[String]())}) : _*)

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

  def addConstraint(process : Int, trace : Trace, constraintType : Int) : Unit = {
    constraintType match {
      case 34 =>
        assert(trace.size > 0)
        val prefix = trace.dropRight(1)
        constraint = z3ctx.mkAnd(constraint, 
          z3ctx.mkOr(
            z3ctx.mkOr(processDependencies(process).map({j => z3ctx.mkNot(varOfIndexedTrace(j, prefix))}).toSeq : _*),
            varOfIndexedTrace(process, trace)
          )
        )
        incrementalTraces.append((process, trace, constraintType))
    }
  }

  def addFinalPremiseConstraint(trace : Trace) : Unit = {
    constraint = z3ctx.mkAnd(constraint, 
      z3ctx.mkOr(
        z3ctx.mkOr(propertyDependencies.map({j => z3ctx.mkNot(varOfIndexedTrace(j, trace))}).toSeq : _*)
      )
    )
  }


  def restart(processDependencies : Buffer[Set[Int]], assumptionAlphabets : Buffer[Set[String]]) : Unit = {
    this.processDependencies = processDependencies
    this.assumptionAlphabets = assumptionAlphabets
    constraint = z3ctx.mkTrue()
    theoryConstraints = z3ctx.mkTrue()
    solver = z3ctx.mkSolver()
    incrementalTraces.foreach({ tr => addConstraint(tr._1, tr._2, tr._3)})
    (0 until nbProcesses).foreach({i => updateTheoryConstraints(i)})
  }

  def checkPrefixIndependance(pos : Buffer[Trace], neg : Buffer[Trace]) : Unit =  {
    for p <- pos do {
      for n <- neg do {
        if (p.startsWith(neg)) then {
          throw Exception(s"pos: ${p}, neg: ${n}")
        }
      }
    }
  }
  def generateAssumptions(oldAssumptions : Buffer[DLTS]) : Buffer[DLTS] = {
    var positiveSamples = Buffer.tabulate(nbProcesses)({_ => Buffer[Trace]()})
    var negativeSamples = Buffer.tabulate(nbProcesses)({_ => Buffer[Trace]()})
    // System.out.println(s"Old positive samples: ${this.positiveSamples}")
    // System.out.println(s"Old negative samples: ${this.negativeSamples}")

    solver.add(constraint)
    solver.add(theoryConstraints)
    if(solver.check() != z3.Status.SATISFIABLE){
      throw Exception("Constraints are unsatisfiable")
    }
    // System.out.println(constraint)
    // System.out.println(theoryConstraints)
    val m = solver.getModel()
    // System.out.println(m)
    samples.zipWithIndex.foreach({
      (isamples, i) => 
        isamples.foreach({
          (trace, v) =>
            m.evaluate(v, false).getBoolValue() match {
              case z3.enumerations.Z3_lbool.Z3_L_TRUE =>
                // System.out.println(s"Valuation(${i}):POS: ${trace} --> ${trace.filter(assumptionAlphabets(i))}")
                positiveSamples(i).add(trace.filter(assumptionAlphabets(i)))
              case z3.enumerations.Z3_lbool.Z3_L_FALSE => 
                // System.out.println(s"Valuation(${i}):NEG: ${trace} --> ${trace.filter(assumptionAlphabets(i))}")
                negativeSamples(i).add(trace.filter(assumptionAlphabets(i)))
              case _ =>
                ()
            }
        })
    })
    val newAssumptions = Buffer[DLTS]()
    for i <- 0 until nbProcesses do {
      // System.out.println(s"Old positive samples for ${i}: ${this.positiveSamples(i)}")
      // System.out.println(s"Old negative samples for ${i}: ${this.negativeSamples(i)}")
      System.out.println(s"#POS(${i}) = ${positiveSamples(i).size}:\n")
      for w <- positiveSamples(i) do {
        System.out.println(s"\t${w}")
      }
      System.out.println(s"#NEG(${i}) = ${negativeSamples(i).size}:\n")
      for w <- negativeSamples(i) do {
        System.out.println(s"\t${w}")
      }
      checkPrefixIndependance(positiveSamples(i), negativeSamples(i))
      if( positiveSamples(i).toSet == this.positiveSamples(i).toSet
      && negativeSamples(i).toSet == this.negativeSamples(i).toSet){
        newAssumptions.append(oldAssumptions(i))
        // System.out.println(s"Keeping assumption ${i}...")
      } else {
        System.out.println(s"${BLUE}Updating assumption ${i}...${RESET}")
        val learner = BlueFringeRPNIDFA(Alphabets.fromList(assumptionAlphabets(i).toList))
        learner.addPositiveSamples(positiveSamples(i).map(Word.fromList(_)))
        learner.addNegativeSamples(negativeSamples(i).map(Word.fromList(_)))
        newAssumptions.append(
          DLTS(oldAssumptions(i).name, 
              DFAs.complete(DLTS.makePrefixClosed(learner.computeModel(), assumptionAlphabets(i)), Alphabets.fromList(assumptionAlphabets(i).toList)),
              assumptionAlphabets(i)))
        // Visualization.visualize(newAssumptions(i).dfa, Alphabets.fromList(assumptionAlphabets(i).toList))
        this.positiveSamples(i) = positiveSamples(i)
        this.negativeSamples(i) = negativeSamples(i)
      }
    }
    newAssumptions
  }
  /**
    * Compute boolean expression with the following property:
      For each pair of traces w, w', if proj(w, alphabet) is a prefix of proj(w', alphabet),
    * then var(w') -> var(w).
    * Here w ranges over samples(process)(sampleIndex..) and w' ranges over samples(process)(sampleIndex-1)
    *
    * @param process
    * @param alphabet
    * @return
    */
  private def updateTheoryConstraints(process : Int, sampleIndex : Int = 0) : Unit = {
    // val projTraces = samples(process).map({ (trace,v) => (trace.filter(this.assumptionAlphabets(process).contains(_)), v)})
    for i <- sampleIndex until samples(process).size do {
      val projTrace_i = this.samples(process)(i)._1.filter(this.assumptionAlphabets(process).contains(_))
      val vi = this.samples(process)(i)._2
      for j <- 0 until i do {
        val projTrace_j = this.samples(process)(j)._1.filter(this.assumptionAlphabets(process).contains(_))
        val vj = this.samples(process)(j)._2
        // System.out.println(s"VERSUS ${samples(process)(i)._1} - ${samples(process)(j)._1}")
        // System.out.println(s"PROJ VERSUS ${projTrace_i} - ${projTrace_j}")

        if projTrace_i.startsWith(projTrace_j) then{
          theoryConstraints = z3ctx.mkAnd(theoryConstraints, z3ctx.mkImplies(vi, vj))
          // System.out.println("\t  -> ")
        }
        if projTrace_j.startsWith(projTrace_i) then{
          theoryConstraints = z3ctx.mkAnd(theoryConstraints, z3ctx.mkImplies(vj, vi))
          // System.out.println("\t  <- ")
        }
      }
    }
  }

}

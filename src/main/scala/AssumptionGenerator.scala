package fr.irisa.circag

import java.util.HashMap
import scala.collection.mutable.Buffer
import collection.JavaConverters._
import collection.convert.ImplicitConversions._


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

  private var positiveSamples = Buffer.tabulate(nbProcesses)({_ => Set[Trace]()})
  private var negativeSamples = Buffer.tabulate(nbProcesses)({_ => Set[Trace]()})

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

  def generateAssumptions(oldAssumptions : Buffer[DLTS]) : Buffer[DLTS] = {
    var positiveSamples = Buffer.tabulate(nbProcesses)({_ => Set[Trace]()})
    var negativeSamples = Buffer.tabulate(nbProcesses)({_ => Set[Trace]()})
    solver.add(constraint)
    solver.add(theoryConstraints)
    if(solver.check() != z3.Status.SATISFIABLE){
      throw Exception("Constraints are unsatisfiable")
    }
    val m = solver.getModel()
    System.out.println(m)
    samples.zipWithIndex.foreach({
      (isamples, i) => 
        isamples.foreach({
          (trace, v) =>
            m.evaluate(v, false).getBoolValue() match {
              case z3.enumerations.Z3_lbool.Z3_L_TRUE => 
                positiveSamples(i).add(trace)
              case z3.enumerations.Z3_lbool.Z3_L_FALSE => 
                negativeSamples(i).add(trace)
              case _ =>
                throw Exception("Unknown value for variable " + v)
            }
        })
    })
    System.out.println(s"New positive samples: ${positiveSamples}")
    System.out.println(s"New negative samples: ${negativeSamples}")
    val newAssumptions = Buffer[DLTS]()
    for i <- 0 until nbProcesses do {
      if( positiveSamples(i) == this.positiveSamples(i)
      && negativeSamples(i) == this.negativeSamples(i)){
        newAssumptions.append(oldAssumptions(i))
      } else {
        System.out.println(s"updating assumption ${i}...")
        val learner = BlueFringeRPNIDFA(Alphabets.fromList(assumptionAlphabets(i).toList))
        learner.addPositiveSamples(positiveSamples(i).map(Word.fromList(_)))
        learner.addNegativeSamples(negativeSamples(i).map(Word.fromList(_)))
        newAssumptions.append(DLTS(oldAssumptions(i).name, DLTS.makePrefixClosed(learner.computeModel(), assumptionAlphabets(i)), assumptionAlphabets(i)))
        Visualization.visualize(newAssumptions(i).dfa, Alphabets.fromList(assumptionAlphabets(i).toList))
        this.positiveSamples = positiveSamples
        this.negativeSamples = negativeSamples
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
    val projTraces = samples(process).map({ (trace,v) => (trace.filter(this.assumptionAlphabets(process).contains(_)), v)})
    for i <- sampleIndex until projTraces.size do {
      for j <- 0 until i do {
        if projTraces(i)._1.startsWith(projTraces(j)._1) then{
          theoryConstraints = z3ctx.mkAnd(constraint, z3ctx.mkImplies(projTraces(i)._2, projTraces(j)._2))
        }
        if projTraces(j)._1.startsWith(projTraces(i)._1) then{
          theoryConstraints = z3ctx.mkAnd(constraint, z3ctx.mkImplies(projTraces(j)._2, projTraces(i)._2))
        }
      }
    }
  }

}

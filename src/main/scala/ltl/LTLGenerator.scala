package fr.irisa.circag.ltl

import scala.collection.mutable.{HashMap,Buffer}
import scala.collection.mutable
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
import fr.irisa.circag.{Trace, Lasso, DLTS, Alphabet}
import fr.irisa.circag.pruned

enum AssumptionGeneratorType:
  case SAT
  case Fijalkow


trait LTLLearner(name : String, alphabet : Alphabet) {
  def setPositiveSamples(samples : Set[Lasso]) = {
    if positiveSamples != samples then {
      positiveSamples = samples
      dlts = None
    }
  }
  def setNegativeSamples(samples : Set[Lasso]) = {
    if negativeSamples != samples then {
      negativeSamples = samples
      dlts = None
    }
  }
  def getLTL() : LTL
  protected var dlts : Option[LTL] = None
  protected var positiveSamples : Set[Lasso] = Set()
  protected var negativeSamples : Set[Lasso] = Set()
}

/**
* Neider et al.
*
* @param name
* @param alphabet
*/
class SATLearner(name : String, alphabet : Alphabet) extends LTLLearner(name, alphabet) {
  val ctx = {
    val cfg = HashMap[String, String]()
    cfg.put("model", "true");
    z3.Context(cfg);
  }
  val solver = ctx.mkSolver()

  override def getLTL() : LTL = {
    LTLTrue()
  }
}

class LTLGenerator(proofSkeleton : AGProofSkeleton, assumptionGeneratorType : AssumptionGeneratorType = AssumptionGeneratorType.SAT) {
  protected val z3ctx = {
    val cfg = HashMap[String, String]()
    cfg.put("model", "true")
    z3.Context(cfg);
  }

  protected val nbProcesses = proofSkeleton.nbProcesses
  // Set of all samples added so far
  protected val samples = Buffer.tabulate(nbProcesses)({_ => Buffer[(Trace,z3.BoolExpr)]()})
  // Boolean variable corresponding to each pair (pr,trace)
  protected val toVars = HashMap[(Int,Trace), z3.BoolExpr]()
  protected val toIndexedTraces = HashMap[z3.BoolExpr, (Int,Trace)]()

  protected var solver = z3ctx.mkSolver()

  // Samples that were used to compute assumptions the last time. Here the prefix closure of the positive samples were added
  protected var positiveSamples = Buffer.tabulate(nbProcesses)({_ => Set[Trace]()})
  protected var negativeSamples = Buffer.tabulate(nbProcesses)({_ => Set[Trace]()})
}
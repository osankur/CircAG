package fr.irisa.circag.ltl
import org.slf4j.Logger
import org.slf4j.LoggerFactory

import scala.collection.mutable.{HashMap,Buffer}
import scala.collection.mutable
import scala.collection.immutable.Set
import collection.JavaConverters._
import collection.convert.ImplicitConversions._
import scala.sys.process._
import scala.io
import java.io.File
import java.io.InputStream
import java.nio.file._
import java.io.PrintWriter
import java.io.ByteArrayInputStream

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

  /**
  * Passive learning of LTL formulas.
  *
  * @param name name of the DLTS to be learned
  * @param alphabet alphabet of the DLTS
  */
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
  def getLTL() : Option[LTL]
  protected var dlts : Option[LTL] = None
  protected var positiveSamples : Set[Lasso] = Set()
  protected var negativeSamples : Set[Lasso] = Set()
}

/**
* Interface to Iran Gavran's samples2LTL tool.
*
* @param name name of the DLTS to be learned
* @param alphabet alphabet of the DLTS
*/
class SATLearner(name : String, alphabet : Alphabet) extends LTLLearner(name, alphabet) {

  protected val logger = LoggerFactory.getLogger("CircAG")

  def samples2LTL(universal : Boolean) : Option[LTL] = {
    // Map each symbol of alphabet to 1,0,0; 0,1,0; 0,0,1 etc.
    val symbol2code = mutable.Map[String, String]()
    // Backward substitution: x0 -> a, x1 -> b, x2 -> c etc
    val bwdSubst = mutable.Map[String, String]()
    val nAlphabet = alphabet.size
    for (symbol, i) <- alphabet.toList.zipWithIndex do {
      val prefix = List.tabulate(i)(_ => "0")
      val suffix = List.tabulate(nAlphabet-i-1)(_ => "0")      
      symbol2code.put(symbol, (prefix:::(1::suffix)).mkString(","))
      bwdSubst.put(s"x${i}", symbol)
    }

    def encodeLasso(lasso : Lasso) :String = {
      val (pref, cycle) = lasso
      s"${(pref++cycle).map(symbol2code.apply).mkString(";")}::${pref.size}"
    }
    val encPos = positiveSamples.map(encodeLasso)
    val encNeg = negativeSamples.map(encodeLasso)

    val inputFile =
      Files.createTempFile(configuration.get().getTmpDirPath(), "samples2LTL-query", ".trace").toFile()
    val pw = PrintWriter(inputFile)
    for samples <- encPos do {
      pw.write(samples)  
      pw.write("\n")
    }
    pw.write("---\n")
    for samples <- encNeg do {
      pw.write(samples)  
      pw.write("\n")
    }
    pw.close()

    val universalStr = if universal then "--universal" else ""
    val cmd = s"python samples2ltl/samples2LTL.py --sat ${universalStr} --traces ${inputFile.toString}"

    logger.debug(cmd)

    val stdout = StringBuilder()
    val stderr = StringBuilder()
    val output = cmd !! ProcessLogger(stdout append _, stderr append _)
    
    if output.contains("NO SOLUTION") then
      logger.debug(s"Samples2LTL returned NO SOLUTION")
      None
    else {
      val ltl = LTL.fromString(output)
      val substLtl = LTL.substitute(ltl, bwdSubst)
      logger.debug(s"Samples2LTL returned ${substLtl}")
      Some(substLtl)
    }
  }

  override def getLTL() : Option[LTL] = {
    dlts match {
      case Some(dlts) => Some(dlts)
      case None => 
        None
    }
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
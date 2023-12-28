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
import java.nio.file.StandardCopyOption.REPLACE_EXISTING
import java.nio.file.Files.copy
import java.nio.file.Paths.get
import java.io.File
import java.io.InputStream
import java.nio.file.{Paths,Files}
import java.io.PrintWriter
import java.io.ByteArrayInputStream

import io.AnsiColor._

import com.microsoft.z3

import fr.irisa.circag.statistics
import fr.irisa.circag.configuration
import fr.irisa.circag.{Trace, Lasso, DLTS, Alphabet}
import fr.irisa.circag.{pruned, filter, suffix, semanticEquals, size}


enum LTLLearningAlgorithm:
  case Samples2LTL, Scarlet

  /**
  * Passive learning of LTL formulas. If learning universal formulas of the form G(phi),
  * all samples constraint phi.
  *
  * @param name name of the DLTS to be learned
  * @param alphabet alphabet of the DLTS
  * @param universal whether a universal formula is to be learned.
  */
trait LTLLearner(name : String, alphabet : Alphabet, universal : Boolean) {
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
* Interface to Iran Gavran's samples2LTL, and Ritam et al. Scarlet tools.
*
* @param name name of the DLTS to be learned
* @param alphabet alphabet of the DLTS
*/
class SATLearner(name : String, alphabet : Alphabet, universal : Boolean, solver : LTLLearningAlgorithm) 
  extends LTLLearner(name, alphabet, universal) {

  protected val logger = LoggerFactory.getLogger("CircAG")

  def learn() : Option[LTL] = {
    // logger.debug(s"Entering learn(${solver}) (universal=${universal}) for process ${name} with the following samples:")
    // logger.debug(s"Pos = ${positiveSamples}")
    // logger.debug(s"Neg = ${negativeSamples}")
    // Take care of the corner case not handled by samples2LTL
    if negativeSamples.isEmpty then
      if universal then return Some(G(LTLTrue()))
      else return Some(LTLTrue())
    else if positiveSamples.isEmpty then {
      if universal then return Some(G(LTLFalse()))
      else return Some(LTLFalse())
    }

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
    // pw.write("---\n")
    // pw.write("G,F,!,|,&\n")
    pw.close()

    solver match {
      case LTLLearningAlgorithm.Samples2LTL => 
        val cmd = s"python samples2ltl/samples2LTL.py --sat --traces ${inputFile.toString}"

        logger.debug(s"${BLUE}${cmd}${RESET}")

        val stdout = StringBuilder()
        val stderr = StringBuilder()
        val beginTime = System.nanoTime()
        val output =
          try{
          cmd !! ProcessLogger(stdout append _, stderr append _)
          } catch {        
            case e => 
              logger.error(s"Unexpected return value when executing: ${cmd}")
              throw e
          }
        statistics.Timers.incrementTimer("ltl-learner", System.nanoTime() - beginTime)
        
        if output.contains("NO SOLUTION") then
          // logger.debug(s"Samples2LTL returned NO SOLUTION")
          None
        else {      
          val output_ = output.replaceAll("true","1").replaceAll("false","0")
          val ltl = LTL.fromString(output_)
          val substLtl = LTL.substitute(ltl, bwdSubst) match {
            case f if universal => G(f) 
            case f => f
          }      
          // logger.debug(s"Samples2LTL returned ${substLtl}")
          Some(substLtl)
        }
      case LTLLearningAlgorithm.Scarlet =>        
        Files.copy(inputFile.toPath(), Paths.get("Scarlet/_input_.trace"), REPLACE_EXISTING)
        val cmd = s"python -m Scarlet.ltllearner --i _input_.trace --timeout 120 --verbose --outputcsv _output_.csv"
        val stdout = StringBuilder()
        val stderr = StringBuilder()
        val beginTime = System.nanoTime()
        val output =
          try{
          cmd !! ProcessLogger(stdout append _, stderr append _)
          } catch {        
            case e => 
              logger.error(s"Unexpected return value when executing: ${cmd}")
              throw e
          }
        statistics.Timers.incrementTimer("ltl-learner", System.nanoTime() - beginTime)
        
        val solutions = io.Source.fromFile("Scarlet/_output_.csv").getLines().toSeq.tail
        if solutions.isEmpty then {
          None
        } else {
          // Parse alphabet
          val alphabetString = 
            val l = stderr.toString().split("\n").filter(_.contains("Alphabet: "))
            if (l.size != 1) then throw Exception(s"Cannot parse alphabet from the following output of Scarlet:\n${stderr}")
            l.head
          val rAlphabet = ".*\\[(.*)\\].*".r
          val rLetter1 = "'(.*)'".r
          val rLetter2 = "\"(.*)\"".r
          val letters = 
            alphabetString match {
              case rAlphabet(letters) => 
                letters.split(",").map({
                    sigma =>  sigma.strip() match {
                      case rLetter1(a) => a
                      case rLetter2(a) => a
                      case _ => throw Exception(s"Cannot parse letter ${sigma} in the alphabet description ${alphabetString} of Scarlet")
                    }
                  })
              case _ => throw Exception(s"Could not parse alphabet from the following line: ${alphabetString}")
            }
          // println(s"Parsed alphabet: ${letters.toList}")
          // Parse solution
          val lastSolution = solutions.last
          // println(s"Last solution is: ${lastSolution}")
          val csvTerms = lastSolution.split(",")
          if (csvTerms.size < 3) then throw Exception(s"Output file Scarlet/_output_.csv does not contain a solution")
          val ltlFormula = LTL.fromString(csvTerms(2)) match {
            case f if universal => G(f)
            case f => f
          }
          // Double substitute p -> x0 -> bwdSubst(x0)
          val subst = HashMap[String,String]()
          letters
          .zipWithIndex
          .foreach({
            (p, i) => subst.put(p, bwdSubst(s"x${i}"))
          })
          // println(s"Substitution is ${subst}")
          Some(LTL.substitute(ltlFormula, subst))
        }
    }
  }

  override def getLTL() : Option[LTL] = {
    dlts match {
      case Some(dlts) => Some(dlts)
      case None => 
        dlts = learn()
        dlts
    }
  }
}


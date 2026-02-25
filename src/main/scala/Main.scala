package fr.irisa.circag

import collection.JavaConverters._
import collection.convert.ImplicitConversions._
import scala.sys.process._
import org.slf4j.Logger
import org.slf4j.LoggerFactory
import io.AnsiColor._
import scopt.OParser
import java.io._
import java.nio.file.Files

import net.automatalib.words.Word
import net.automatalib.words.Alphabet;
import net.automatalib.words.impl.Alphabets;
import net.automatalib.automata.fsa.impl.compact.CompactDFA;
import net.automatalib.util.automata.builders.AutomatonBuilders;

import fr.irisa.circag.configuration.Configuration
import fr.irisa.circag.configuration.FSM
import fr.irisa.circag.TA
import fr.irisa.circag.dfa.DFALearningAlgorithm
import scala.collection.mutable
import scala.collection.immutable
import collection.JavaConverters._
import scala.annotation.static
import com.microsoft.z3

import net.automatalib.automata.fsa.impl.FastDFA
import net.automatalib.automata.fsa.impl.FastDFAState
import net.automatalib.util.automata.fsa.DFAs 
import net.automatalib.util.automata.fsa.NFAs 
import net.automatalib.automata.fsa.impl.compact.CompactDFA;
import net.automatalib.util.automata.builders.AutomatonBuilders;

import fr.irisa.circag.ltl._
object Main {
  val logger = LoggerFactory.getLogger("CircAG")

  def main(args: Array[String]): Unit = {   
    val builder = OParser.builder[Configuration]
    val parser1 = {
      import builder._
      OParser.sequence(
        programName("CircAG"),
        head("circAG", "0.1"),
        opt[Seq[File]]("files")
          .valueName("<files>")
          .action(
            (x,c) =>
            c.copy(ltsFiles = x.toArray)
          )
          .text("List of .tck files defining the system"),
        opt[File]("dir")
          .valueName("<dir>")
          .action(
            (x, c) =>
              if !x.isDirectory() then {
                throw Exception(s"Argument to option dir must be a directory")
              }
              c.copy(ltsFiles = x.listFiles.filter({f => f.getName().endsWith((".tck"))} ))
          )
          .text("Directory containing the .tck files defining the system"),
        opt[Seq[String]]("err")
          .valueName("<err>")
          .action((x, c) => 
              c.copy(err = x.toList)
            )
          .text("list of labels considered to be an error; so that the property to be checked is 'G /\\_{e in err} e'."),
        opt[String]("ltlProperty")
          .valueName("<ltlProperty>")
          .action((x, c) => 
              c.copy(ltlProperty = Some(x))
            )
          .text("LTL property to be checked in the infinite and fair behaviors of the overall system."),
        opt[Boolean]("verbose")
          .action((x, c) => c.copy(verbose = x))
          .valueName("(true|false)"),
        opt[Int]("seed")
          .action((x, c) => c.copy(randomSeed = x)),
        opt[Boolean]("keepTmpFiles")
          .action((x, c) => c.copy(keepTmpFiles = x))
          .valueName("(true|false)"),
        opt[Boolean]("dumpAssumptions")
          .action((x, c) => c.copy(dumpAssumptions = x))
          .valueName("(true|false)")
          .text("Dump the assumption DFAs or LTL formulas that were learned"),
        opt[Boolean]("visualizeAssumptions")
          .action((x, c) => c.copy(visualizeAssumptions = x))
          .valueName("(true|false)")
          .text("Visualize learned assumptions by a pop-up"),
        opt[String]("dfaLearningAlgorithm")
          .action({(x, c) => x match {
            case "SAT" => c.copy(dfaLearningAlgorithm = DFALearningAlgorithm.SAT)
            case "UFSAT" => c.copy(dfaLearningAlgorithm = DFALearningAlgorithm.UFSAT)
            case _ => c.copy(dfaLearningAlgorithm = DFALearningAlgorithm.RPNI)
          }})
          .text("DFA Learning algorithm (RPNI|SAT|UFSAT)"),
        opt[String]("strategy")
          .action({(x, c) => x match {
            case "Disjunctive" => 
              c.copy(constraintStrategy = dfa.ConstraintStrategy.Disjunctive, 
                    dfaLearningAlgorithm = DFALearningAlgorithm.SAT)
            case "LoggingDisjunctive" => 
              c.copy(constraintStrategy = dfa.ConstraintStrategy.LoggingDisjunctive, 
                    dfaLearningAlgorithm = DFALearningAlgorithm.SAT)
            case "DisjunctiveSeparate" => 
              c.copy(constraintStrategy = dfa.ConstraintStrategy.DisjunctiveSeparate)
            case "Eager" => 
              c.copy(constraintStrategy = dfa.ConstraintStrategy.Eager)
          }})
          .text("Constraint strategy: Eager | DisjunctiveSeparate | Disjunctive"),
        cmd("product")
          .action((_, c) => c.copy(cmd = "product"))
          .text("Compute the product of the given .tck files. If error labels are given, run TChecker to check the product."),
        cmd("dfa")
          .action((_, c) => c.copy(cmd = "dfa"))
          .text("Apply automatic AG for finite traces"),
        cmd("ltl")
          .action((_, c) => c.copy(cmd = "ltl"))
          .text("Apply automatic AG for infinite traces")
      )
    }
    val beginTime = System.nanoTime()
    try {
      OParser.parse(parser1, args, Configuration()) match {
        case None => ()
        case Some(config) =>
          configuration.set(config)
          logger.info(s"Command: ${config.cmd}")
          logger.info(s"Files: ${config.ltsFiles.toSeq}")
          if config.ltsFiles.isEmpty then {
            throw Exception("Please provide input files with the --files or --dir options.")
          }
          config.ltlProperty match {
            case None => ()
            case Some(ltl) => logger.info(s"LTL property: ${ltl}")
          }
          for file <- configuration.get().ltsFiles do {
            if (!file.exists()){
              throw Exception(("%sFile " + file.getAbsolutePath() + " does not exist%s").format(RED,RESET))
            }
          }
          z3.Global.setParameter("smt.random_seed",s"${config.randomSeed}")
          z3.Global.setParameter("sat.random_seed",s"${config.randomSeed}")

          config.cmd match {
            case "product" =>
              val tas = configuration.get().ltsFiles.map(TA.fromFile(_))              
              val product = TA.synchronousProduct(tas.toList)
              if config.err.size == 0 then {
                System.out.println(product.toString())
              } else {
                product.checkReachability(config.err : _*) match {
                  case None => logger.info(s"${GREEN}Safety holds in the product${RESET}")
                  case Some(cex) => logger.info(s"${GREEN}Labels are reachable ${cex}${RESET}")
                }
              }
            case "dfa" =>
                logger.info(s"DFA Learning Algorithm: ${config.dfaLearningAlgorithm}")
                logger.info(s"DFA Learning Strategy: ${config.constraintStrategy}")
                logger.info(s"Error labels: ${config.err}")
                if config.err.size == 0 then {
                  throw Exception("Please provide an error event with the --err option")
                }
                dfa.DFAAutomaticVerifier(
                  dfa.SystemSpec(
                    configuration.get().ltsFiles, 
                    Some(DLTS.fromErrorSymbol(configuration.get().err))),
                  configuration.get().dfaLearningAlgorithm,
                  configuration.get().constraintStrategy
                ).learnAssumptions()
            case "ltl" =>
              val ltlProperty = LTL.fromString(configuration.get().ltlProperty.getOrElse("G 1"))
              val files = configuration.get().ltsFiles              
                ltl.LTLAutomaticVerifier(ltl.SystemSpec(files,ltlProperty))
                .learnAssumptions(configuration.get().ltlProperty != None)
            case _ => 
              logger.error("Unknown command")
          }
        }
    } catch {
      case e => 
        e.printStackTrace()
        System.err.println(e.getMessage())
    }
    val totalTime = (System.nanoTime() - beginTime)/1e9d
    logger.info(s"Counters: ${statistics.Counters.toString}")
    logger.info(s"Timers: ${statistics.Timers}")
    logger.info(s"Total time: ${totalTime}s")
    logger.info(s"Relative times: ${statistics.Timers.timer.map({(k,value) => f"${k}:${(value/1e7d)/totalTime}%.2f%%"}).toString()}")
  }
}

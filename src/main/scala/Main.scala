package fr.irisa.circag

import scala.sys.process._
import org.slf4j.Logger
import org.slf4j.LoggerFactory
import io.AnsiColor._
import scopt.OParser
import java.io._
import net.automatalib.words.Word
import net.automatalib.words.Alphabet;
import net.automatalib.words.impl.Alphabets;
import net.automatalib.automata.fsa.impl.compact.CompactDFA;
import net.automatalib.util.automata.builders.AutomatonBuilders;

import fr.irisa.circag.configuration.Configuration
import fr.irisa.circag.configuration.FSM
import fr.irisa.circag.tchecker.TA

import scala.collection.mutable
import scala.collection.immutable
import collection.JavaConverters._
import scala.annotation.static
import com.microsoft.z3

object Main {
  val logger = LoggerFactory.getLogger("CircAG")

  def main(args: Array[String]): Unit = {
    val builder = OParser.builder[Configuration]
    val parser1 = {
      import builder._
      OParser.sequence(
        programName("circAG"),
        head("circAG", "0.1"),
        opt[Seq[File]]("lts")
          .required()
          .valueName("<lts>")
          .action(
            (x,c) =>
            c.copy(ltsFiles = x.toArray)
          ),
        opt[String]("err")
          .valueName("<err>")
          .action((x, c) => 
              c.copy(err = x)
            )
          .text("err is the label indicating an error; so that the property to be checked is 'G not err'."),
        opt[Boolean]("ar")
          .valueName("<ar>")
          .optional()
          .action((x, c) => 
              c.copy(alphabetRefinement = x)
            )
          .text("Use automatic alphabet refinement."),
        opt[Boolean]("verbose")
          .action((_, c) => c.copy(verbose = true))
          .valueName("(true|false)"),
        opt[Int]("seed")
          .action((x, c) => c.copy(randomSeed = x)),
        opt[Boolean]("keepTmpFiles")
          .action((_, c) => c.copy(keepTmpFiles = true))
          .valueName("(true|false)"),
        opt[Boolean]("visualizeDFA")
          .action((_, c) => c.copy(visualizeDFA = true))
          .valueName("(true|false)")
          .text("Visualize the DFAs that were learned"),
        cmd("product")
          .action((_, c) => c.copy(cmd = "product")),
        cmd("dfa-aag")
          .action((_, c) => c.copy(cmd = "dfa-aag")),
        cmd("ag")
          .action((_, c) => c.copy(cmd = "ag"))
      )
    }
    val beginTime = System.nanoTime()
    try {
      OParser.parse(parser1, args, Configuration()) match {
        case None => ()
        case Some(config) =>
          configuration.set(config)
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
              val product = tchecker.TA.synchronousProduct(tas.toList)
              System.out.println(product.toString())
            case "dfa-aag" =>
              tchecker.dfa.DFAAssumeGuaranteeVerifier(configuration.get().ltsFiles, configuration.get().err, config.alphabetRefinement).check()
              match {
                case None => System.out.println(s"${GREEN}${BOLD}Success${RESET}")
                case Some(cex) => System.out.println(s"${RED}${BOLD}Counterexample${RESET} ${cex}")
              }
              
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
    logger.info(s"Total: ${totalTime}")
    logger.info(s"Relative times: ${statistics.Timers.timer.map({(k,value) => f"${k}:${(value/1e7d)/totalTime}%.2f%%"}).toString()}")
  }
}

// object DebugMain {

//   def main(args: Array[String]): Unit = {
//     val ltsFiles = Array[File](File("examples/toy/lts1.ta"),File("examples/toy/lts2.ta"),File("examples/toy/lts3.ta"))
//     configuration.globalConfiguration = configuration.get().copy(verbose = true)
//     tchecker.TCheckerAssumeGuaranteeVerifier(ltsFiles, "err", false).check()
//     match {
//       case None => System.out.println(s"${GREEN}${BOLD}Success${RESET}")
//       case Some(cex) => System.out.println(s"${RED}${BOLD}Counterexample${RESET} ${cex}")
//     }
//  }
// }
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

import scala.collection.mutable._
import collection.JavaConverters._

object Main {
  val logger = LoggerFactory.getLogger("CircAG")

  def main(args: Array[String]): Unit = {
    val builder = OParser.builder[Configuration]
    val parser1 = {
      import builder._
      OParser.sequence(
        programName("circAG"),
        head("circAG", "0.1"),
        opt[File]("lts")
          .required()
          .valueName("<lts>")
          .action((x, c) => 
              if (x.toString.endsWith(".ta")){
                c.copy(ltsFile = x, ltsFormat = FSM.TCheckerTA)
              } else {
                throw Exception("Unknown lts format")
              }
            )
          .text("lts is the labeled transition system to be verified."),
        opt[File]("p")
          .required()
          .valueName("<p>")
          .action((x, c) => 
              if (x.toString.endsWith(".ta")){
                c.copy(ltsFile = x, ltsFormat = FSM.TCheckerTA)
              } else {
                throw Exception("Unknown lts format")
              }
            )
          .text("p is the property to be checked, given as a lts."),
        opt[Boolean]("verbose")
          .action((_, c) => c.copy(verbose = true))
          .valueName("(true|false)"),
        opt[Boolean]("keepTmpFiles")
          .action((_, c) => c.copy(keepTmpFiles = true))
          .valueName("(true|false)"),
        opt[Boolean]("visualizeDFA")
          .action((_, c) => c.copy(visualizeDFA = true))
          .valueName("(true|false)")
          .text("Visualize the DFA that was learned")
      )
    }

    OParser.parse(parser1, args, Configuration()) match {
      case None => ()
      case Some(config) =>
        configuration.set(config)
        if (!configuration.get().ltsFile.exists()){
          logger.error(("%s File " + configuration.get().ltsFile.getAbsolutePath() + " does not exist%s").format(RED,RESET))
          return
        }
        if (!configuration.get().pFile.exists()){
          logger.error(("%s File " + configuration.get().pFile.getAbsolutePath() + " does not exist%s").format(RED,RESET))
          return
        }
        logger.info("LTS File: " + configuration.get().ltsFile)
        logger.info("P File: " + configuration.get().pFile)
        val tmpFolder = configuration.get().tmpDirPath()
        
      }
  }
}

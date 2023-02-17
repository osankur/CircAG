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

import scala.collection.mutable
import scala.collection.immutable
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
        opt[Seq[File]]("lts")
          .required()
          .valueName("<lts>")
          .action(
            (x,c) =>
            c.copy(ltsFiles = x.toArray)
          ),
        opt[String]("err")
          .required()
          .valueName("<err>")
          .action((x, c) => 
              c.copy(err = x)
            )
          .text("err is the label indicating an error; so that the property to be checked is 'G not err'."),
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
        for file <- configuration.get().ltsFiles do {
          if (!file.exists()){
            logger.error(("%s File " + file.getAbsolutePath() + " does not exist%s").format(RED,RESET))
            return
          }
        }
        val checker = tchecker.TCheckerAssumeGuaranteeVerifier(configuration.get().ltsFiles, configuration.get().err)
        // checker.checkInductivePremises(checker.processes(0),)
      }
  }
}

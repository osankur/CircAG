package fr.irisa.circag

import collection.JavaConverters._
import collection.convert.ImplicitConversions._
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
import fr.irisa.circag.TA
import fr.irisa.circag.dfa.AssumptionGeneratorType
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

object Main {
  val logger = LoggerFactory.getLogger("CircAG")

  // def test() : Unit = {
  //   val inputs1: Alphabet[String] = Alphabets.fromList(List("req1","req2", "rel1", "rel2", "grant1", "grant2"))
  //   val gUser =
  //   AutomatonBuilders
  //     .forDFA(FastDFA(inputs1))
  //     .withInitial("i")
  //     .from("i")
  //     .on("req1")
  //     .to("r1")
  //     .from("i")
  //     .on("req2")
  //     .to("r2")
  //     .from("r1")
  //     .on("grant1")
  //     .to("g1")
  //     .from("r2")
  //     .on("grant2")
  //     .to("g2")
  //     .from("g1")
  //     .on("rel1")
  //     .to("i")
  //     .from("g2")
  //     .on("rel2")
  //     .to("i")
  //     .withAccepting("i")
  //     .withAccepting("r2")
  //     .withAccepting("r1")
  //     .withAccepting("g1")
  //     .withAccepting("g2")
  //    .create();
  
  //   val inputs2: Alphabet[String] = Alphabets.fromList(List("start1", "start2", "end1", "end2","req1","req2", "rel1", "rel2", "grant1", "grant2"))
  //   val gSched =
  //   AutomatonBuilders
  //     .forDFA(FastDFA(inputs2))
  //     .withInitial("q0")
  //     .from("q0").on("req1").to("r1")
  //     .from("r1").on("grant1").to("g1")
  //     .from("g1").on("start1").to("s1")
  //     .from("s1").on("end1").to("e1")
  //     .from("e1").on("rel1").to("q0")

  //     .from("g1").on("req2").to("r2")
  //     .from("r1").on("req2").to("r2")
  //     .from("s1").on("req2").to("r2")

  //     .from("q0").on("req2").to("r2")
  //     .from("r2").on("grant2").to("g2")
  //     .from("g2").on("start2").to("s2")
  //     .from("s2").on("end2").to("e2")
  //     .from("e2").on("rel2").to("q0")

  //     .from("g2").on("req1").to("r1")
  //     .from("r2").on("req1").to("r1")
  //     .from("s2").on("req1").to("r1")

  //     .withAccepting("q0")
  //     .withAccepting("r1")
  //     .withAccepting("r2")
  //     .withAccepting("g1")
  //     .withAccepting("g2")
  //     .withAccepting("s1")
  //     .withAccepting("s2")
  //     .withAccepting("e1")
  //     .withAccepting("e2")

  //     .create();

  //   val err = "err"
  //   val gMachine : FastDFA[String] =
  //     AutomatonBuilders
  //       .forDFA(FastDFA(Alphabets.fromList(List(err,"start1","start2","end1", "end2"))))
  //       .withInitial("q0")
  //       .from("q0")
  //       .on("start1")
  //       .to("q1")
  //       .from("q0")
  //       .on("start2")
  //       .to("q2")
  //       .from("q1")
  //       .on("end1")
  //       .to("q0")
  //       .from("q2")
  //       .on("end2")
  //       .to("q0")
  //       // error
  //       .from("q1")
  //       .on("start1")
  //       .to("qerr")
  //       .from("q1")
  //       .on("start2")
  //       .to("qerr")
  //       .from("q2")
  //       .on("start1")
  //       .to("qerr")
  //       .from("q2")
  //       .on("start2")
  //       .to("qerr")
  //       .from("qerr")
  //       .on("err")
  //       .to("qerr")
  //       .withAccepting("q0")
  //       .withAccepting("q1")
  //       .withAccepting("q2")
  //       .withAccepting("qerr")
  //       .create();
  //   // Visualization.visualize(gMachine, gMachine.getInputAlphabet())
  //   // Visualization.visualize(gUser, gUser.getInputAlphabet())
  //   // Visualization.visualize(gSched, gSched.getInputAlphabet())
  //   val errDFA : FastDFA[String] =
  //     AutomatonBuilders
  //       .forDFA(FastDFA(Alphabets.fromList(List(err))))
  //       .withInitial("q0")
  //       .from("q0")
  //       .on(err)
  //       .to("q1")
  //       .withAccepting("q0")
  //       .create();
  //   // Visualization.visualize(errDFA, true)
  //   assert(!errDFA.isPrunedSafety)
  //   assert(errDFA.isSafety)
  //   assert(errDFA.pruned.isPrunedSafety)
  //   assert(gUser.isPrunedSafety)
  //   assert(gUser.isSafety)
  //   val ver = dfa.DFAAutomaticAssumeGuaranteeVerifier(Array(File("examples/ums/user.ta"), File("examples/ums/scheduler.ta"), File("examples/ums/machine.ta")), "err")
  //   ver.assumptions(0) = DLTS("user", gUser, gUser.getInputAlphabet().toSet)
  //   ver.assumptions(0).visualize()
  //   ver.assumptions(1) = DLTS("sched", gSched, gSched.getInputAlphabet().toSet)
  //   ver.assumptions(2) = DLTS("machine", gMachine, gMachine.getInputAlphabet().toSet)
  //   configuration.set(configuration.get().copy(verbose_MembershipQueries = true))
  //   ver.proveGlobalPropertyByLearning(Some(List(0,1)))
  // }
  def main(args: Array[String]): Unit = {
    // test()
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
          .action((x, c) => c.copy(verbose = x))
          .valueName("(true|false)"),
        opt[Int]("seed")
          .action((x, c) => c.copy(randomSeed = x)),
        opt[Boolean]("keepTmpFiles")
          .action((x, c) => c.copy(keepTmpFiles = x))
          .valueName("(true|false)"),
        opt[Boolean]("visualizeDFA")
          .action((x, c) => c.copy(visualizeDFA = x))
          .valueName("(true|false)")
          .text("Visualize the DFAs that were learned"),
        opt[String]("learnerType")
          .action({(x, c) => x match {
            case "SAT" => c.copy(learnerType = AssumptionGeneratorType.SAT)
            case _ => c.copy(learnerType = AssumptionGeneratorType.RPNI)
          }})
          .text("Learner algorithm (RPNI|SAT)"),
        cmd("product")
          .action((_, c) => c.copy(cmd = "product")),
        cmd("dfa-aag")
          .action((_, c) => c.copy(cmd = "dfa-aag")),
        cmd("ltl-aag")
          .action((_, c) => c.copy(cmd = "ltl-aag"))
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
              val product = TA.synchronousProduct(tas.toList)
              System.out.println(product.toString())
            case "dfa-aag" =>
              dfa.DFAAutomaticAssumeGuaranteeVerifier(configuration.get().ltsFiles, configuration.get().err, configuration.get().learnerType, config.alphabetRefinement)
              .proveGlobalPropertyByLearning()
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

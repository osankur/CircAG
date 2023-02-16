package fr.irisa.circag

import java.util.HashMap
import java.io.File
import collection.JavaConverters._
import collection.convert.ImplicitConversions._
import com.microsoft.z3._


import dk.brics.automaton.Automaton
import dk.brics.automaton.RegExp

import de.learnlib.api.oracle._
import de.learnlib.api.oracle.MembershipOracle
import net.automatalib.words._
import de.learnlib.api.algorithm.LearningAlgorithm.DFALearner
import de.learnlib.algorithms.lstar.dfa.ClassicLStarDFA;
import de.learnlib.algorithms.lstar.dfa.ClassicLStarDFABuilder;
import de.learnlib.api.oracle.MembershipOracle.DFAMembershipOracle;
import de.learnlib.datastructure.observationtable.OTUtils;
import de.learnlib.datastructure.observationtable.writer.ObservationTableASCIIWriter;
import de.learnlib.filter.statistic.oracle.DFACounterOracle;
import de.learnlib.oracle.equivalence.DFAWMethodEQOracle;
import de.learnlib.oracle.membership.SimulatorOracle.DFASimulatorOracle;
import de.learnlib.util.Experiment.DFAExperiment;
import de.learnlib.util.statistics.SimpleProfiler;
import net.automatalib.automata.fsa.DFA;
import net.automatalib.util.automata.fsa.DFAs 
import net.automatalib.automata.fsa.impl.compact.CompactDFA;
import net.automatalib.util.automata.builders.AutomatonBuilders;
import net.automatalib.visualization.Visualization;
import net.automatalib.words.Alphabet;
import net.automatalib.words.impl.Alphabets;
import net.automatalib.brics.AbstractBricsAutomaton
import net.automatalib.brics.BricsNFA
import net.automatalib.visualization.Visualization
import net.automatalib.automata.fsa.DFA;
import net.automatalib.automata.fsa.impl.compact.CompactDFA;
import net.automatalib.util.automata.builders.AutomatonBuilders;
import net.automatalib.visualization.Visualization;
import net.automatalib.words.Alphabet;
import net.automatalib.words.impl.Alphabets;
import de.learnlib.util.MQUtil;
import de.learnlib.api.oracle.EquivalenceOracle
import de.learnlib.api.query.DefaultQuery;
// For more information on writing tests, see
// https://scalameta.org/munit/docs/getting-started.html

class MySuite extends munit.FunSuite {
  test("SAT Solver") {
    Global.ToggleWarningMessages(true);
    Log.open("test.log");

    System.out.print("Z3 Major Version: ");
    System.out.println(Version.getMajor());
    System.out.print("Z3 Full Version: ");
    System.out.println(Version.getString());
    System.out.print("Z3 Full Version String: ");
    System.out.println(Version.getFullVersion());

    val cfg = HashMap[String, String]()
    cfg.put("model", "true");
    val ctx = Context(cfg);      
    /* do something with the context */

    val opt = ctx.mkOptimize()

    // Set constraints.
    val xExp : IntExpr = ctx.mkIntConst("x")
    val yExp : IntExpr = ctx.mkIntConst("y")

    opt.Add(ctx.mkEq(ctx.mkAdd(xExp, yExp), ctx.mkInt(10)),
            ctx.mkGe(xExp, ctx.mkInt(0)),
            ctx.mkGe(yExp, ctx.mkInt(0)))

    // Set objectives.
    val mx : Optimize.Handle[IntSort] = opt.MkMaximize(xExp)
    val my : Optimize.Handle[IntSort] = opt.MkMaximize(yExp)

    System.out.println(opt.Check())
    System.out.println(mx)
    System.out.println(my)
    /* be kind to dispose manually and not wait for the GC. */
    ctx.close();      
  }

  test("premiseChecker"){
    val inputs1: Alphabet[String] = Alphabets.fromList(List("a","b"))
    val dfa1: CompactDFA[String] =
    AutomatonBuilders
      .newDFA(inputs1)
      .withInitial("q0")
      .from("q0")
      .on("a")
      .to("q0")
      .from("q0")
      .on("b")
      .to("q1")
      .from("q1")
      .on("b")
      .to("q1")
      .from("q1")
      .on("a")
      .to("q2")
      .withAccepting("q0")
      .withAccepting("q1")
      .create();
  
    val inputs2: Alphabet[String] = Alphabets.fromList(List("b", "c", "d"))
    val dfa2: CompactDFA[String] =
    AutomatonBuilders
      .newDFA(inputs2)
      .withInitial("q0")
      .from("q0")
      .on("c")
      .to("q0")
      .from("q0")
      .on("b")
      .to("q1")
      .from("q1")
      .on("d")
      .to("q1")
      .from("q1")
      .on("c")
      .to("q2")
      .withAccepting("q0")
      .withAccepting("q1")
      .create();
    val err = "c"
    val errDFA : CompactDFA[String] = {
      AutomatonBuilders
        .newDFA(Alphabets.fromList(List(err)))
        .withInitial("q0")
        .from("q0")
        .on(err)
        .to("q1")
        .withAccepting("q0")
        .create();
      }
    val extendedAlph = Alphabets.fromList(List("a","b","c","d"))
    // System.out.println(tchecker.TA.fromDLTS(DLTS("ass1", dfa1, dfa1.getInputAlphabet()), acceptingLabelSuffix = Some("_acc_")))
    val dltss = List(DLTS("ass1", dfa1, dfa1.getInputAlphabet()), DLTS("ass2", dfa2, dfa2.getInputAlphabet()))
    // Visualization.visualize(dltss.head.dfa, Alphabets.fromList(List("a","b")))
    // Visualization.visualize(DLTSs.lift(dltss.head, extendedAlph).dfa, extendedAlph)
    // System.out.println(dltss.map(tchecker.TA.fromDLTS(_)))
    val checker = tchecker.TCheckerAssumeGuaranteeOracles(Array(File("examples/b.ta")), err)
    checker.checkInductivePremises(checker.processes(0), dltss, DLTS("guarantee", errDFA, errDFA.getInputAlphabet()))
    // System.out.println("Printing core: " + checker.processes(0).core)
    // Then, display a DOT representation of this automaton
    // Visualization.visualize(ba, true);
  }
//   test("learning"){
//     val inputs: Alphabet[Character] = Alphabets.characters('a', 'b')
//     val mqOracle: MembershipOracle[Character, java.lang.Boolean] =
//       SampleMembershipOracle()
//     val lstar = ClassicLStarDFABuilder[Character]()
//       .withAlphabet(inputs)
//       .withOracle(mqOracle)
//       .create()
//     val wMethod = SampleEquivalenceOracle()
//     val experiment: DFAExperiment[Character] =
//       DFAExperiment(lstar, wMethod, inputs);

//     // turn on time profiling
//     experiment.setProfile(true);

//     // enable logging of models
//     experiment.setLogModels(true);

//     // run experiment
//     experiment.run();

//     // get learned model
//     val result = experiment.getFinalHypothesis();

//     // report results
//     System.out.println(
//       "-------------------------------------------------------"
//     );

//     // profiling
//     System.out.println(SimpleProfiler.getResults());

//     // learning statistics
//     System.out.println(experiment.getRounds().getSummary());

//     // model statistics
//     System.out.println("States: " + result.size());
//     System.out.println("Sigma: " + inputs.size());

//     // show model
//     // Visualization.visualize(result, inputs);
//     val f = new java.util.function.Function[Character, String] {
//       override def apply(input: Character): String = input + ""
//     }
//     // System.out.println(AUTWriter.writeAutomaton(result, inputs, f, System.out))

//     System.out.println(
//       "-------------------------------------------------------"
//     );
//   }
}
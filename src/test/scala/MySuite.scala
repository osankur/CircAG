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

import fr.irisa.circag.DLTS
import fr.irisa.circag.Trace

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
    // {a,c,d}*
    val inputs1: Alphabet[String] = Alphabets.fromList(List("c","d", "a"))
    val dfa1: CompactDFA[String] =
    AutomatonBuilders
      .newDFA(inputs1)
      .withInitial("q0")
      .from("q0")
      .on("c")
      .to("q0")
      .from("q0")
      .on("d")
      .to("q0")
      .from("q0")
      .on("a")
      .to("q0")
      .withAccepting("q0")
      .create();
  
    // a* + a*d+
    val inputs2: Alphabet[String] = Alphabets.fromList(List("d", "a"))
    val dfa2: CompactDFA[String] =
    AutomatonBuilders
      .newDFA(inputs2)
      .withInitial("q0")
      .from("q0")
      .on("a")
      .to("q0")
      .from("q0")
      .on("d")
      .to("q1")
      .from("q1")
      .on("d")
      .to("q1")
      .withAccepting("q0")
      .withAccepting("q1")
      .create();
    val err = "err"
    val errDFA : CompactDFA[String] =
      AutomatonBuilders
        .newDFA(Alphabets.fromList(List(err)))
        .withInitial("q0")
        .from("q0")
        .on(err)
        .to("q1")
        .withAccepting("q0")
        .create();

    val dltss = List(DLTS("ass1p", dfa1, dfa1.getInputAlphabet()), DLTS("ass2", dfa2, dfa2.getInputAlphabet()))
    val agv = tchecker.TCheckerAssumeGuaranteeVerifier(Array(File("examples/lts1.ta")), err)
    val checker = tchecker.TCheckerAssumeGuaranteeOracles.checkInductivePremises(agv.processes(0), dltss, agv.propertyDLTS)
    assert(checker != None)
    //System.out.println(checker)

    val dfa1_p: CompactDFA[String] =
    AutomatonBuilders
      .newDFA(Alphabets.fromList(List("c","d")))
      .withInitial("q0")
      .from("q0")
      .on("d")
      .to("q1")
      .from("q1")
      .on("c")
      .to("q1")
      .from("q1")
      .on("d")
      .to("q1")
      .withAccepting("q0")
      .withAccepting("q1")
      .create();
    
    val dltss_p = List(DLTS("ass1p", dfa1_p, dfa1_p.getInputAlphabet()), DLTS("ass2", dfa2, dfa2.getInputAlphabet()))
    val checker_p = tchecker.TCheckerAssumeGuaranteeOracles.checkInductivePremises(agv.processes(0), dltss_p, agv.propertyDLTS)
    assertEquals(checker_p, None)

 
 
    val dfa3: CompactDFA[String] =
    AutomatonBuilders
      .newDFA(Alphabets.fromList(List("c","a","b", "err")))
      .withInitial("q0")
      .from("q0")
      .on("a")
      .to("q0")
      .from("q0")
      .on("b")
      .to("q0")      
      .from("q0")
      .on("c")
      .to("q1")
      .from("q1")
      .on("b")
      .to("q1")
      .from("q1")
      .on("c")
      .to("q1")
      .from("q1")
      .on("a")
      .to("q2")
      .from("q2")
      .on("a")
      .to("q2")
      .from("q2")
      .on("b")
      .to("q2")
      .from("q2")
      .on("c")
      .to("q2")
      .from("q2")
      .on("err")
      .to("q3")
      .withAccepting("q0")
      .withAccepting("q1")
      .withAccepting("q2")
      .withAccepting("q3")
      .create();
 
    val cex3 = tchecker.TCheckerAssumeGuaranteeOracles.checkFinalPremise(DLTS("ass3", dfa3, dfa3.getInputAlphabet())::dltss_p, agv.propertyDLTS)
    assertEquals(cex3, None)

    assert(None == tchecker.TCheckerAssumeGuaranteeOracles.checkTraceMembership(agv.processes(0), List[String]("c", "c", "err", "err"), Some(Set[String]("c", "err"))))
    assert(None != tchecker.TCheckerAssumeGuaranteeOracles.checkTraceMembership(agv.processes(0), List[String]("c", "c", "err"), Some(Set[String]("c", "err"))))
    assert(None != tchecker.TCheckerAssumeGuaranteeOracles.checkTraceMembership(agv.processes(0), List[String]("c", "b", "err"), Some(Set[String]("c", "err"))))
    // (checker_p.processes(0), dltss_p, DLTS("guarantee", errDFA, errDFA.getInputAlphabet()))
    assert(tchecker.TCheckerAssumeGuaranteeOracles.extendTrace(agv.processes(0), List[String]("c", "c", "err"), None)
      == Some(List("c","c","a","err")))
  }
  test("fromTrace"){
    val _ = DLTS.fromTrace(List("a","b","c","a"),Some(Set("a", "b")))
  }
}
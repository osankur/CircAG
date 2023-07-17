package fr.irisa.circag


import net.automatalib.serialization.saf.SAFSerializationDFA 
import net.automatalib.serialization.aut.AUTWriter 

import java.util.HashMap
import java.io.File
import collection.JavaConverters._
import collection.convert.ImplicitConversions._
import collection.mutable.Buffer
import com.microsoft.z3._

import net.automatalib.serialization.aut.AUTWriter
import dk.brics.automaton.Automaton
import dk.brics.automaton.RegExp
import net.automatalib.serialization.taf.writer.TAFWriter 

import de.learnlib.algorithms.rpni.BlueFringeRPNIDFA
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
import net.automatalib.automata.fsa.impl.FastDFA
import net.automatalib.automata.fsa.impl.FastDFAState
import net.automatalib.util.automata.fsa.DFAs 
import net.automatalib.util.automata.fsa.NFAs 
import net.automatalib.automata.fsa.impl.compact.CompactDFA;
import net.automatalib.util.automata.builders.AutomatonBuilders;
import net.automatalib.visualization.Visualization;
import net.automatalib.words.Alphabet;
import net.automatalib.commons.util.nid.MutableNumericID;
import net.automatalib.words.impl.FastAlphabet;
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
import fr.irisa.circag.{DLTS, Trace}
import fr.irisa.circag._
import com.microsoft.z3.enumerations.Z3_lbool
import fr.irisa.circag.ltl._
import fr.irisa.circag.dfa._
import fr.irisa.circag.ltl.LTL




class Z3Tests extends munit.FunSuite {
  test("z3 enum sort"){
    val cfg = HashMap[String, String]()
    cfg.put("model", "true");
    // cfg.put("proof", "true");
    // cfg.put("unsat_core", "true")
    val ctx = Context(cfg);      
    val solver3 = ctx.mkSolver()
    val enumSort = ctx.mkEnumSort("T", Array[String]("a","b","c") : _*);
    val T = enumSort
    val esa = enumSort.getConst(0)
    val esb = enumSort.getConst(1)
    val esc = enumSort.getConst(2)
    val x = ctx.mkConst("x", T)
    val y = ctx.mkConst("y", T)
    val z = ctx.mkConst("z", T)

    solver3.add( ctx.mkOr(ctx.mkEq(x,esa), ctx.mkEq(y,esb)))
    solver3.add( ctx.mkOr(ctx.mkNot(ctx.mkEq(x,y))))
    assert(solver3.check() == Status.SATISFIABLE)
    // val m = solver3.getModel()
    // System.out.println(m)
  }
  test("z3 unsat core"){
    val cfg = HashMap[String, String]()
    cfg.put("proof", "true");
    cfg.put("unsat_core", "true");
    val ctx = Context(cfg);      
    val x = ctx.mkSymbol("x")
    val varx = ctx.mkBoolConst(x)
    val y = ctx.mkSymbol("x")
    val vary = ctx.mkBoolConst(x)
    val e = ctx.mkEq(varx, ctx.mkNot(varx))
    val solver = ctx.mkSolver()
    solver.add(e)
    assert(solver.check(vary) == Status.UNSATISFIABLE)
    System.out.println(solver.getProof())
    for ass <- solver.getUnsatCore() do {
      System.out.println(ass)
    }    
  }
}

class ParserTests extends munit.FunSuite {
  test("CEX Parsing from TChecker"){
    // get cex from tchecker
  }
  test("CEX Parsing from String"){
    val tck_output = """digraph _premise_lts1 {
      0 [initial="true", intval="", labels="lifted_g_1_accept_,lifted_g_2_accept_", vloc="<q1,qs0,qs0,qs0>", zone="()"]
      1 [intval="", labels="lifted_g_1_accept_,lifted_g_2_accept_", vloc="<q1,qs2,qs0,qs0>", zone="()"]
      2 [intval="", labels="lifted_g_1_accept_,lifted_g_2_accept_", vloc="<q2,qs2,qs2,qs0>", zone="()"]
      3 [final="true", intval="", labels="_comp_g_0_accept_,lifted_g_1_accept_,lifted_g_2_accept_", vloc="<q2,qs3,qs2,qs0>", zone="()"]
      4 [intval="", labels="lifted_g_1_accept_,lifted_g_2_accept_", vloc="<q3,qs2,qs2,qs0>", zone="()"]
      0 -> 2 [guard="", reset="", src_invariant="", tgt_invariant="", vedge="<lts1@a,_comp_g_0@a,lifted_g_1@a,lifted_g_2@a>"]
      1 -> 3 [guard="", reset="", src_invariant="", tgt_invariant="", vedge="<lts1@a,_comp_g_0@a,lifted_g_1@a,lifted_g_2@a>"]
      2 -> 4 [guard="", reset="", src_invariant="", tgt_invariant="", vedge="<lts1@b,lifted_g_1@b,lifted_g_2@b>"]
      4 -> 1 [guard="", reset="", src_invariant="", tgt_invariant="", vedge="<lts1@c,_comp_g_0@c,lifted_g_1@c,lifted_g_2@c>"]
    }""""
    val trace = TA.getTraceFromCounterExampleOutput(tck_output.split("\n").toList, Set("a","b","c"))
    assert(trace == List("a","b","c","a"))
  }
  test("fromTrace"){
    val dlts = DLTS.fromTrace(List("a","b","c","a"))
    assert(dlts.dfa.accepts(List("a","b","c", "a")))
    assert(!dlts.dfa.accepts(List("a","a","a")))
    assert(!dlts.dfa.accepts(List("a","b","b")))
  }
  test("fromTchecker"){
    val dlts = DLTS.fromTChecker(java.io.File("examples/lts1.ta"))
    // dlts.visualize()
    assert(dlts.dfa.accepts(List("a", "b", "c")))
    assert(dlts.dfa.accepts(List("c", "b", "a", "err")))
    assert(!dlts.dfa.accepts(List("c", "b", "err")))

  }

}
class DFAAAG extends munit.FunSuite {
  test("SAT Solver") {
    // Global.ToggleWarningMessages(true);
    // Log.open("test.log");
    // System.out.print("Z3 Major Version: ");
    // System.out.println(Version.getMajor());
    // System.out.print("Z3 Full Version: ");
    // System.out.println(Version.getString());
    // System.out.print("Z3 Full Version String: ");
    // System.out.println(Version.getFullVersion());

    val cfg = HashMap[String, String]()
    cfg.put("model", "true");
    // cfg.put("proof", "true");
    // cfg.put("unsat_core", "true")
    val ctx = Context(cfg);      
    /* do something with the context */

    val x = ctx.mkSymbol("x")
    val y = ctx.mkSymbol("y")
    val varx = ctx.mkBoolConst(x)
    val vary = ctx.mkBoolConst(y)
    val e = ctx.mkEq(varx, ctx.mkNot(vary))
    val solver = ctx.mkSolver()
    solver.add(e)
    // System.out.println(e)
    // System.out.println(solver.check())
    assert(solver.check() == Status.SATISFIABLE)
    val m = solver.getModel()
    // System.out.println(m)
    // System.out.println("x:" + (m.evaluate(varx, false).getBoolValue() == Z3_lbool.Z3_L_TRUE))
    // System.out.println("y:" + (m.evaluate(vary, false).getBoolValue() == Z3_lbool.Z3_L_TRUE))
    val a = m.evaluate(varx, false)
    val solver2 = ctx.mkSolver()
    solver2.add(ctx.mkAnd(varx,ctx.mkNot(varx)))
    assert(solver2.check() == Status.UNSATISFIABLE)
    ctx.close();      
  }

  test("sat learner"){
    val satLearner = dfa.SATLearner("ass", Set("a","b","c"))
    val positives = Set(List("a","b","c"),List("c","c"))
    val negatives = Set(List("b","c"),List("a","b","b"))
    satLearner.setPositiveSamples(positives)
    satLearner.setNegativeSamples(negatives)
    // satLearner.setPositiveSamples(Set(List("a","b")))
    // satLearner.setNegativeSamples(Set(List("a","b","b"), List("c")))
    // satLearner.setNegativeSamples(Set(List("b","b")))
    val dlts = satLearner.getDLTS()
    // dlts.visualize()
    positives.foreach(x => assert(dlts.dfa.accepts(x)))
    negatives.foreach(x => assert(!dlts.dfa.accepts(x)))
    // assert(dlts.dfa.accepts(List("a","b")))
    // assert(!dlts.dfa.accepts(List("c")))
    // assert(!dlts.dfa.accepts(List("a","b","b")))
    // dlts.visualize()
  }

  test("premiseChecker"){
    // {a,c,d}*
    val inputs1: Alphabet[String] = Alphabets.fromList(List("c","d", "a"))
    val dfa1 =
    AutomatonBuilders
      .forDFA(FastDFA(inputs1))
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
    val dfa2 =
    AutomatonBuilders
      .forDFA(FastDFA(inputs2))
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
    val errDFA : FastDFA[String] =
      AutomatonBuilders
        .forDFA(FastDFA(Alphabets.fromList(List(err))))
        .withInitial("q0")
        .from("q0")
        .on(err)
        .to("q1")
        .withAccepting("q0")
        .create();

    val dltss = List(DLTS("ass1p", dfa1, dfa1.getInputAlphabet().toSet), DLTS("ass2", dfa2, dfa2.getInputAlphabet().toSet))
    val dltsssB = dltss.toBuffer
    val agv = dfa.DFAAutomaticVerifier(Array(File("examples/lts1.ta")), Some(DLTS.fromErrorSymbol(err)))
    agv.setAssumption(0, dltsssB(0))
    agv.setAssumption(1, dltsssB(1))
    // val cex = agv.checkInductivePremise(0)
    // assert(cex != None)
    //System.out.println(checker)

    val dfa1_p: FastDFA[String] =
    AutomatonBuilders
      .forDFA(FastDFA(Alphabets.fromList(List("c","d"))))
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
    
    val dltss_p = Buffer(DLTS("ass1p", dfa1_p, dfa1_p.getInputAlphabet().toSet), DLTS("ass2", dfa2, dfa2.getInputAlphabet().toSet))
    agv.setAssumption(0, dltss_p(0))
    agv.setAssumption(1, dltss_p(1))
    // val checker_p = agv.checkInductivePremise(0)
    // // System.out.println(s"inductive check 0: ${checker_p}")
    // assertEquals(checker_p, None)
 
    val dfa3 =
    AutomatonBuilders
      .forDFA(FastDFA(Alphabets.fromList(List("c","a","b", "err"))))
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
 
    // agv.assumptions = (DLTS("ass3", dfa3, dfa3.getInputAlphabet().toSet)::dltss_p.toList).toBuffer
    // val cex3 = agv.checkFinalPremise()
    // assertEquals(cex3, None)
    assert(None == agv.processes(0).checkTraceMembership(List[String]("c", "c", "err", "err"), Some(Set[String]("c", "err"))))
    assert(None != agv.processes(0).checkTraceMembership(List[String]("c", "c", "err"), Some(Set[String]("c", "err"))))
    assert(None != agv.processes(0).checkTraceMembership(List[String]("c", "b", "err"), Some(Set[String]("c", "err"))))
    // (checker_p.processes(0), dltss_p, DLTS("guarantee", errDFA, errDFA.getInputAlphabet()))
    val cex4 = DFAAutomaticVerifierAlphabetRefinement.extendTrace(agv.processes(0), List[String]("c", "c", "err"), None)
    // System.out.println(s"CEX4: ${cex4}")
    assert(cex4
      == Some(List("c","a","c", "err")))
  }
  test("mus-inline"){
    val inputs1: Alphabet[String] = Alphabets.fromList(List("req1","req2", "rel1", "rel2"))
    val gUser =
    AutomatonBuilders
      .forDFA(FastDFA(inputs1))
      .withInitial("q0")
      .from("q0")
      .on("req1")
      .to("q1")
      .from("q1")
      .on("rel1")
      .to("q0")
      .from("q0")
      .on("req2")
      .to("q2")
      .from("q2")
      .on("rel2")
      .to("q0")
      .withAccepting("q0")
      .withAccepting("q1")
      .withAccepting("q2")
      .create();
  
    // a* + a*d+
    val inputs2: Alphabet[String] = Alphabets.fromList(List("start1", "start2", "end1", "end2"))
    val gSched =
    AutomatonBuilders
      .forDFA(FastDFA(inputs2))
      .withInitial("q0")
      .from("q0")
      .on("start1")
      .to("q1")
      .from("q1")
      .on("end1")
      .to("q0")
      .from("q0")
      .on("start2")
      .to("q2")
      .from("q2")
      .on("end2")
      .to("q0")
      .withAccepting("q0")
      .withAccepting("q1")
      .withAccepting("q2")
      .create();

    val err = "err"
    val gMachine : FastDFA[String] =
      AutomatonBuilders
        .forDFA(FastDFA(Alphabets.fromList(List(err))))
        .withInitial("q0")
        .withAccepting("q0")
        .create();

    val errDFA : FastDFA[String] =
      AutomatonBuilders
        .forDFA(FastDFA(Alphabets.fromList(List(err))))
        .withInitial("q0")
        .from("q0")
        .on(err)
        .to("q1")
        .withAccepting("q0")
        .create();

    val ver = dfa.DFAAutomaticVerifier(Array(File("examples/ums/user.ta"), File("examples/ums/scheduler.ta"), File("examples/ums/machine.ta")), Some(DLTS.fromErrorSymbol("err")))
    ver.setAssumption(0, DLTS("user", gUser, gUser.getInputAlphabet().toSet))
    ver.setAssumption(1, DLTS("sched", gSched, gSched.getInputAlphabet().toSet))
    ver.setAssumption(2, DLTS("machine", gMachine, gMachine.getInputAlphabet().toSet))
    assert( None == ver.checkFinalPremise())
    ver.applyAG() match {
      case AGResult.Success => ()
      case _ => throw Exception("AG Verification failed")
    }
  
  }

  test("mus-inline-self"){
    val inputs1: Alphabet[String] = Alphabets.fromList(List("req1","req2", "rel1", "rel2", "grant1", "grant2"))
    val gUser =
    AutomatonBuilders
      .forDFA(FastDFA(inputs1))
      .withInitial("i")
      .from("i")
      .on("req1")
      .to("r1")
      .from("i")
      .on("req2")
      .to("r2")
      .from("r1")
      .on("grant1")
      .to("g1")
      .from("r2")
      .on("grant2")
      .to("g2")
      .from("g1")
      .on("rel1")
      .to("i")
      .from("g2")
      .on("rel2")
      .to("i")
      .withAccepting("i")
      .withAccepting("r2")
      .withAccepting("r1")
      .withAccepting("g1")
      .withAccepting("g2")
     .create();
  
    val inputs2: Alphabet[String] = Alphabets.fromList(List("start1", "start2", "end1", "end2","req1","req2", "rel1", "rel2", "grant1", "grant2"))
    val gSched =
    AutomatonBuilders
      .forDFA(FastDFA(inputs2))
      .withInitial("q0")
      .from("q0").on("req1").to("r1")
      .from("r1").on("grant1").to("g1")
      .from("g1").on("start1").to("s1")
      .from("s1").on("end1").to("e1")
      .from("e1").on("rel1").to("q0")

      .from("g1").on("req2").to("r2")
      .from("r1").on("req2").to("r2")
      .from("s1").on("req2").to("r2")

      .from("q0").on("req2").to("r2")
      .from("r2").on("grant2").to("g2")
      .from("g2").on("start2").to("s2")
      .from("s2").on("end2").to("e2")
      .from("e2").on("rel2").to("q0")

      .from("g2").on("req1").to("r1")
      .from("r2").on("req1").to("r1")
      .from("s2").on("req1").to("r1")

      .withAccepting("q0")
      .withAccepting("r1")
      .withAccepting("r2")
      .withAccepting("g1")
      .withAccepting("g2")
      .withAccepting("s1")
      .withAccepting("s2")
      .withAccepting("e1")
      .withAccepting("e2")

      .create();

    val err = "err"
    val gMachine : FastDFA[String] =
      AutomatonBuilders
        .forDFA(FastDFA(Alphabets.fromList(List(err,"start1","start2","end1", "end2"))))
        .withInitial("q0")
        .from("q0")
        .on("start1")
        .to("q1")
        .from("q0")
        .on("start2")
        .to("q2")
        .from("q1")
        .on("end1")
        .to("q0")
        .from("q2")
        .on("end2")
        .to("q0")
        // error
        .from("q1")
        .on("start1")
        .to("qerr")
        .from("q1")
        .on("start2")
        .to("qerr")
        .from("q2")
        .on("start1")
        .to("qerr")
        .from("q2")
        .on("start2")
        .to("qerr")
        .from("qerr")
        .on("err")
        .to("qerr")
        .withAccepting("q0")
        .withAccepting("q1")
        .withAccepting("q2")
        .withAccepting("qerr")
        .create();
    // Visualization.visualize(gMachine, gMachine.getInputAlphabet())
    // Visualization.visualize(gUser, gUser.getInputAlphabet())
    // Visualization.visualize(gSched, gSched.getInputAlphabet())
    val errDFA : FastDFA[String] =
      AutomatonBuilders
        .forDFA(FastDFA(Alphabets.fromList(List(err))))
        .withInitial("q0")
        .from("q0")
        .on(err)
        .to("q1")
        .withAccepting("q0")
        .create();
    // Visualization.visualize(errDFA, true)
    assert(!errDFA.isPrunedSafety)
    assert(errDFA.isSafety)
    assert(errDFA.pruned.isPrunedSafety)
    assert(gUser.isPrunedSafety)
    assert(gUser.isSafety)
    val ver = dfa.DFAAutomaticVerifier(Array(File("examples/ums/user.ta"), File("examples/ums/scheduler.ta"), File("examples/ums/machine.ta")), Some(DLTS.fromErrorSymbol("err")))
    ver.setAssumption(0, DLTS("user", gUser, gUser.getInputAlphabet().toSet))
    ver.setAssumption(1, DLTS("sched", gSched, gSched.getInputAlphabet().toSet))
    ver.setAssumption(2, DLTS("machine", gMachine, gMachine.getInputAlphabet().toSet))
    assert( None == ver.checkFinalPremise())
    ver.applyAG() match {
      case AGResult.Success => ()
      case _ => throw Exception("AG Verification failed")
    }
  }


  test("lts from file"){
    val files = Array(File("examples/toy/lts1.ta"),File("examples/toy/lts2.ta"),File("examples/toy/lts3.ta"))
    val verSAT = dfa.DFAAutomaticVerifier(files, Some(DLTS.fromErrorSymbol("err")), dfa.AssumptionGeneratorType.SAT)
    val verUFSAT = dfa.DFAAutomaticVerifier(files, Some(DLTS.fromErrorSymbol("err")), dfa.AssumptionGeneratorType.UFSAT)
    val verRPNI = dfa.DFAAutomaticVerifier(files, Some(DLTS.fromErrorSymbol("err")), dfa.AssumptionGeneratorType.RPNI)
    assert(verUFSAT.learnAssumptions() == AGResult.Success)
    assert(verSAT.learnAssumptions() == AGResult.Success)
    assert(verRPNI.learnAssumptions() == AGResult.Success)
  }

  test("seq-toy from file"){
    val files = Array(File("examples/seq-toy/lts0.ta"),File("examples/seq-toy/lts1.ta"),File("examples/seq-toy/lts2.ta"))
    val verUFSAT =  dfa.DFAAutomaticVerifier(files, Some(DLTS.fromErrorSymbol("err")), dfa.AssumptionGeneratorType.SAT)
    val verSAT =  dfa.DFAAutomaticVerifier(files, Some(DLTS.fromErrorSymbol("err")), dfa.AssumptionGeneratorType.SAT)
    val verRPNI = dfa.DFAAutomaticVerifier(files, Some(DLTS.fromErrorSymbol("err")), dfa.AssumptionGeneratorType.RPNI)
    assert(verRPNI.learnAssumptions() != AGResult.Success)
    assert(verSAT.learnAssumptions() != AGResult.Success)
    assert(verUFSAT.learnAssumptions() != AGResult.Success)

    val files2 = Array(File("examples/seq-toy/lts0.ta"),File("examples/seq-toy/lts1.ta"),File("examples/seq-toy/lts2.ta"),File("examples/seq-toy/lts3.ta"))
    val ver2SAT = dfa.DFAAutomaticVerifier(files2, Some(DLTS.fromErrorSymbol("err")), dfa.AssumptionGeneratorType.SAT)
    assert(ver2SAT.learnAssumptions() == AGResult.Success)
    val ver2UFSAT = dfa.DFAAutomaticVerifier(files2, Some(DLTS.fromErrorSymbol("err")), dfa.AssumptionGeneratorType.SAT)
    assert(ver2UFSAT.learnAssumptions() == AGResult.Success)
    val ver2RPNI = dfa.DFAAutomaticVerifier(files2, Some(DLTS.fromErrorSymbol("err")), dfa.AssumptionGeneratorType.RPNI)
    assert(ver2RPNI.learnAssumptions() == AGResult.Success)
  }

  test("regexp"){
    // DLTS.fromRegExp("ocan", "@a@b+(@c|@d)*@e?")
    val dlts = DLTS.fromRegExp("ocan", "(~(.*@start1[^@end1]*@start1.*))&(~(.*@start2[^@end2]*@start2.*))")
    // dlts.visualize()
    // val r = new RegExp("~(ab+(c|d)*e?)");
    val r = new RegExp("(a*b*c*)&(a*c*)");
    // val r = new RegExp("(a*)&(a*)");
    // System.out.println(r)
    // val r = new RegExp("(~(.*a[^b]*a.*)) ")
    val a = r.toAutomaton();
    val ba = new BricsNFA(a);
    assert(ba.accepts(List[Character]('a','c')))
    assert(!ba.accepts(List[Character]('a','b', 'c')))
    // AUTWriter.writeAutomaton(ba, ba.getIn)
    // Then, display a DOT representation of this automaton
    // Visualization.visualize(ba, true);
    // val r2 = dk.brics.automaton.RegExp("~(ab)")
    // val aut = r2.toAutomaton()
    // val baut : AbstractBricsAutomaton = BricsNFA(aut)
    // Visualization.visualize(baut, true)
  }

  test("ltl skeleton"){
    val skeleton = ltl.AGProofSkeleton(3)
    var processAlphabets = Buffer(Set[String]("a","b","c"), Set[String]("a","d"), Set[String]("d","e"))
    var propertyAlphabet = Set[String]("e")
    var commonAssumptionAlphabet = Set[String]("a","b","c","d","e")
    skeleton.updateByCone(processAlphabets, propertyAlphabet)
    assert((0 until 3).forall(skeleton.isCircular(_)))
    assert((0 until 3).forall({i => (0 until 3).forall({j => i == j || skeleton.processDependencies(i).contains(j)})}))

    skeleton.setProcessDependencies(0,Set(1))
    skeleton.setProcessDependencies(1,Set(0))
    assert((0 to 1).forall(skeleton.isCircular(_)))
    assert(!skeleton.isCircular(2))
  }
  test("dfa to string"){
   val inputs2: Alphabet[String] = Alphabets.fromList(List("start1", "start2", "end1", "end2"))
   val aut : DFA[java.lang.Integer, String] =
      AutomatonBuilders
        .newDFA(inputs2)
        // .forDFA(FastDFA(inputs2))
        .withInitial("q0")
        .from("q0")
        .on("start1")
        .to("q1")
        .from("q1")
        .on("end1")
        .to("q0")
        .from("q0")
        .on("start2")
        .to("q2")
        .from("q2")
        .on("end2")
        .to("q0")
        .withAccepting("q0")
        .withAccepting("q1")
        .withAccepting("q2")
        .create();
    // System.out.println(TAFWriter.dfaToString(gSched, inputs2))
    // SAFSerializationDFA.getInstance().writeModel(System.out, aut, inputs2)
    // System.out.println(AUTWriter.writeAutomaton(aut, inputs2, System.out))
  }  
}

class LTLAGTests extends munit.FunSuite {
  test("HOA"){
    val automatonString = """
        HOA: v1
        name: "G((!a | !b) & Fa & Fb)"
        States: 3
        Start: 0
        AP: 2 "a" "b"
        acc-name: Buchi
        Acceptance: 1 Inf(0)
        properties: trans-labels explicit-labels state-acc deterministic
        properties: stutter-invariant
        --BODY--
        State: 0
        [!1] 0
        [!0&1] 1
        State: 1
        [!0] 1
        [0&!1] 2
        State: 2 {0}
        [!1] 0
        [!0&1] 1
        --END--
    """
    val str2 = """
        HOA: v1
        States: 2
        Start: 0
        acc-name: Rabin 1
        Acceptance: 2 (Fin(0) & Inf(1))
        AP: 2 "a" "b"
        --BODY--
        State: 0 "a U b"   /* An example of named state */
          [0 & !1] 0 {0}
          [1] 1 {0}
        State: 1
          [t] 1 {1}
        --END--
    """
    val nlts = NLTS.fromLTL("G~(a U b)", Some(Set("a","b")))
    assert(nlts.dfa.accepts(List("a","a")))
    assert(!nlts.dfa.accepts(List("a","a","b")))
  }
  test("ltl parsing"){
    val input = "X M \"a\" | ! \"b\" \"c\""
    val ltl = LTL.fromLBT(input)
    assert(!ltl.isUniversal)
    val input2 = "G M \"a\" | ! \"b\" \"c\""
    val ltl2 = LTL.fromLBT(input2)
    assert(ltl2.isUniversal)
    assert(LTL.fromString("G F (a & !b)").isUniversal)
    // System.out.println(ltl)ltl.Not(
  }
  test("ltl asynchronous transformation"){
    val alph = Set("a","b")
    val falph = Or(List(Atomic("a"),Atomic("b")))
    val fnalph = Not(falph) // And(List(Not(Atomic("a")),Not(Atomic("b"))))
    val f1 = LTL.asynchronousTransform(Atomic("b"),alph)
    assert(f1 == U(Not(Or(Atomic("a"), Atomic("b"))), Atomic("b")))
    val f2 = LTL.asynchronousTransform(X(Atomic("b")),alph)
    val expected2 = U(fnalph, And(List(falph, X(U(fnalph, And(List(falph, f1)))))))
    assert(f2 == expected2)
    val f3 = LTL.asynchronousTransform(U(Atomic("b"), X(Atomic("b"))), alph)
    val expected3 = U(Implies(falph, f1), And(List(falph, f2)))
    assert(f3 == expected3)
  }
  test("ltl inductive check: ltl-toy1 a b"){
    // val ass = List("G ((a -> X !a) & !c)", "G F b")
    val ass = List("G ((a -> X !a))", "G F b")
    val ltl = ass.map(LTL.fromString)
    System.out.println(s"LTL assumptions: ${ltl}")
    val tas = Array(File("examples/ltl-toy1/a.ta"), File("examples/ltl-toy1/b.ta"))
    val checker = LTLVerifier(tas, G(F(Atomic("a"))))
    ltl.zipWithIndex.foreach( (ltl,i) => checker.setAssumption(i, ltl))
    // Without instantaneous assumptions, the proof fails:
    assert(checker.checkInductivePremise(0) != None)
    // By making an instantaneous assumption, the proof passes:
    checker.proofSkeleton.setProcessInstantaneousDependencies(0, Set(1))
    assert(checker.checkInductivePremise(0) == None)
    assert(checker.checkFinalPremise() != None)
  }
  test("ltl inductive check: ltl-toy1 a b - double G"){
    val ass = List("G ((a -> X !a))", "G G F b") // Spot will simplify G G to G
    val ltl = ass.map(LTL.fromString)
    System.out.println(s"LTL assumptions: ${ltl}")
    val tas = Array(File("examples/ltl-toy1/a.ta"), File("examples/ltl-toy1/b.ta"))
    val checker = LTLVerifier(tas, G(F(Atomic("a"))))
    checker.setAssumption(1, G(G(F(Atomic("b"))))) // Overwrite
    ltl.zipWithIndex.foreach( (ltl,i) => checker.setAssumption(i, ltl))
    // Without instantaneous assumptions, the proof fails:
    // assert(checker.checkInductivePremise(0) == None)
    // By making an instantaneous assumption, the proof passes:
    checker.proofSkeleton.setProcessInstantaneousDependencies(0, Set(1))
    assert(checker.checkInductivePremise(0) == None)
  }

  test("ltl inductive check w fairness: ltl-toy1 c d"){
    val ass = List("G F (a | b)", "G !d")
    val ltl = ass.map(LTL.fromString)
    System.out.println(s"LTL assumptions: ${ltl}")
    val tas = Array(File("examples/ltl-toy1/c.ta"), File("examples/ltl-toy1/d.ta"))
    val checker = LTLVerifier(tas, LTLTrue())
    ltl.zipWithIndex.foreach( (ltl,i) => checker.setAssumption(i, ltl))

    checker.proofSkeleton.setProcessInstantaneousDependencies(1, Set(0))

    // The proof fails without fairness assumption.
    // One possible counterexample is: b d a d^omega where {a,b}, the alphabet of process 0, is only seen finitely often
    assert(checker.checkInductivePremise(1,false) != None)
    // The proof succeeds under fairness:
    assert(checker.checkInductivePremise(1) == None)
  }
  test("ltl final premise check"){
    val ass = List("G ((a -> X !a) & !c)", "G (d -> (X c))")
    val ltl = ass.map(LTL.fromString)
    // System.out.println(s"LTL assumptions: ${ltl}")
    val tas = Array(File("examples/ltl-toy1/a.ta"), File("examples/ltl-toy1/b.ta"))
    val checker = LTLVerifier(tas, G(Not(Atomic("d"))))
    ltl.zipWithIndex.foreach( (ltl,i) => checker.setAssumption(i, ltl))
    System.out.println(checker.checkFinalPremise(true))
    assert(checker.checkFinalPremise(true) == None)
    
    val checker2 = LTLVerifier(tas, G(Not(Atomic("a"))))
    ltl.zipWithIndex.foreach( (ltl,i) => checker2.setAssumption(i, ltl))
    assert(checker2.checkFinalPremise() != None)
  } 
}

class Benjamin extends munit.FunSuite {
  test("ltl inductive check: ltl-toy1 a b - Benjamin"){
    val tas = Array(File("examples/ltl-toy1/a.ta"), File("examples/ltl-toy1/b.ta"))
    val checker = LTLVerifier(tas, G(F(Atomic("a"))))
    checker.setAssumption(0, G(LTLTrue()))
    checker.setAssumption(1, G(LTLTrue()))
    checker.proofSkeleton.setProcessInstantaneousDependencies(0, Set(1))
    // assert(checker.checkFinalPremise() != None)

    val ass0 = "G (( b-> X a) & (c -> !(F b)))"
    val ass1 = "G (( d-> X b) & F(c | d) & (c -> ! F c))"
    checker.setAssumption(0, LTL.fromString(ass0))
    checker.setAssumption(1, LTL.fromString(ass1))

    val ta0 = TA.fromFile(File("examples/ltl-toy1/a.ta"))
    System.out.println(LTL.fromString(ass0))
    // The property of ta0 actually holds without any assumption
    assert(ta0.checkLTL(LTL.fromString(ass0)) == None)
    // The proof of the inductive premise fails presumably due to asynchronous transformation requiring fairness
    assert(checker.checkInductivePremise(0, false) != None)
    // This passes with fairness
    assert(checker.checkInductivePremise(0, true) == None)
    assert(checker.checkFinalPremise() == None)
  }
}

class PartialLearning extends munit.FunSuite {

  test("mus-inline-self-partial-learning"){
    val inputs1: Alphabet[String] = Alphabets.fromList(List("req1","req2", "rel1", "rel2", "grant1", "grant2"))
    val gUser =
    AutomatonBuilders
      .forDFA(FastDFA(inputs1))
      .withInitial("i")
      .from("i")
      .on("req1")
      .to("r1")
      .from("i")
      .on("req2")
      .to("r2")
      .from("r1")
      .on("grant1")
      .to("g1")
      .from("r2")
      .on("grant2")
      .to("g2")
      .from("g1")
      .on("rel1")
      .to("i")
      .from("g2")
      .on("rel2")
      .to("i")
      .withAccepting("i")
      .withAccepting("r2")
      .withAccepting("r1")
      .withAccepting("g1")
      .withAccepting("g2")
     .create();
  
    val inputs2: Alphabet[String] = Alphabets.fromList(List("start1", "start2", "end1", "end2","req1","req2", "rel1", "rel2", "grant1", "grant2"))
    val gSched =
    AutomatonBuilders
      .forDFA(FastDFA(inputs2))
      .withInitial("q0")
      .from("q0").on("req1").to("r1")
      .from("r1").on("grant1").to("g1")
      .from("g1").on("start1").to("s1")
      .from("s1").on("end1").to("e1")
      .from("e1").on("rel1").to("q0")

      .from("g1").on("req2").to("r2")
      .from("r1").on("req2").to("r2")
      .from("s1").on("req2").to("r2")

      .from("q0").on("req2").to("r2")
      .from("r2").on("grant2").to("g2")
      .from("g2").on("start2").to("s2")
      .from("s2").on("end2").to("e2")
      .from("e2").on("rel2").to("q0")

      .from("g2").on("req1").to("r1")
      .from("r2").on("req1").to("r1")
      .from("s2").on("req1").to("r1")

      .withAccepting("q0")
      .withAccepting("r1")
      .withAccepting("r2")
      .withAccepting("g1")
      .withAccepting("g2")
      .withAccepting("s1")
      .withAccepting("s2")
      .withAccepting("e1")
      .withAccepting("e2")

      .create();

    val err = "err"
    val gMachine : FastDFA[String] =
      AutomatonBuilders
        .forDFA(FastDFA(Alphabets.fromList(List(err,"start1","start2","end1", "end2"))))
        .withInitial("q0")
        .from("q0")
        .on("start1")
        .to("q1")
        .from("q0")
        .on("start2")
        .to("q2")
        .from("q1")
        .on("end1")
        .to("q0")
        .from("q2")
        .on("end2")
        .to("q0")
        // error
        .from("q1")
        .on("start1")
        .to("qerr")
        .from("q1")
        .on("start2")
        .to("qerr")
        .from("q2")
        .on("start1")
        .to("qerr")
        .from("q2")
        .on("start2")
        .to("qerr")
        .from("qerr")
        .on("err")
        .to("qerr")
        .withAccepting("q0")
        .withAccepting("q1")
        .withAccepting("q2")
        .withAccepting("qerr")
        .create();
    // Visualization.visualize(gMachine, gMachine.getInputAlphabet())
    // Visualization.visualize(gUser, gUser.getInputAlphabet())
    // Visualization.visualize(gSched, gSched.getInputAlphabet())
    val errDFA : FastDFA[String] =
      AutomatonBuilders
        .forDFA(FastDFA(Alphabets.fromList(List(err))))
        .withInitial("q0")
        .from("q0")
        .on(err)
        .to("q1")
        .withAccepting("q0")
        .create();
    // Visualization.visualize(errDFA, true)
    assert(!errDFA.isPrunedSafety)
    assert(errDFA.isSafety)
    assert(errDFA.pruned.isPrunedSafety)
    assert(gUser.isPrunedSafety)
    assert(gUser.isSafety)
    val ver = dfa.DFAAutomaticVerifier(Array(File("examples/ums/user.ta"), File("examples/ums/scheduler.ta"), File("examples/ums/machine.ta")), Some(DLTS.fromErrorSymbol("err")))
    ver.setAssumption(0, DLTS("user", gUser, gUser.getInputAlphabet().toSet))
    ver.setAssumption(1, DLTS("sched", gSched, gSched.getInputAlphabet().toSet))
    ver.setAssumption(2, DLTS("machine", gMachine, gMachine.getInputAlphabet().toSet))
    configuration.set(configuration.get().copy(verbose_MembershipQueries = true))
    assert(ver.learnAssumptions(true, (List(0,1))) == AGResult.Success)
    assert(ver.learnAssumptions(true, (List(1,2))) == AGResult.Success)
  }
}

class Single extends munit.FunSuite{
  test("dfa clusters"){
    val files = Array(File("examples/ltl-toy1/a.ta"), File("examples/ltl-toy1/b.ta"), File("examples/ltl-toy1/b.ta"), File("examples/ltl-toy1/b.ta"))
    val nbProcesses =files.size
    val ver = DFAVerifier(files)
    for i <- 0 until nbProcesses do {
      ver.setAssumption(i, DLTS.fromTChecker(files(i)))
    }
    // ver.proofSkeleton.processDependencies(3) = Set(1)
    // ver.proofSkeleton.processDependencies(1) = Set(2)
    // ver.proofSkeleton.processDependencies(2) = Set(1,0)
    // ver.proofSkeleton.processDependencies(0) = Set[Int]()
    // System.out.println("\n")
    // ver.proofSkeleton.updateClusters()
  } 
  test("proof invalidation"){
    val filenames = Array("examples/seq-toy/lts0.ta", "examples/seq-toy/lts1.ta", "examples/seq-toy/lts2.ta", "examples/seq-toy/lts3.ta")
    val int = Interactive(filenames.toList)
    val nbProcesses = filenames.size
    for i <- 0 until nbProcesses do {
        int.setDFAAssumption(i, DLTS.fromTChecker(File(filenames(i))))
    }
    int.checkDFAAssumption(0)
    int.checkDFAAssumption(1)
    assert(int.getDFAProofState(0) == DFAProofState.PremiseSucceeded)
    assert(int.getDFAProofState(1) == DFAProofState.PremiseSucceeded)
    int.setDFAAssumption(3, DLTS.fromTChecker(File(filenames(3))))
    assert(int.getDFAProofState(0) == DFAProofState.PremiseSucceeded)
    assert(int.getDFAProofState(1) == DFAProofState.PremiseSucceeded)

    int.setDFAAssumptionDependencies(0,Set[Int]())
    int.setDFAAssumptionDependencies(1,Set(2))
    int.setDFAAssumptionDependencies(2, Set(1,0))
    int.setDFAAssumptionDependencies(3, Set(1))
    int.checkDFAAssumption(0)
    int.checkDFAAssumption(1)
    int.checkDFAAssumption(2)
    int.checkDFAAssumption(3)
    int.setDFAAssumption(2, DLTS.fromTChecker(File(filenames(2))))
    assert(int.getDFAProofState(0) == DFAProofState.Proved)
    assert(int.getDFAProofState(1) == DFAProofState.Unknown)
    assert(int.getDFAProofState(2) == DFAProofState.Unknown)
    assert(int.getDFAProofState(3) == DFAProofState.Unknown)
    int.checkDFAAssumption(0)
    int.checkDFAAssumption(1)
    int.checkDFAAssumption(2)
    int.checkDFAAssumption(3)
    int.setDFAAssumption(3, DLTS.fromTChecker(File(filenames(2))))
    assert(int.getDFAProofState(0) == DFAProofState.Proved)
    assert(int.getDFAProofState(1) == DFAProofState.Proved)
    assert(int.getDFAProofState(2) == DFAProofState.Proved)

  }
}
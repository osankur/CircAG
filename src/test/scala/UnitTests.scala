package fr.irisa.circag


import net.automatalib.serialization.saf.SAFSerializationDFA 
import net.automatalib.serialization.aut.AUTWriter 

import java.util.HashMap
import java.io.File
import collection.JavaConverters._
import collection.convert.ImplicitConversions._
import collection.mutable.{Buffer}
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
    // System.out.println(solver.getProof())
    // for ass <- solver.getUnsatCore() do {
    //   System.out.println(ass)
    // }    
  }
}

class TAandLTSTests extends munit.FunSuite {
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
    println(trace)
    assert(trace == List("a","b","c","a"))
  }
  test("Lasso graph parsing optimizations"){
    // val tck_output = """digraph _hoa_ {
    //   0 [initial="true", intval="", labels="", vloc="<qs0>", zone="()"]
    //   1 [final="true", intval="", labels="_hoa__ltl_acc_", vloc="<qs3>", zone="()"]
    //   0 -> 1 [guard="", reset="", src_invariant="", tgt_invariant="", vedge="<_hoa_@a>"]
    //   1 -> 1 [guard="", reset="", src_invariant="", tgt_invariant="", vedge="<_hoa_@a>"]
    //   }"""
    val tck_output1 = """digraph _hoa_ {
      0 [final="true", intval="", labels="", vloc="<qs0>", zone="()"]
      1 [final="true", intval="", labels="", vloc="<qs0>", zone="()"]
      0 -> 1 [guard="", reset="", src_invariant="", tgt_invariant="", vedge="<_hoa_@a>"]
      1 -> 1 [guard="", reset="", src_invariant="", tgt_invariant="", vedge="<_hoa_@a>"]
      }"""
    val tck_output2 = """digraph _hoa_ {
      0 [vloc="<qs2>"]
      1 [vloc="<qs0>"]
      2 [vloc="<qs0>"]
      0 -> 1 [guard="", reset="", src_invariant="", tgt_invariant="", vedge="<_hoa_@a>"]
      1 -> 2 [guard="", reset="", src_invariant="", tgt_invariant="", vedge="<_hoa_@b>"]
      2 -> 2 [guard="", reset="", src_invariant="", tgt_invariant="", vedge="<_hoa_@c>"]
      }"""
    val tck_output3 = """digraph _hoa_ {
      0 [vloc="<qs2>"]
      1 [vloc="<qs1>"]
      2 [vloc="<qs2>"]
      3 [vloc="<qs0>"]
      0 -> 1 [guard="", reset="", src_invariant="", tgt_invariant="", vedge="<_hoa_@a>"]
      1 -> 2 [guard="", reset="", src_invariant="", tgt_invariant="", vedge="<_hoa_@b>"]
      2 -> 3 [guard="", reset="", src_invariant="", tgt_invariant="", vedge="<_hoa_@c>"]
      3 -> 3 [guard="", reset="", src_invariant="", tgt_invariant="", vedge="<_hoa_@c>"]
      }"""
    val tck_output4 = """digraph _hoa_ {
      0 [vloc="<qs1>"]
      1 [vloc="<qs2>"]
      2 [vloc="<qs2>"]
      3 [vloc="<qs0>"]
      0 -> 1 [guard="", reset="", src_invariant="", tgt_invariant="", vedge="<_hoa_@a>"]
      1 -> 2 [guard="", reset="", src_invariant="", tgt_invariant="", vedge="<_hoa_@b>"]
      2 -> 3 [guard="", reset="", src_invariant="", tgt_invariant="", vedge="<_hoa_@c>"]
      3 -> 3 [guard="", reset="", src_invariant="", tgt_invariant="", vedge="<_hoa_@c>"]
      }"""
    val tck_output5 = """digraph _hoa_ {
      0 [vloc="<qs1>"]
      1 [vloc="<qs2>"]
      2 [vloc="<qs2>"]
      3 [vloc="<qs0>"]
      0 -> 1 [guard="", reset="", src_invariant="", tgt_invariant="", vedge="<_hoa_@a>"]
      1 -> 2 [guard="", reset="", src_invariant="", tgt_invariant="", vedge="<_hoa_@b>"]
      2 -> 3 [guard="", reset="", src_invariant="", tgt_invariant="", vedge="<_hoa_@c>"]
      3 -> 2 [guard="", reset="", src_invariant="", tgt_invariant="", vedge="<_hoa_@c>"]
      }"""
    val trace1 = TA.getLassoFromCounterExampleOutput(tck_output1.split("\n").toList, Set("a","b","c"))
    assert(trace1 == (List(),List("a")))

    val trace2 = TA.getLassoFromCounterExampleOutput(tck_output2.split("\n").toList, Set("a","b","c"))    
    assert(trace2 == (List("a"),List("c")))

    val trace3 = TA.getLassoFromCounterExampleOutput(tck_output3.split("\n").toList, Set("a","b","c"))    
    assert(trace3 == (List("c"),List("c")))

    val trace4 = TA.getLassoFromCounterExampleOutput(tck_output4.split("\n").toList, Set("a","b","c")) 
    assert(trace4 == (List("a","c"),List("c")))

    val trace5 = TA.getLassoFromCounterExampleOutput(tck_output5.split("\n").toList, Set("a","b","c")) 
    assert(trace5 == (List("a"),List("c","c")))
    // println(trace5)
  }  
  test("DLTS from fromTrace"){
    val dlts = DLTS.fromTrace(List("a","b","c","a"))
    assert(dlts.dfa.accepts(List("a","b","c", "a")))
    assert(!dlts.dfa.accepts(List("a","a","a")))
    assert(!dlts.dfa.accepts(List("a","b","b")))
  }
  test("Read TA fromTCheckerFile"){
    val dlts = DLTS.fromTCheckerFile(java.io.File("examples/simple-sdn/observer.tck"))
    assert(dlts.dfa.accepts(List("send", "change", "ack")))
    assert(dlts.dfa.accepts(List("send", "change", "send","err")))
    assert(!dlts.dfa.accepts(List("send", "change", "send","send")))
  }

  test("regexp"){
    val dlts = DLTS.fromRegExp("ocan", "(~(.*@start1[^@end1]*@start1.*))&(~(.*@start2[^@end2]*@start2.*))")
    val r = new RegExp("(a*b*c*)&(a*c*)");
    val a = r.toAutomaton();
    val ba = new BricsNFA(a);
    assert(ba.accepts(List[Character]('a','c')))
    assert(!ba.accepts(List[Character]('a','b', 'c')))
  }
  test("lasso-semantic-equals"){
    val l1 : Lasso = (List("a","b"), List("a", "c"))
    val l2 : Lasso = (List("a","b","a"), List("c", "a"))
    val l3 : Lasso = (List("a","b","a"), List("c", "a", "c", "a"))
    val l4 : Lasso = (List("a","b","a"), List("c", "a", "c"))
    assert(l1.semanticEquals(l1))
    assert(l1.semanticEquals(l2))
    assert(l1.semanticEquals(l3))
    assert(l2.semanticEquals(l1))
    assert(l3.semanticEquals(l1))
    assert(!l4.semanticEquals(l1))
    assert(!l1.semanticEquals(l4))
  }
  test("ta from lasso"){
    val l3 : Lasso = (List("a","b","a"), List("c", "a", "c", "a"))
    val f1 = G(F(Atomic("a")))
    val f2 = F(G(Not(Atomic("b"))))
    val f3 = F(G(Not(Atomic("c"))))

    assert(f1.accepts(l3))
    assert(f2.accepts(l3))
    assert(!f3.accepts(l3))
  }
  test("lasso membership"){
    val ta = TA.fromFile(File("examples/simple.tck"))
    val l1 : Lasso = (List("a","a","b"), List("c", "a", "c", "a"))
    val l2 : Lasso = (List("b"), List("c"))
    val l3 : Lasso = (List("b","b"), List("c"))
    assert(ta.checkLassoMembership(l1) != None)
    assert(ta.checkLassoMembership(l2) != None)
    assert(ta.checkLassoMembership(l3) == None)
  }
  test("lasso as suffix"){
     val ta = TA.fromFile(File("examples/simple.tck"))
     assert(ta.checkLassoSuffixMembership((List(),List("c","a"))) != None)
     assert(ta.checkLassoSuffixMembership((List("b"),List("c","a")))!= None)
     assert(ta.checkLassoSuffixMembership((List("a"),List("a","a")))!= None)
     assert(ta.checkLassoSuffixMembership((List("a"),List("b","c","a"))) == None)
  }
  test("lasso as suffix"){
     val ta = TA.fromFile(File("examples/simple-sdn/controller.tck"))
     val lasso = (List("change"),List("change"))
     assert(ta.checkLassoMembership(lasso) != None)
     assert(ta.checkLassoMembership(lasso,Some(ta.alphabet)) == None)
  }

}
class DFAAAG extends munit.FunSuite {
  test("sat learner"){
    val satLearner = dfa.SATLearner("ass", Set("a","b","c"))
    val positives = Set(List("a","b","c"),List("c","c"))
    val negatives = Set(List("b","c"),List("a","b","b"))
    satLearner.setPositiveSamples(positives)
    satLearner.setNegativeSamples(negatives)
    val dlts = satLearner.getDLTS()
    positives.foreach(x => assert(dlts.dfa.accepts(x)))
    negatives.foreach(x => assert(!dlts.dfa.accepts(x)))
  }

  test("premiseChecker"){
    // {a,c,d}*
    val inputs1: Alphabet[String] = Alphabets.fromList(List("c","d", "a", "err"))
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
    val agv = dfa.DFAAutomaticVerifier(Array(File("examples/lts1.ta"), File("examples/lts1.ta")), Some(DLTS.fromErrorSymbol(err)), dfa.DFALearningAlgorithm.RPNI)
    agv.setAssumption(0, dltsssB(0))

    assert(None == agv.system.processes(0).checkTraceMembership(List[String]("c", "c", "err", "err"), Some(Set[String]("c", "err"))))
    assert(None != agv.system.processes(0).checkTraceMembership(List[String]("c", "c", "err"), Some(Set[String]("c", "err"))))
    assert(None != agv.system.processes(0).checkTraceMembership(List[String]("c", "b", "err"), Some(Set[String]("c", "err"))))
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

    val ver = dfa.DFAAutomaticVerifier(Array(File("examples/ums/user.ta"), File("examples/ums/scheduler.ta"), File("examples/ums/machine.ta")), Some(DLTS.fromErrorSymbol("err")),dfa.DFALearningAlgorithm.RPNI)
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
    val ver = dfa.DFAAutomaticVerifier(Array(File("examples/ums/user.ta"), File("examples/ums/scheduler.ta"), File("examples/ums/machine.ta")), Some(DLTS.fromErrorSymbol("err")), dfa.DFALearningAlgorithm.RPNI)
    ver.setAssumption(0, DLTS("user", gUser, gUser.getInputAlphabet().toSet))
    ver.setAssumption(1, DLTS("sched", gSched, gSched.getInputAlphabet().toSet))
    ver.setAssumption(2, DLTS("machine", gMachine, gMachine.getInputAlphabet().toSet))
    assert( None == ver.checkFinalPremise())
    ver.applyAG() match {
      case AGResult.Success => ()
      case _ => throw Exception("AG Verification failed")
    }
  }


  test("toy: with SAT, UFSAT, RPNI"){
    val files = Array(File("examples/toy/lts1.ta"),File("examples/toy/lts2.ta"),File("examples/toy/lts3.ta"))
    val verSAT = dfa.DFAAutomaticVerifier(files, Some(DLTS.fromErrorSymbol("err")), dfa.DFALearningAlgorithm.SAT)
    val verUFSAT = dfa.DFAAutomaticVerifier(files, Some(DLTS.fromErrorSymbol("err")), dfa.DFALearningAlgorithm.UFSAT)
    val verRPNI = dfa.DFAAutomaticVerifier(files, Some(DLTS.fromErrorSymbol("err")), dfa.DFALearningAlgorithm.RPNI)
    assert(verUFSAT.learnAssumptions() == AGResult.Success)
    assert(verSAT.learnAssumptions() == AGResult.Success)
    assert(verRPNI.learnAssumptions() == AGResult.Success)
  }

  test("seq-toy"){
    val files = Array(File("examples/seq-toy/lts0.ta"),File("examples/seq-toy/lts1.ta"),File("examples/seq-toy/lts2.ta"))
    val verUFSAT =  dfa.DFAAutomaticVerifier(files, Some(DLTS.fromErrorSymbol("err")), dfa.DFALearningAlgorithm.SAT)
    val verSAT =  dfa.DFAAutomaticVerifier(files, Some(DLTS.fromErrorSymbol("err")), dfa.DFALearningAlgorithm.SAT)
    val verRPNI = dfa.DFAAutomaticVerifier(files, Some(DLTS.fromErrorSymbol("err")), dfa.DFALearningAlgorithm.RPNI)
    assert(verRPNI.learnAssumptions() != AGResult.Success)
    assert(verSAT.learnAssumptions() != AGResult.Success)
    assert(verUFSAT.learnAssumptions() != AGResult.Success)

    val files2 = Array(File("examples/seq-toy/lts0.ta"),File("examples/seq-toy/lts1.ta"),File("examples/seq-toy/lts2.ta"),File("examples/seq-toy/lts3.ta"))
    val ver2SAT = dfa.DFAAutomaticVerifier(files2, Some(DLTS.fromErrorSymbol("err")), dfa.DFALearningAlgorithm.SAT)
    assert(ver2SAT.learnAssumptions() == AGResult.Success)
    val ver2UFSAT = dfa.DFAAutomaticVerifier(files2, Some(DLTS.fromErrorSymbol("err")), dfa.DFALearningAlgorithm.SAT)
    assert(ver2UFSAT.learnAssumptions() == AGResult.Success)
    val ver2RPNI = dfa.DFAAutomaticVerifier(files2, Some(DLTS.fromErrorSymbol("err")), dfa.DFALearningAlgorithm.RPNI)
    assert(ver2RPNI.learnAssumptions() == AGResult.Success)
  }

  test("ltl skeleton"){
    val skeleton = ltl.LTLProofSkeleton(3)
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

class LTLTests extends munit.FunSuite {
  test("ltl parsing"){
    val input = "X M \"a\" | ! \"b\" \"c\""
    val ltl = LTL.fromLBT(input)
    assert(!ltl.isUniversal)
    val input2 = "G M \"a\" | ! \"b\" \"c\""
    val ltl2 = LTL.fromLBT(input2)
    assert(ltl2.isUniversal)
    assert(LTL.fromString("G F (a & !b)").isUniversal)
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
  test("lasso |= LTL"){
    val lassoTA = TA.fromLTS(DLTS.fromLasso((List("a"), List("a"))))
    val f = Atomic("b")
    val g = And(Atomic("b"), X(Atomic("a")))
    val h = G(Atomic("a"))
    assert(lassoTA.checkLTL(f) != None)
    assert(lassoTA.checkLTL(g) != None)
    assert(lassoTA.checkLTL(h) == None)
  }
  test("ta |= LTL"){
    val ta = TA.fromFile(File("examples/simple-sdn/controller.tck"))
    assert(ta.checkLTL(G(F(Atomic("change")))) != None)
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
  test("violation index"){
    val tas = Array(File("examples/ltl-toy1/a.ta"), File("examples/ltl-toy1/b.ta"))
    val checker = LTLAutomaticVerifier(ltl.SystemSpec(tas, G(F(Atomic("a")))))
    val query = CircularPremiseQuery(1, List(), List((0,(Atomic("b")))), List(), Atomic("d"), LTLTrue())
    val lasso = (List("a","a","c"), List("c"))
    assert(checker.getPremiseViolationIndex(lasso, query) == 0)

    val lasso2 = (List("d","d","d"), List("d", "a"))
    assert(checker.getPremiseViolationIndex(lasso2, query) == 4)
  }  

  test("ltl inductive check: ltl-toy1 a b"){
    // val ass = List("G ((a -> X !a) & !c)", "G F b")
    val ass = List("G ((a -> X !a))", "G F b")
    val ltlf = ass.map(LTL.fromString)
    System.out.println(s"LTL assumptions: ${ltlf}")
    val tas = Array(File("examples/ltl-toy1/a.ta"), File("examples/ltl-toy1/b.ta"))    
    val checker = LTLVerifier(ltl.SystemSpec(tas, G(F(Atomic("a")))))
    ltlf.zipWithIndex.foreach( (ltl,i) => checker.setAssumption(i, ltl))
    // Without instantaneous assumptions, the proof fails:
    assert(checker.checkInductivePremise(0) != None)
    // By making an instantaneous assumption, the proof passes:
    checker.setProcessInstantaneousDependencies(0, Set(1))
    assert(checker.checkInductivePremise(0) == None)
    assert(checker.checkFinalPremise() != None)
  }
  test("ltl inductive check: ltl-toy1 a b - double G"){
    val ass = List("G ((a -> X !a))", "G G F b") // Spot will simplify G G to G
    val ltlf = ass.map(LTL.fromString)
    System.out.println(s"LTL assumptions: ${ltlf}")
    val tas = Array(File("examples/ltl-toy1/a.ta"), File("examples/ltl-toy1/b.ta"))
    val checker = LTLVerifier(ltl.SystemSpec(tas, G(F(Atomic("a")))))
    checker.setAssumption(1, G(G(F(Atomic("b"))))) // Overwrite
    ltlf.zipWithIndex.foreach( (ltl,i) => checker.setAssumption(i, ltl))
    // Without instantaneous assumptions, the proof fails:
    // assert(checker.checkInductivePremise(0) == None)
    // By making an instantaneous assumption, the proof passes:
    checker.setProcessInstantaneousDependencies(0, Set(1))
    assert(checker.checkInductivePremise(0) == None)
  }

  test("ltl inductive check w fairness: ltl-toy1 c d"){
    val ass = List("G F (a | b)", "G !d")
    val ltlf = ass.map(LTL.fromString)
    System.out.println(s"LTL assumptions: ${ltlf}")
    val tas = Array(File("examples/ltl-toy1/c.ta"), File("examples/ltl-toy1/d.ta"))
    val checker = LTLVerifier(ltl.SystemSpec(tas, LTLTrue()))
    ltlf.zipWithIndex.foreach( (ltl,i) => checker.setAssumption(i, ltl))

    checker.setProcessInstantaneousDependencies(1, Set(0))

    // The proof fails without fairness assumption.
    // One possible counterexample is: b d a d^omega where {a,b}, the alphabet of process 0, is only seen finitely often
    assert(checker.checkInductivePremise(1,false) != None)
    // The proof succeeds under fairness:
    assert(checker.checkInductivePremise(1) == None)
  }
  test("ltl final premise check"){
    val ass = List("G ((a -> X !a) & !c)", "G (d -> (X c))")
    val ltlf = ass.map(LTL.fromString)
    // System.out.println(s"LTL assumptions: ${ltl}")
    val tas = Array(File("examples/ltl-toy1/a.ta"), File("examples/ltl-toy1/b.ta"))
    val checker = LTLVerifier(ltl.SystemSpec(tas, G(Not(Atomic("d")))))
    ltlf.zipWithIndex.foreach( (ltl,i) => checker.setAssumption(i, ltl))
    System.out.println(checker.checkFinalPremise(true))
    assert(checker.checkFinalPremise(true) == None)
    
    val checker2 = LTLVerifier(tas, G(Not(Atomic("a"))))
    ltlf.zipWithIndex.foreach( (ltl,i) => checker2.setAssumption(i, ltl))
    assert(checker2.checkFinalPremise() != None)
  } 

  test("TA Buchi check"){
    val ta = TA.fromFile(File("examples/simple.tck"))
    assert(ta.checkBuchi("3") == Some(List("a","b"), List("c", "a")))
    assert(ta.checkBuchi("4") == None)
  }


  test("sat-ltl-learner"){
    val learner = ltl.SATLearner("a", Set("a","b","c"), universal= true, ltl.LTLLearningAlgorithm.Samples2LTL)
    learner.setPositiveSamples(Set((List("a","b"), List("c"))))
    learner.setNegativeSamples(Set((List("b","b"), List("b")), (List("a","a"), List("b","b"))))
    learner.getLTL() match {
      case None => assert(false)
      case Some(ltl) => assert(ltl.toString == "(G (F c))")
    }

    val learner2 = ltl.SATLearner("a", Set("a","b","c"), universal= true, ltl.LTLLearningAlgorithm.Scarlet)
    learner2.setPositiveSamples(Set((List("a","b"), List("c"))))
    learner2.setNegativeSamples(Set((List("b","b"), List("b")), (List("a","a"), List("b","b"))))
    learner2.getLTL() match {
      case None => assert(false)
      case Some(ltl) => assert(ltl.toString == "(G (F c))")
    }
  }
  test("sat-ltl-learner2"){
    val learner = ltl.SATLearner("formula", Set("a","b","c"), universal=true, ltl.LTLLearningAlgorithm.Samples2LTL)
    val pos = Set((List(),List("a", "b")), (List("a", "b"),List("a", "b")))
    val neg = Set((List("c"),List("c")))
    println(learner.getLTL())
  }
  test("ltl inductive check: ltl-toy1 a b"){
    // val ass = List("G ((a -> X !a) & !c)", "G F b")
    val ass = List("G ((a -> X !a))", "G F b")
    val ltlf = ass.map(LTL.fromString)
    System.out.println(s"LTL assumptions: ${ltlf}")
    val tas = Array(File("examples/ltl-toy1/a.ta"), File("examples/ltl-toy1/b.ta"))
    val checker = LTLVerifier(tas, G(F(Atomic("a"))))
    ltlf.zipWithIndex.foreach( (ltl,i) => checker.setAssumption(i, ltl))
    // Without instantaneous assumptions, the proof fails:
    assert(checker.checkInductivePremise(0) != None)
    // By making an instantaneous assumption, the proof passes:
    checker.setProcessInstantaneousDependencies(0, Set(1))
    assert(checker.checkInductivePremise(0) == None)
    assert(checker.checkFinalPremise() != None)
  } 
}

class DFAAutomatic extends munit.FunSuite {
 test("DFA learn assumptions: simple sdn"){
    val tas = Array(File("examples/simple-sdn/device.tck"), File("examples/simple-sdn/switch.tck"), File("examples/simple-sdn/controller.tck"), File("examples/simple-sdn/supervisor.tck"), File("examples/simple-sdn/observer.tck"))
    val dfaChecker = DFAAutomaticVerifier(tas, Some(DLTS.fromErrorSymbol("err")), dfa.DFALearningAlgorithm.RPNI)
    dfaChecker.learnAssumptions(true)
  }
 test("DFA learn assumptions: full sdn"){
    val tas = Array(File("examples/sdn/device.tck"), File("examples/sdn/switch.tck"), File("examples/sdn/controller.tck"), File("examples/sdn/supervisor.tck"), File("examples/sdn/observer.tck"))
    val dfaChecker = DFAAutomaticVerifier(tas, Some(DLTS.fromErrorSymbol("err")), dfa.DFALearningAlgorithm.RPNI)
    dfaChecker.learnAssumptions(true)
  }
}
class LTLAutomatic  extends munit.FunSuite {
  test("ltl learn assumptions: sdn"){
      val tas = Array(File("examples/simple-sdn/device.tck"), File("examples/simple-sdn/switch.tck"), File("examples/simple-sdn/controller.tck"), File("examples/simple-sdn/supervisor.tck"), File("examples/simple-sdn/observer.tck"))
      val ltlChecker = LTLAutomaticVerifier(ltl.SystemSpec(tas, (F(Atomic("change")))))
      ltlChecker.setAssumptionAlphabet(1, Set("change","send"))
      ltlChecker.setAssumptionAlphabet(2, Set("change","ack","send"))
      // ~100s
      ltlChecker.learnAssumptions(true)
    }
  test("ltl learn assumptions: muo 2 processes"){
    val tas = Array(File("examples/muo/user.tck"), File("examples/muo/machine.tck"))
    val checker = LTLAutomaticVerifier(ltl.SystemSpec(tas, G(F(Atomic("cycle")))))
    checker.setProcessInstantaneousDependencies(1, Set(0))
    // this should take 15 attempts
    val result2 = checker.learnAssumptions(proveGlobalProperty = true)
    assert(result2 == ltl.LTLAGResult.Success)
    // One can also check just F send much faster
  }
  test("ltl learn assumptions: ltl-toy1 2 processes"){
    val tas = Array(File("examples/ltl-toy1/a.ta"), File("examples/ltl-toy1/b.ta"))
    val checker = LTLAutomaticVerifier(ltl.SystemSpec(tas, G(F(Atomic("a")))))
    checker.setProcessInstantaneousDependencies(0, Set(1))
    val result = checker.learnAssumptions(proveGlobalProperty = true)
    assert(result == ltl.LTLAGResult.Success)
  }

  test("ltl learn assumptions: ums-1task"){
    val tas = Array(File("examples/ltl-toy1/a.ta"), File("examples/ltl-toy1/b.ta"))
    val checker = LTLAutomaticVerifier(ltl.SystemSpec(tas, G(F(Atomic("a")))))
    checker.setProcessInstantaneousDependencies(0, Set(1))
    val result = checker.learnAssumptions(proveGlobalProperty = true)
    assert(result == ltl.LTLAGResult.Success)
  }

}

class Single extends munit.FunSuite {
  test("ltl learn assumptions: ltl-toy1 2 processes"){
    val tas = Array(File("examples/ltl-toy1/a.ta"), File("examples/ltl-toy1/b.ta"))
    val checker = LTLAutomaticVerifier(ltl.SystemSpec(tas, G(F(Atomic("a")))))
    checker.setProcessInstantaneousDependencies(0, Set(1))
    assert(checker.learnAssumptions(proveGlobalProperty = true) == LTLAGResult.Success)
  }
  test("ltl learn assumptions: ltl-toy1 3 processes"){
    val tas = Array(File("examples/ltl-toy1/a.ta"), File("examples/ltl-toy1/b.ta"), File("examples/ltl-toy1/c.ta"))
    val checker = LTLAutomaticVerifier(ltl.SystemSpec(tas, G(F(Atomic("a")))))
    checker.setProcessInstantaneousDependencies(0, Set(1))
    // The learned assumptions are: G (b -> (X a))) and (G (c U b)
    // This corresponds to the only infinite execution in this product: abaac^omega
    assert(checker.learnAssumptions(proveGlobalProperty = true) == LTLAGResult.Success)
  }
  test("ltl inductive check: ltl-toy1 applyAG"){
    val tas = Array(File("examples/ltl-toy1/a.ta"), File("examples/ltl-toy1/b.ta"))
    val checker = LTLVerifier(ltl.SystemSpec(tas, G(F(Atomic("a")))))
    checker.setAssumption(0, G(LTLTrue()))
    checker.setAssumption(1, G(LTLTrue()))
    checker.setProcessInstantaneousDependencies(0, Set(1))
    val ass0 = LTL.fromString("G (( b-> X a) & (c -> !(F b)))")
    val ass1 = LTL.fromString("G (( d-> X b) & (c -> !X(F c)))")
    val ass1_ = LTL.fromString("G (( d-> X b) & F(c | d) & (c -> ! F c))")
    checker.setAssumption(0, (ass0))
    checker.setAssumption(1, (ass1))
    assert(TA.fromFile(tas(0)).checkLTL(ass0) == None)
    assert(TA.fromFile(tas(1)).checkLTL(ass1) == None)
    assert(checker.applyAG(proveGlobalproperty = false) == LTLAGResult.Success)
    assert(checker.applyAG(proveGlobalproperty = true) == LTLAGResult.Success)
  }
}

class A extends munit.FunSuite {

  // test("ltl learn assumptions: ums"){
  //   // This does not terminate :()
  //   val tas = Array(File("examples/ums-1task/user.tck"), File("examples/ums-1task/scheduler.tck"), File("examples/ums-1task/machine.tck"))
  //   val checker = LTLAutomaticVerifier(ltl.SystemSpec(tas, (F(Atomic("rel1")))))
  //   checker.setProcessDependencies(0, Set())
  //   checker.learnAssumptions(true)
  // }

  // test("ltl learn assumptions: sdn"){
  //     val tas = Array(File("examples/sdn/device.tck"), File("examples/sdn/switch.tck"), File("examples/sdn/controller.tck"), File("examples/sdn/supervisor.tck"), File("examples/sdn/observer.tck"))
  //     val ltlChecker = LTLAutomaticVerifier(ltl.SystemSpec(tas, (F(Atomic("change")))))
  //     ltlChecker.setAssumptionAlphabet(1, Set("change","send"))
  //     ltlChecker.setAssumptionAlphabet(2, Set("change","ack","send"))
  //     ltlChecker.learnAssumptions(true)
  // //   }
  // test("ltl learn assumptions: simple-sdn"){
  //     val tas = Array(File("examples/simple-sdn/device.tck"), File("examples/simple-sdn/switch.tck"), File("examples/simple-sdn/controller.tck"), File("examples/simple-sdn/supervisor.tck"), File("examples/simple-sdn/observer.tck"))
  //     // 15s, ArrayBuffer((G 1), (G 1), (G (F ack)), (G (F go)), (G ((F err) -> err)))
  //     // val ltlChecker = LTLAutomaticVerifier(ltl.SystemSpec(tas, LTL.fromString("G(ask -> F go)")))

  //     // 89s, ArrayBuffer((G 1), (G ((G (change -> (G change))) -> (G send))), (G (G ((F ack) & (F send)))), (G (G (F (go & (F ask))))), (G (G (!err))))
  //     // val ltlChecker = LTLAutomaticVerifier(ltl.SystemSpec(tas, LTL.fromString("G(change -> F ack)")))

  //     val ltlChecker = LTLAutomaticVerifier(ltl.SystemSpec(tas, LTL.fromString("G(F send)"))) // constraints unsatisfiable 150s
  //     ltlChecker.learnAssumptions(true)
  // }
  // test("manual simple-sdn"){
  //   val assumptions = Array(G(LTLTrue()), G(LTLTrue()), G(LTL.fromString("(G (G (((send U ack) -> ack) U ack)))")), G(LTL.fromString("(G (G ((!go) U (go & (X (!go))))))")), LTL.fromString("(G (!(F err)))"))
  //   val tas = Array(File("examples/simple-sdn/device.tck"), File("examples/simple-sdn/switch.tck"), File("examples/simple-sdn/controller.tck"), File("examples/simple-sdn/supervisor.tck"), File("examples/simple-sdn/observer.tck"))
  //   val ltlChecker = LTLAutomaticVerifier(ltl.SystemSpec(tas, (F(Atomic("change")))))
  //   ltlChecker.setAssumptionAlphabet(1, Set("change","send"))
  //   ltlChecker.setAssumptionAlphabet(2, Set("change","ack","send"))
  //   assumptions
  //     .zipWithIndex
  //     .foreach((f,i) => ltlChecker.setAssumption(i, f))
  //   ltlChecker.applyAG(true)
  // }
    // test("as"){
    //   val ta = TA.fromFile(File("examples/simple-sdn/a.tck"))
    //   val bta = ta.buchiIntersection(NLTS.fromLTL("((G F (go | ask)) & (G F (change | send)) & ~(G(ask -> F go)))", None),"acc")
    //   println(bta)
    // }
  test("DFA learn assumptions: full sdn"){
    val tas = Array(File("examples/sdn/device.tck"), File("examples/sdn/switch.tck"), File("examples/sdn/controller.tck"), File("examples/sdn/supervisor.tck"), File("examples/sdn/observer.tck"))
    val dfaChecker = DFAAutomaticVerifier(tas, Some(DLTS.fromErrorSymbol("err")), dfa.DFALearningAlgorithm.RPNI)
    dfaChecker.learnAssumptions(true)
  }
    
 }
 
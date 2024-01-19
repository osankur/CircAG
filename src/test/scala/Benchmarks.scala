// package fr.irisa.circag


// import net.automatalib.serialization.saf.SAFSerializationDFA 
// import net.automatalib.serialization.aut.AUTWriter 

// import java.util.HashMap
// import java.io.File
// import collection.JavaConverters._
// import collection.convert.ImplicitConversions._
// import collection.mutable.{Buffer}
// import com.microsoft.z3._

// import net.automatalib.serialization.aut.AUTWriter
// import dk.brics.automaton.Automaton
// import dk.brics.automaton.RegExp
// import net.automatalib.serialization.taf.writer.TAFWriter 

// import de.learnlib.algorithms.rpni.BlueFringeRPNIDFA
// import de.learnlib.api.oracle._
// import de.learnlib.api.oracle.MembershipOracle
// import net.automatalib.words._
// import de.learnlib.api.algorithm.LearningAlgorithm.DFALearner
// import de.learnlib.algorithms.lstar.dfa.ClassicLStarDFA;
// import de.learnlib.algorithms.lstar.dfa.ClassicLStarDFABuilder;
// import de.learnlib.api.oracle.MembershipOracle.DFAMembershipOracle;
// import de.learnlib.datastructure.observationtable.OTUtils;
// import de.learnlib.datastructure.observationtable.writer.ObservationTableASCIIWriter;
// import de.learnlib.filter.statistic.oracle.DFACounterOracle;
// import de.learnlib.oracle.equivalence.DFAWMethodEQOracle;
// import de.learnlib.oracle.membership.SimulatorOracle.DFASimulatorOracle;
// import de.learnlib.util.Experiment.DFAExperiment;
// import de.learnlib.util.statistics.SimpleProfiler;
// import net.automatalib.automata.fsa.DFA;
// import net.automatalib.automata.fsa.impl.FastDFA
// import net.automatalib.automata.fsa.impl.FastDFAState
// import net.automatalib.util.automata.fsa.DFAs 
// import net.automatalib.util.automata.fsa.NFAs 
// import net.automatalib.automata.fsa.impl.compact.CompactDFA;
// import net.automatalib.util.automata.builders.AutomatonBuilders;
// import net.automatalib.visualization.Visualization;
// import net.automatalib.words.Alphabet;
// import net.automatalib.commons.util.nid.MutableNumericID;
// import net.automatalib.words.impl.FastAlphabet;
// import net.automatalib.words.impl.Alphabets;
// import net.automatalib.brics.AbstractBricsAutomaton
// import net.automatalib.brics.BricsNFA
// import net.automatalib.visualization.Visualization
// import net.automatalib.automata.fsa.DFA;
// import net.automatalib.automata.fsa.impl.compact.CompactDFA;
// import net.automatalib.util.automata.builders.AutomatonBuilders;
// import net.automatalib.visualization.Visualization;
// import net.automatalib.words.Alphabet;
// import net.automatalib.words.impl.Alphabets;
// import de.learnlib.util.MQUtil;
// import de.learnlib.api.oracle.EquivalenceOracle
// import de.learnlib.api.query.DefaultQuery;
// import fr.irisa.circag.{DLTS, Trace}
// import fr.irisa.circag._
// import com.microsoft.z3.enumerations.Z3_lbool
// import fr.irisa.circag.ltl._
// import fr.irisa.circag.dfa._
// import fr.irisa.circag.ltl.LTL

// class DFAAutomatic extends munit.FunSuite {
//  test("DFA learn assumptions: simple sdn"){
//     val tas = Array(File("examples/simple-sdn/device.tck"), File("examples/simple-sdn/switch.tck"), File("examples/simple-sdn/controller.tck"), File("examples/simple-sdn/supervisor.tck"), File("examples/simple-sdn/observer.tck"))
//     val dfaChecker = DFAAutomaticVerifier(dfa.SystemSpec(tas, Some(DLTS.fromErrorSymbol("err"))))
//     dfaChecker.learnAssumptions(true)
//   }
//  test("DFA learn assumptions: full sdn"){
//     val tas = Array(File("examples/sdn/device.tck"), File("examples/sdn/switch.tck"), File("examples/sdn/controller.tck"), File("examples/sdn/supervisor.tck"), File("examples/sdn/observer.tck"))
//     val dfaChecker = DFAAutomaticVerifier(dfa.SystemSpec(tas, Some(DLTS.fromErrorSymbol("err"))))
//     dfaChecker.learnAssumptions(true)
//   }
//  test("DFA learn assumptions: ums-2"){
//     val tas = Array(File("examples/ums-2/user.tck"), File("examples/ums-2/scheduler.tck"), File("examples/ums-2/machine.tck"))
//     val checker = DFAAutomaticVerifier(dfa.SystemSpec(tas, Some(DLTS.fromErrorSymbol("err"))))
//     // val checker = LTLAutomaticVerifier(ltl.SystemSpec(tas, LTL.fromString("F(rel1)"))) // fails
//     checker.learnAssumptions(true)
//  }
//  test("DFA learn assumptions: ums-1"){
//     val tas = Array(File("examples/ums-1/user.tck"), File("examples/ums-1/scheduler.tck"), File("examples/ums-1/machine.tck"))
//     val checker = DFAAutomaticVerifier(dfa.SystemSpec(tas, Some(DLTS.fromErrorSymbol("err"))))
//     // val checker = LTLAutomaticVerifier(ltl.SystemSpec(tas, LTL.fromString("F(rel1)"))) // fails
//     checker.learnAssumptions(true)
//  }
// }

// class LTLAutomatic  extends munit.FunSuite {
//   // test("ltl learn assumptions: muo 2 processes"){
//   //   val tas = Array(File("examples/muo/user.tck"), File("examples/muo/machine.tck"))
//   //   val checker = LTLAutomaticVerifier(ltl.SystemSpec(tas, G(F(Atomic("cycle")))))
//   //   checker.setProcessInstantaneousDependencies(1, Set(0))
//   //   // this should take 15 attempts
//   //   val result2 = checker.learnAssumptions(proveGlobalProperty = true)
//   //   assert(result2 == ltl.LTLAGResult.Success)
//   // }
//   test("ltl learn assumptions: ltl-toy1 2 processes"){
//     val tas = Array(File("examples/ltl-toy1/a.tck"), File("examples/ltl-toy1/b.tck"))
//     val checker = LTLAutomaticVerifier(ltl.SystemSpec(tas, G(F(Atomic("a")))))
//     checker.setProcessInstantaneousDependencies(0, Set(1))
//     val result = checker.learnAssumptions(proveGlobalProperty = true)
//     assert(result == ltl.LTLAGResult.Success)
//   }
// }


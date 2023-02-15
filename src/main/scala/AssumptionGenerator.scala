package fr.irisa.circag

import java.util.HashMap

import de.learnlib.api.oracle.EquivalenceOracle
import de.learnlib.api.query.DefaultQuery;
import de.learnlib.api.oracle._
import de.learnlib.api.oracle.MembershipOracle

import net.automatalib.automata.fsa.impl.compact.CompactDFA;
import net.automatalib.util.automata.builders.AutomatonBuilders;
import net.automatalib.automata.fsa.DFA
import net.automatalib.util.automata.fsa.NFAs
import net.automatalib.automata.fsa.NFA
import net.automatalib.util.automata.fsa.DFAs
import net.automatalib.words.impl.Alphabets;
import net.automatalib.words._
import net.automatalib.util.automata.builders.AutomatonBuilders;
import net.automatalib.visualization.Visualization;
import net.automatalib.automata.fsa.impl.compact.CompactNFA;
import net.automatalib.serialization.aut.AUTSerializationProvider 
import net.automatalib.automata.fsa.NFA


// import de.uni_freiburg.informatik.ultimate.logic.Annotation;
// import de.uni_freiburg.informatik.ultimate.logic.Logics;
// import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
// import de.uni_freiburg.informatik.ultimate.logic.Script;
// import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
// import de.uni_freiburg.informatik.ultimate.logic.Sort;
// import de.uni_freiburg.informatik.ultimate.logic.Term;
// import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

import com.microsoft.z3._
trait AssumptionGenerator{
  def getAssumption(positiveSamples : List[String], negativeSamples : List[String]) : DFA[String, String]
}

abstract class LStarAssumptionGenerator extends AssumptionGenerator{
  
}
class SATAssumptionGenerator {
  def doSomething() : Unit =
    {

    }
}
abstract class IDFAAssumptionGenerator extends AssumptionGenerator
package fr.irisa.circag.ltl

import scala.util.boundary, boundary.break
import org.slf4j.Logger
import org.slf4j.LoggerFactory
import io.AnsiColor._

import collection.JavaConverters._
import collection.convert.ImplicitConversions._
import collection.mutable.Buffer
import collection.mutable.HashMap
import scala.sys.process._
import scala.io
import java.io.ByteArrayInputStream
import java.nio.file._
import java.io.{File, PrintWriter}
import net.automatalib.automata.fsa.MutableDFA
import net.automatalib.automata.fsa.DFA;
import net.automatalib.automata.fsa.impl.compact.CompactDFA;
import net.automatalib.automata.fsa.impl.FastDFA
import net.automatalib.automata.fsa.impl.FastDFAState
import net.automatalib.util.automata.fsa.DFAs
import net.automatalib.util.automata.fsa.NFAs
import net.automatalib.automata.fsa.impl.compact.CompactDFA;
import net.automatalib.util.automata.builders.AutomatonBuilders;
import net.automatalib.words.impl.Alphabets;

import com.microsoft.z3

import fr.irisa.circag.statistics
import fr.irisa.circag.configuration
import fr.irisa.circag._

class LTLAutomaticVerifier(_ltsFiles: Array[File], _property: LTL, ltlLearningAlgorithm : LTLLearningAlgorithm = LTLLearningAlgorithm.Samples2LTL)
  extends LTLVerifier(_ltsFiles, _property){
  private val ltlGenerator = LTLGenerator(proofSkeleton, ltlLearningAlgorithm)

  /**
    * @brief Prove or disprove the fixed assumptions and the global property by learning nonfixed assumptions
    * 
    * @param proveGlobalProperty whether the given global property is to be checked
    * @param fixedAssumptions list of process ids for which the assumptions are fixed; these will not be learned
    * @return
    */
  def learnAssumptions(proveGlobalProperty : Boolean = true, fixedAssumptions : List[Int] = List()): LTLAGResult = {
    var count = 0
    val fixedAssumptionsMap = HashMap[Int, LTL]()
    fixedAssumptions.foreach(i => 
      fixedAssumptionsMap.put(i, assumptions(i))      
    )
    var doneVerification = false
    var currentState = LTLAGResult.Success
    while (!doneVerification && count < 20) {
      count += 1
      ltlGenerator.generateAssumptions(fixedAssumptionsMap) match {
        case Some(newAss) => this.assumptions = newAss
        case None         => 
          println(s"${RED}Unsat${RESET}")
          throw LTLUnsatisfiableConstraints()
      }
      println(s"${MAGENTA}Assumptions at attempt #${count}: ${assumptions}${RESET}")
      currentState = this.applyAG(proveGlobalProperty) 
      currentState match {
        case LTLAGResult.Success => 
          println("Success")
          doneVerification = true
        case LTLAGResult.AssumptionViolation(processID, cex, query) => 
          println(s"AssumptionViolation ${processID} ${cex}")
          query match {
            case q : NonCircularPremiseQuery => 
              ltlGenerator.refineConstraintsByPremiseQuery(cex, q, 0)
            case q : CircularPremiseQuery => 
              val k0 = getPremiseViolationIndex(cex, q)
              ltlGenerator.refineConstraintsByPremiseQuery(cex, q, k0)
          }
          doneVerification = fixedAssumptions.contains(processID)
        case LTLAGResult.GlobalPropertyViolation(cex) => 
          println(s"Gobalproperty violation ${cex}")
          doneVerification = true
        case LTLAGResult.PremiseFail(processID, cex, query) => 
          println(s"PremiseFail ${processID} ${cex}")
          query match {
            case q : NonCircularPremiseQuery => 
              ltlGenerator.refineConstraintsByPremiseQuery(cex, q, 0)
            case q : CircularPremiseQuery => 
              val k0 = getPremiseViolationIndex(cex, q)
              ltlGenerator.refineConstraintsByPremiseQuery(cex, q, k0)
          }
          // ltlGenerator.refineConstraintsByPremiseQuery(cex, query)
        case LTLAGResult.GlobalPropertyProofFail(cex) => 
          println(s"Global Proof fail ${cex}")
          ltlGenerator.refineConstraintsByFinal(cex)
      }
    }
    currentState
  }

}

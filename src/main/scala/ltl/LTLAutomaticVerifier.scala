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

class LTLAutomaticVerifier(_system : SystemSpec, ltlLearningAlgorithm : LTLLearningAlgorithm = LTLLearningAlgorithm.Samples2LTL, constraintStrategy : ConstraintStrategy = ConstraintStrategy.Eager)
  extends LTLVerifier(_system){

  private val ltlGenerator = LTLGenerator.getGenerator(system, proofSkeleton, ltlLearningAlgorithm, constraintStrategy)

  /**
    * @brief Prove or disprove the fixed assumptions and the global property by learning nonfixed assumptions
    * 
    * @param proveGlobalProperty whether the given global property is to be checked
    * @param fixedAssumptions list of process ids for which the assumptions are fixed; these will not be learned
    * @return
    */
  def learnAssumptions(proveGlobalProperty : Boolean = true, fixedAssumptions : List[Int] = List()): LTLAGResult = {
    var count = 0
    val fixedAssumptionsMap = Map[Int, LTL]()
    fixedAssumptions.foreach(i => 
      fixedAssumptionsMap.put(i, assumptions(i))      
    )
    var doneVerification = false
    var currentState = LTLAGResult.Success
    while (!doneVerification && count < 50) {
      count += 1
      logger.debug(s"${BOLD}${MAGENTA}Attempt #${count}${RESET}")
      ltlGenerator.generateAssumptions(fixedAssumptionsMap) match {
        case Some(newAss) =>           
          this.assumptions = newAss
          val (pos, neg) = ltlGenerator.getSamples()
          for i <- 0 until nbProcesses do {
            logger.debug(s"Pos($i) = ${pos(i)}")
            logger.debug(s"Neg($i) = ${neg(i)}")
            logger.debug(s"Assumption($i) = ${assumptions(i)}")
          }          
        case None         => 
          logger.debug(s"${RED}${BOLD}Unsat${RESET}")
          throw LTLUnsatisfiableConstraints()
      }
      currentState = this.applyAG(proveGlobalProperty) 
      currentState match {
        case LTLAGResult.Success => 
          logger.debug(s"${GREEN}${BOLD}Success${RESET}")
          doneVerification = true
        case LTLAGResult.AssumptionViolation(processID, cex, query) => 
          logger.debug(s"${RED}AssumptionViolation ${processID} ${cex}${RESET}")
          query match {
            case q : NonCircularPremiseQuery => 
              ltlGenerator.refineByInductivePremiseCounterexample(cex, q, 0)
            case q : CircularPremiseQuery => 
              val k0 = getPremiseViolationIndex(cex, q)
              ltlGenerator.refineByInductivePremiseCounterexample(cex, q, k0)
          }
          doneVerification = fixedAssumptions.contains(processID)
        case LTLAGResult.GlobalPropertyViolation(cex) => 
          logger.debug(s"${RED}Gobalproperty violation ${cex}${RESET}")
          doneVerification = true
        case LTLAGResult.PremiseFail(processID, cex, query) => 
          logger.debug(s"${RED}PremiseFail ${processID} ${cex}${RESET}")
          query match {
            case q : NonCircularPremiseQuery => 
              ltlGenerator.refineByInductivePremiseCounterexample(cex, q, 0)
            case q : CircularPremiseQuery => 
              val k0 = getPremiseViolationIndex(cex, q)
              ltlGenerator.refineByInductivePremiseCounterexample(cex, q, k0)
          }
          logger.debug("Refined constraints")
        case LTLAGResult.GlobalPropertyProofFail(cex) => 
          println(s"Global Proof fail ${cex}")
          ltlGenerator.refineByFinalPremiseCounterexample(cex)
      }
    }
    val (pos, neg) = ltlGenerator.getSamples()
    for i <- 0 until nbProcesses do {
      logger.debug(s"Pos($i) = ${pos(i)}")
      logger.debug(s"Neg($i) = ${neg(i)}")
    }
    currentState
  }

}

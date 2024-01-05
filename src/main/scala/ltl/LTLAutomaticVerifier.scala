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
import fr.irisa.circag.dfa.AGResult

class LTLAutomaticVerifier(_system : SystemSpec, ltlLearningAlgorithm : LTLLearningAlgorithm = LTLLearningAlgorithm.Samples2LTL, constraintStrategy : ConstraintStrategy = ConstraintStrategy.Eager)
  extends LTLVerifier(_system){

  private var ltlGenerator = LTLGenerator.getGenerator(system, proofSkeleton, ltlLearningAlgorithm, constraintStrategy)

  override def setProcessDependencies(i: Int, deps: Set[Int]) : Unit =
    super.setProcessDependencies(i,deps)
    ltlGenerator = LTLGenerator.getGenerator(system, proofSkeleton, ltlLearningAlgorithm, constraintStrategy)

  override def setProcessInstantaneousDependencies(i: Int, deps: Set[Int]) : Unit =
    super.setProcessInstantaneousDependencies(i,deps)
    ltlGenerator = LTLGenerator.getGenerator(system, proofSkeleton, ltlLearningAlgorithm, constraintStrategy)

  override def setPropertyDependencies(deps: Set[Int]) =
    super.setPropertyDependencies(deps)
    ltlGenerator = LTLGenerator.getGenerator(system, proofSkeleton, ltlLearningAlgorithm, constraintStrategy)

  override def setAssumptionAlphabet(i: Int, alphabet: Alphabet) =
    super.setAssumptionAlphabet(i, alphabet)
    ltlGenerator = LTLGenerator.getGenerator(system, proofSkeleton, ltlLearningAlgorithm, constraintStrategy)

  override def setPropertyAlphabet(alphabet: Alphabet) =
    super.setPropertyAlphabet(alphabet)
    ltlGenerator = LTLGenerator.getGenerator(system, proofSkeleton, ltlLearningAlgorithm, constraintStrategy)


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
      val (pos,neg) = ltlGenerator.getSamples()
      val totalNbSamples = pos.map(_.size).fold(0)((x,y) => x + y) + neg.map(_.size).fold(0)((x,y) => x + y)
      logger.debug(s"${BOLD}${MAGENTA}Attempt #${count}${RESET} with total ${totalNbSamples} of samples")
      for i <- 0 until nbProcesses do {
        logger.debug(s"Previous assumption($i) = ${assumptions(i)}")
        logger.debug(s"\tNew PositiveSamples($i) = ${MAGENTA}${pos(i)}${RESET}")
        logger.debug(s"\tNew NegativeSamples($i) = ${MAGENTA}${neg(i)}${RESET}")
      }
      ltlGenerator.generateAssumptions(fixedAssumptionsMap) match {
        case Some(newAss) => 
          this.assumptions = newAss
        case None         => 
          logger.info(s"${RED}${BOLD}Constraints unsat: verification is inconclusive${RESET}")
          throw LTLUnsatisfiableConstraints()
      }
      currentState = this.applyAG(proveGlobalProperty) 
      currentState match {
        case LTLAGResult.Success => 
          logger.info(s"${GREEN}${BOLD}Success${RESET}")
          logger.info(s"Following assumptions were learned: ${assumptions}")
          doneVerification = true
        case LTLAGResult.GlobalPropertyViolation(cex) => 
          logger.info(s"${RED}Gobalproperty violation ${cex}${RESET}")
          doneVerification = true
        case LTLAGResult.PremiseFail(processID, cex, query) => 
          logger.debug(s"${RED}PremiseFail ${processID} ${cex}${RESET}")
          if fixedAssumptions.contains(processID) then {
            if checkCounterExample(cex) then {
              doneVerification = true
              logger.info(s"${RED}Fixed assumption $processID fails with ${cex}${RESET}")
            }
          } else {
            query match {
              case q : NonCircularPremiseQuery => 
                ltlGenerator.refineByInductivePremiseCounterexample(cex, q, 0)
              case q : CircularPremiseQuery => 
                val k0 = getPremiseViolationIndex(cex, q)
                ltlGenerator.refineByInductivePremiseCounterexample(cex, q, k0)
            }          
          }
        case LTLAGResult.GlobalPropertyProofFail(cex) => 
          try {
            ltlGenerator.refineByFinalPremiseCounterexample(cex)
          } catch {
            case LTLAGResult.GlobalPropertyViolation(lasso) => 
              logger.debug(s"${RED}Gobalproperty violation ${cex}${RESET}")
              doneVerification = true
            case e => 
              throw e
          }
      }
    }
    val (pos, neg) = ltlGenerator.getSamples()
    for i <- 0 until nbProcesses do {
      logger.debug(s"Positive samples for process $i: ${pos(i)}")
      logger.debug(s"Negative samples for process $i: ${neg(i)}")
    }
    currentState
  }

}

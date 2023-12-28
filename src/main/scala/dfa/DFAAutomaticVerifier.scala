package fr.irisa.circag.dfa

import org.slf4j.Logger
import org.slf4j.LoggerFactory

import io.AnsiColor._

import collection.JavaConverters._
import collection.convert.ImplicitConversions._
import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.ListBuffer
import scala.collection.mutable.Buffer
import scala.sys.process._
import scala.io
import scala.collection.mutable.StringBuilder
import scala.collection.mutable.HashMap

import java.io.File
import java.io.InputStream
import java.nio.file._
import java.io.PrintWriter
import java.io.ByteArrayInputStream
import fr.irisa.circag._
import fr.irisa.circag.DLTS
import fr.irisa.circag.Trace
import fr.irisa.circag.configuration
import fr.irisa.circag.statistics

/** Automatic assume-guarantee property prover which can check the inductive premises and the final premise
  * by automatically learning assumptions for processes.
  *
  * @param system
  *   system under study
  */
class DFAAutomaticVerifier(
    _system: SystemSpec,
    dfaLearnerAlgorithm: DFALearningAlgorithm,
    constraintStrategy : ConstraintStrategy
) extends DFAVerifier(_system) {

  private val cexHistory = Buffer.tabulate(nbProcesses)({_ => Set[Trace]()})
  private def resetCexHistory() : Unit = {
    for i <- 0 until cexHistory.size do {
      cexHistory(i) = Set[Trace]()
    }
  }

  def this(
      ltsFiles: Array[File],
      property: Option[DLTS],
      dfaLearnerAlgorithm: DFALearningAlgorithm = DFALearningAlgorithm.RPNI,
      constraintStrategy : ConstraintStrategy = ConstraintStrategy.Eager
  ) = {
    this(SystemSpec(ltsFiles, property), dfaLearnerAlgorithm, constraintStrategy)
  }

  protected val logger = LoggerFactory.getLogger("CircAG")
  protected var dfaGenerator =
    DFAGenerator.getGenerator(
      system,
      proofSkeleton,
      dfaLearnerAlgorithm,
      constraintStrategy
    )

  def setAssumptionAlphabet(processID: Int, alphabet: Alphabet): Unit = {
    if (
      !alphabet.containsAll(
        proofSkeleton
          .getPropertyAlphabet()
          .intersect(assumptions(processID).alphabet)
      )
    ) {
      throw Exception(
        "The assumption alphabet must contain the symbols that appear in the property alphabet"
      )
    }
    this.proofSkeleton.setAssumptionAlphabet(processID, alphabet);
  }

  def dumpAssumptions() : Unit = {
    for i <- 0 until nbProcesses do {
      val tck = TA.fromLTS(assumptions(i))
      val writer = PrintWriter(new File(s"_assumption${i}_${system.processes(i).systemName}"))
      writer.write(tck.toString())
      writer.close()
    }
  }

  /** Check the AG rule once for the current assumption alphabet and DFAs
   */
  override def applyAG(proveGlobalproperty: Boolean = true): AGResult = {

    // A proof for a process must not depend on itself
    logger.debug(s"applyAG with alphabets: ${assumptions.map(_.alphabet)}")
    try {
      for (ta, i) <- system.processes.zipWithIndex do {
        // DFAAssumeGuaranteeVerifier.checkInductivePremise(ta, proofSkeleton.processDependencies(i).map(assumptions(_)).toList, assumptions(i))
        this.checkInductivePremise(i) match {
          case None => ()
            // System.out.println(s"${GREEN}Premise ${i} passed${RESET}")
          case Some(cexTrace) =>
            latestCex = cexTrace
            System.out.println(
              s"${RED}Premise ${i} failed with cex: ${cexTrace}${RESET}"
            )
            if (this.cexHistory(i).contains(cexTrace)) then {
              for j <- proofSkeleton.processDependencies(i) do {
                System.out.println(
                  s"Dependency: Assumption ${assumptions(j).name} for ${system.processes(j).systemName}"
                )
                assumptions(j).visualize()
              }
              System.out.println(
                s"Assumption for this process ${system.processes(i).systemName}"
              )
              assumptions(i).visualize()
              throw Exception(s"Repeated CEX: ${cexTrace}")
            } else {
              this.cexHistory(i) = this.cexHistory(i) + cexTrace
            }
            val prefixInP = system.property match {
              case None => false
              case Some(propertyDLTS) =>
                propertyDLTS.dfa.accepts(
                  cexTrace
                    .dropRight(1)
                    .filter(proofSkeleton.getPropertyAlphabet().contains(_))
                )
            }
            val traceInP = system.property match {
              case None => false
              case Some(propertyDLTS) =>
                propertyDLTS.dfa.accepts(
                  cexTrace.filter(
                    proofSkeleton.getPropertyAlphabet().contains(_)
                  )
                )
            }
            val cexAccepted = checkCounterExample(cexTrace)
            if (!prefixInP && checkCounterExample(cexTrace.dropRight(1))) then {
              throw AGResult.GlobalPropertyViolation(cexTrace.dropRight(1))
            } else if (!traceInP && cexAccepted) then {
              throw AGResult.GlobalPropertyViolation(cexTrace)
            }
            // updateConstraints(i, cexTrace)
            dfaGenerator.refineByInductivePremiseCounterexample(i, cexTrace)
            if cexAccepted then {
              throw AGResult.AssumptionViolation(i, cexTrace)
            } else {
              throw AGResult.PremiseFail(i, cexTrace)
            }
        }
      }
      // If no property to check, then we are done
      if system.property == None || !proveGlobalproperty then
        throw AGResult.Success
      this.checkFinalPremise() match {
        case None =>          
          AGResult.Success
        case Some(cexTrace) =>
          latestCex = cexTrace
          // If all processes contain proj(cexTrace), then return false, otherwise continue
          dfaGenerator.refineByFinalPremiseCounterexample(cexTrace)
          throw AGResult.GlobalPropertyProofFail(cexTrace)
      }
    } catch {
      case ex: AGResult => ex
    }
  }

  /** Apply automatic AG; retrun None on succes, and a confirmed cex otherwise.
    *
    * @param proveGlobalProperty
    * @param fixedAssumptions
    * @return
    */
  def learnAssumptions(
      proveGlobalProperty: Boolean = true,
      fixedAssumptions: List[Int] = List()
  ): AGResult = {
    this.resetCexHistory()
    val fixedAssumptionsMap = HashMap[Int, DLTS]()
    fixedAssumptions.foreach(i => fixedAssumptionsMap.put(i, assumptions(i)))
    var doneVerification = false
    var currentState = AGResult.PremiseFail(0, List())
    while (!doneVerification) {
      var newAss = dfaGenerator.generateAssumptions(fixedAssumptionsMap)
      newAss match {
        case Some(newAss) => this.assumptions = newAss
        case None         => throw DFAUnsatisfiableConstraints()
      }
      currentState = this.applyAG(proveGlobalProperty)
      currentState match {
        case AGResult.Success => 
          logger.info(s"${GREEN}${BOLD}Property holds${RESET}")
          doneVerification = true
        case AGResult.AssumptionViolation(processID, cex) =>
          doneVerification = fixedAssumptions.contains(processID)
        case AGResult.GlobalPropertyViolation(cex) => 
          logger.info(s"${RED}${BOLD}Property fails with counterexample ${cex}${RESET}")
          doneVerification = true
        case AGResult.PremiseFail(processID, cex)  => ()
        case AGResult.GlobalPropertyProofFail(cex) => ()
      }
    }
    if configuration.get().dumpAssumptions then dumpAssumptions()
    {
      val sizes = assumptions.map(a => s"${a.name} -> ${a.dfa.size()}")
      logger.info(s"Size of the learned assumptions: ${sizes}")
    }
    currentState
  }
}

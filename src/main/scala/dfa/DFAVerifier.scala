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

import de.learnlib.util.MQUtil;
import de.learnlib.api.oracle.EquivalenceOracle
import de.learnlib.api.query.DefaultQuery;
import de.learnlib.api.oracle._
import de.learnlib.api.oracle.MembershipOracle
import de.learnlib.api.oracle.MembershipOracle.DFAMembershipOracle
import net.automatalib.automata.fsa.impl.compact.CompactDFA;
import net.automatalib.util.automata.builders.AutomatonBuilders;
import net.automatalib.automata.fsa.DFA
import net.automatalib.automata.fsa.impl.FastDFA
import net.automatalib.automata.fsa.impl.FastDFAState
import net.automatalib.util.automata.fsa.NFAs
import net.automatalib.util.automata.fsa.DFAs
import net.automatalib.words.impl.Alphabets;
import net.automatalib.words
import net.automatalib.util.automata.builders.AutomatonBuilders;
import net.automatalib.visualization.Visualization;
import net.automatalib.automata.fsa.impl.compact.CompactNFA;
import net.automatalib.automata.fsa.NFA
import net.automatalib.serialization.aut.AUTWriter

import fr.irisa.circag._
import fr.irisa.circag.DLTS
import fr.irisa.circag.Trace
import fr.irisa.circag.configuration
import fr.irisa.circag.statistics

import com.microsoft.z3
import fr.irisa.circag.isPrunedSafety

enum AGResult extends Exception:
  case Success
  case GlobalPropertyProofFail(cex : Trace)
  case GlobalPropertyViolation(cex : Trace)
  case PremiseFail(processID : Int, cex : Trace)
  case AssumptionViolation(processID : Int, cex : Trace)

class DFAUnsatisfiableConstraints extends Exception


class DFAVerifier(val ltsFiles: Array[File], var property : Option[DLTS] = None) {
  private val logger = LoggerFactory.getLogger("CircAG")

  val nbProcesses = ltsFiles.size
  
  val processes = ltsFiles.map(TA.fromFile(_)).toBuffer

  protected var propertyAlphabet = property match{
    case None =>Set[String]()
    case Some(p) => p.alphabet
  }
  // Set of symbols that appear in the property alphabet, or in at least two processes
  protected var interfaceAlphabet = Set[String]()
  /** Intersection of local alphabets with the interface alphabet: when all
   * assumptions use these alphabets, the AG procedure is complete.
   * i.e. alpha_F = alphaM_i /\ alphaP cup J_i
   */
  protected var completeAlphabets = Buffer.tabulate(nbProcesses)(_ => Set[String]())
  updateAlphabets()

  private def updateAlphabets() : Unit ={
    var propertyAlphabet = property match {
      case None => Set()
      case Some(dlts) => dlts.alphabet
    }    
    // Consider only symbols that appear at least in two processes (union of J_i's in CAV16)
    val symbolCount = HashMap[String, Int]()
    processes.foreach { p =>
      p.alphabet.foreach { sigma =>
        symbolCount.put(sigma, symbolCount.getOrElse(sigma, 0) + 1)
      }
    }
    symbolCount.filterInPlace((sigma, count) => count >= 2)
    interfaceAlphabet = propertyAlphabet | symbolCount.map({ (sigma, _) => sigma }).toSet

    completeAlphabets = processes
      .map({ pr =>
        interfaceAlphabet.intersect(pr.alphabet)
      })
      .toBuffer
  }
  def getPropertyAlphabet() : Set[String] = propertyAlphabet
  def getInterfaceAlphabet(): Set[String] = interfaceAlphabet
  def getCompleteAlphabet(processID : Int): Set[String] = completeAlphabets(processID)

  /** The assumption DLTS g_i for each process i.
    */
  protected var assumptions: Buffer[DLTS] = {
    (0 until ltsFiles.size)
      .map({ i =>
        val alph = interfaceAlphabet.intersect(processes(i).alphabet)
        val dfa = FastDFA(Alphabets.fromList(alph.toList))
        val state = dfa.addState(true)
        for sigma <- alph do {
          dfa.addTransition(state, sigma, state)
        }
        // Visualization.visualize(dfa, Alphabets.fromList(processes(i).alphabet.toList))

        DLTS(s"g_${i}", dfa, alph)
      })
      .toBuffer
  }

  val proofSkeleton = DFAProofSkeleton(
    processes.map(_.alphabet),
    propertyAlphabet,
    interfaceAlphabet
  )

  def getAssumption(processID: Int): DLTS = {
    assumptions(processID)
  }
  def setAssumption(i : Int, dlts : DLTS) : Unit = {
    if (!dlts.alphabet.containsAll(propertyAlphabet.intersect(processes(i).alphabet))){
      throw Exception(s"The assumption alphabet is ${dlts.alphabet} but it must contain the intersection of the process alphabet and the property alphabet")
    }
    assumptions(i) = dlts
    proofSkeleton.setAssumptionAlphabet(i, dlts.alphabet)
  }
  def setGlobalProperty(dlts : DLTS) : Unit = {
    property = Some(dlts)
    updateAlphabets()
    proofSkeleton.setPropertyAlphabet(propertyAlphabet)
    proofSkeleton.updatePropertyDependenciesByCone()
  }
  /** Checks processes(processID) |= A |> G
    *
    * where A is the set of assumptions on which processID depends (according to
    * proofSkeleton), and G is processID's assumption.
    *
    * @param processID
    *   id of the process
    * @pre
    *   guarantee.alphabet <= lts.alphabet (checked by assertion)
    * @pre
    *   All reachable states of the assumptions and ta are accepting (checked by
    *   assertion)
    * @pre
    *   assumptions do not contain the assumption for the process itself (not
    *   checked)
    * @return
    *   A counterexample to the premise: None if the premise holds; and
    *   Some(cexTrace) otherwise
    */
  def checkInductivePremise(processID: Int): Option[Trace] = {
    val guarantee = this.assumptions(processID)
    val localAssumptions =
      proofSkeleton.processDependencies(processID).map(this.assumptions(_))
    val ta = processes(processID)
    require(guarantee.alphabet.toSet.subsetOf(ta.alphabet))
    require(assumptions.forall({ dlts => dlts.dfa.isPrunedSafety }))
    statistics.Counters.incrementCounter("inductive-premise")
    logger.debug(
      s"Checking inductive premise for ${ta.systemName} whose assumption is over alphabet: ${guarantee.alphabet}"
    )
    var beginTime = System.nanoTime()
    // require(assumptions.forall({dlts => !dlts.dfa.getStates().forall(_.isAccepting())}))
    val guaranteeAlphabet = Alphabets.fromList(guarantee.alphabet.toList)
    val compG = DLTS(
      s"_comp_${guarantee.name}",
      DFAs.complement(
        guarantee.dfa,
        guaranteeAlphabet,
        FastDFA(guaranteeAlphabet)
      ),
      guarantee.alphabet
    )
    val liftedAssumptions =
      assumptions.map({ ass =>
        DLTS.liftAndStripNonAccepting(
          ass,
          ta.alphabet,
          Some(s"lifted_${ass.name}")
        )
      })
    val premiseProduct = TA.synchronousProduct(
      ta,
      compG :: liftedAssumptions.toList,
      Some("_accept_")
    )
    statistics.Timers.incrementTimer(
      "inductive-premise",
      System.nanoTime() - beginTime
    )
    premiseProduct.checkReachability(s"${compG.name}_accept_")
  }

  /** Check the final premise, that is, whether /\_{dtls in assumptions} dtls ->
    * property.
    *
    * @pre
    *   All states of the automata in lhs are accepting
    * @return
    *   None if the premise holds; and Some(cexTrace) otherwise
    */
  def checkFinalPremise(): Option[Trace] = {    
    statistics.Counters.incrementCounter("final-premise")
    property match {
      case None => None
      case Some(propertyDLTS) => 
      val lhs = proofSkeleton.propertyDependencies().map(assumptions(_)).toList
      // Check precondition
      for dlts <- lhs do {
        val dfa = dlts.dfa
        dfa
          .getStates()
          .foreach({ s =>
            for a <- dlts.alphabet do {
              dfa
                .getSuccessors(s, a)
                .foreach({ sn =>
                  assert(dfa.isAccepting(sn))
                })
            }
          })
      }
      val alph = Alphabets.fromList(propertyDLTS.alphabet.toList)
      val compG = DLTS(
        s"_comp_${propertyDLTS.name}",
        DFAs.complement(propertyDLTS.dfa, alph, FastDFA(alph)),
        propertyDLTS.alphabet
      )
      val premiseProduct = TA.synchronousProduct(
        TA.fromLTS[FastDFAState](compG, acceptingLabelSuffix = Some("_accept_")),
        lhs
      )
      // System.out.println(premiseProduct)
      premiseProduct.checkReachability(s"${compG.name}_accept_")
    }
  }

  /** Check whether all processes accept the given trace
    */
  def checkCounterExample(trace: Trace): Boolean = {
    var returnValue = true
    class Break extends Exception
    try {
      for (ta, i) <- processes.zipWithIndex do {
        ta.checkTraceMembership(trace, Some(assumptions(i).alphabet)) match {
          case None => // ta rejects
            throw Break()
          case _ => // ta accepts
            ()
        }
      }
    } catch {
      case _: Break =>
        returnValue = false
    }
    returnValue
  }

  /** Apply AG rule with given assumptions and proof skeleton: Checks inductive
    * premises for all processes, then checks the final premise if proveGlobalProperty is true.
    * @return
    */
  def applyAG(proveGlobalProperty : Boolean = true): AGResult = {
    // A proof for a process must not depend on itself
    logger.debug(s"applyAG with alphabets: ${assumptions.map(_.alphabet)}")
    try{
      for (ta, i) <- processes.zipWithIndex do {
        // DFAAssumeGuaranteeVerifier.checkInductivePremise(ta, proofSkeleton.processDependencies(i).map(assumptions(_)).toList, assumptions(i))
        this.checkInductivePremise(i) match {
          case None =>
            logger.info(s"${GREEN}Premise ${i} passed${RESET}")
          case Some(cexTrace) =>
            latestCex = cexTrace
            logger.info(
              s"${RED}Premise ${i} failed with cex: ${cexTrace}${RESET}"
            )
            if checkCounterExample(cexTrace) then {
              logger.info(s"\tCex to assumption ${i} confirmed: ${cexTrace}")
              throw AGResult.AssumptionViolation(i, cexTrace)
            } else 
              throw AGResult.PremiseFail(i, cexTrace)
        }
      }
      // DFAAssumeGuaranteeVerifier.checkFinalPremise(proofSkeleton.propertyDependencies.map(assumptions(_)).toList, propertyDLTS)
      if property == None || !proveGlobalProperty then 
        throw AGResult.Success
      this.checkFinalPremise() match {
        case None =>
          logger.info(s"${GREEN}Final premise succeeded${RESET}")
          AGResult.Success
        case Some(cexTrace) =>
          latestCex = cexTrace
          logger.info(
            s"${RED}Final premise failed with cex: ${cexTrace}${RESET}"
          )
          // If all processes contain proj(cexTrace), then return false, otherwise continue
          if checkCounterExample(cexTrace) then {
            logger.info(s"\tCex confirmed: ${cexTrace}")
            throw AGResult.GlobalPropertyViolation(cexTrace)
          } else {
            logger.info(s"\tCex *spurious*: ${cexTrace}")
            throw AGResult.GlobalPropertyProofFail(cexTrace)
          }
      }
    } catch {
      case ex : AGResult => ex
    }
  }
  // Latest cex encountered in any premise check. This is for debugging.
  protected var latestCex = List[String]()
}

class DFAAutomaticVerifier(
    _ltsFiles: Array[File],
    _property : Option[DLTS],
    assumptionGeneratorType: AssumptionGeneratorType =
      AssumptionGeneratorType.RPNI
) extends DFAVerifier(_ltsFiles, _property) {

  /** Current alphabet for assumptions: the alphabet of each assumption for ta
    * is ta.alphabet & assumptionAlphabet.
    */
  protected val logger = LoggerFactory.getLogger("CircAG")
  protected var dfaGenerator =
    DFAGenerator(proofSkeleton, assumptionGeneratorType)

  def setAssumptionAlphabet(processID : Int, alphabet : Alphabet) : Unit = {
    if (!alphabet.containsAll(propertyAlphabet.intersect(assumptions(processID).alphabet))){
      throw Exception("The assumption alphabet must contain the symbols that appear in the property alphabet")
    }
    this.proofSkeleton.setAssumptionAlphabet(processID, alphabet);
  }

  protected def updateConstraints(process: Int, cexTrace: Trace): Unit = {
    val prefixInP = property match{
      case None => false
      case Some(propertyDLTS) => 
        propertyDLTS.dfa.accepts(
          cexTrace.dropRight(1).filter(propertyAlphabet.contains(_))
        )
    }
    val traceInP = property match{
      case None => false
      case Some(propertyDLTS) => 
        propertyDLTS.dfa.accepts(cexTrace.filter(propertyAlphabet.contains(_)))
    }
    if (prefixInP && !traceInP) then {
      // System.out.println("Case 22")
      dfaGenerator.addConstraint(process, cexTrace, 22)
    } else if (cexTrace.size > 0 && !prefixInP && !traceInP) then {
      // System.out.println("Case 29")
      dfaGenerator.addConstraint(process, cexTrace, 29)
    } else {
      // System.out.println("Case 34")
      dfaGenerator.addConstraint(process, cexTrace, 34)
    }
  }


  /** Check the AG rule once for the current assumption alphabet and DFAs
    */
  override def applyAG(proveGlobalproperty : Boolean = true): AGResult = {
    // val concreteVal = processes.zipWithIndex.map({
    //   (p,i) =>
    //       val valFori =
    //         this.dfaGenerator.samples(i).map({
    //         (trace,v) =>
    //           TCheckerAssumeGuaranteeOracles.checkTraceMembership(p,trace, Some(p.alphabet)) match {
    //             case None => dfaGenerator.z3ctx.mkNot(v)
    //           case Some(_) => v
    //           }
    //         })
    //       dfaGenerator.z3ctx.mkAnd(valFori.toSeq : _*)
    // })
    // System.out.println("Displaying concrete val:")
    // for (p,exp) <- processes.zip(concreteVal) do {
    //   System.out.println(s"${p.systemName}: ${exp}")
    // }
    // dfaGenerator.checkValuation(dfaGenerator.z3ctx.mkAnd(concreteVal.toSeq : _*))

    // A proof for a process must not depend on itself
    logger.debug(s"applyAG with alphabets: ${assumptions.map(_.alphabet)}")
    try {
      for (ta, i) <- processes.zipWithIndex do {
        // DFAAssumeGuaranteeVerifier.checkInductivePremise(ta, proofSkeleton.processDependencies(i).map(assumptions(_)).toList, assumptions(i))
        this.checkInductivePremise(i) match {
          case None =>
            System.out.println(s"${GREEN}Premise ${i} passed${RESET}")
          case Some(cexTrace) =>
            latestCex = cexTrace
            System.out.println(
              s"${RED}Premise ${i} failed with cex: ${cexTrace}${RESET}"
            )
            if (configuration.cex(i).contains(cexTrace)) then {
              // for j <- proofSkeleton.processDependencies(i) do {
              //   System.out.println(
              //     s"Dependency: Assumption ${assumptions(j).name} for ${processes(j).systemName}"
              //   )
              //   assumptions(j).visualize()
              // }
              // System.out.println(
              //   s"Assumption for this process ${processes(i).systemName}"
              // )
              // assumptions(i).visualize()
              throw Exception(s"Repeated CEX: ${cexTrace}")
            } else {
              configuration.cex(i) = configuration.cex(i) + cexTrace
            }
            val prefixInP = property match{
              case None => false
              case Some(propertyDLTS) => 
                propertyDLTS.dfa.accepts(
                  cexTrace.dropRight(1).filter(propertyAlphabet.contains(_))
                )
            }
            val traceInP = property match{
              case None => false
              case Some(propertyDLTS) => 
                propertyDLTS.dfa.accepts(cexTrace.filter(propertyAlphabet.contains(_)))
            }
            val cexAccepted = checkCounterExample(cexTrace)
            if (!prefixInP && checkCounterExample(cexTrace.dropRight(1))) then {
              throw AGResult.GlobalPropertyViolation(cexTrace.dropRight(1))
            } else if (!traceInP && cexAccepted) then {
              throw AGResult.GlobalPropertyViolation(cexTrace)
            }
            updateConstraints(i, cexTrace)
            if cexAccepted then {
              throw AGResult.AssumptionViolation(i, cexTrace)
            } else {
              throw AGResult.PremiseFail(i, cexTrace)
            }
        }
      }
      // If no property to check, then we are done
      if property == None || !proveGlobalproperty then 
        throw AGResult.Success
      this.checkFinalPremise() match {
        case None =>
          System.out.println(s"${GREEN}Final premise succeeded${RESET}")
          AGResult.Success
        case Some(cexTrace) =>
          latestCex = cexTrace
          System.out.println(
            s"${RED}Final premise failed with cex: ${cexTrace}${RESET}"
          )
          // If all processes contain proj(cexTrace), then return false, otherwise continue
          if checkCounterExample(cexTrace) then {
            if configuration.get().verbose then
              System.out.println(s"\tCex confirmed: ${cexTrace}")
            throw AGResult.GlobalPropertyViolation(cexTrace)
          } else {
            dfaGenerator.addFinalPremiseConstraint(cexTrace)
            throw AGResult.GlobalPropertyProofFail(cexTrace)
          }
      }
    } catch {
      case ex : AGResult => ex
    }
  }

  /**
    * Apply automatic AG; retrun None on succes, and a confirmed cex otherwise.
    *
    * @param proveGlobalProperty
    * @param fixedAssumptions
    * @return
    */
  def learnAssumptions(proveGlobalProperty : Boolean = true, fixedAssumptions : List[Int] = List()): AGResult = {
    configuration.resetCEX()
    val fixedAssumptionsMap = HashMap[Int, DLTS]()
    fixedAssumptions.foreach(i => 
      fixedAssumptionsMap.put(i, assumptions(i))      
    )
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
        case AGResult.Success => doneVerification = true
        case AGResult.AssumptionViolation(processID, cex) => doneVerification = fixedAssumptions.contains(processID)
        case AGResult.GlobalPropertyViolation(cex) => doneVerification = true
        case AGResult.PremiseFail(processID, cex) => ()
        case AGResult.GlobalPropertyProofFail(cex) => ()
      }
    }
    currentState
  }

}


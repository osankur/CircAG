package fr.irisa.circag.tchecker.dfa

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
import net.automatalib.words._
import net.automatalib.util.automata.builders.AutomatonBuilders;
import net.automatalib.visualization.Visualization;
import net.automatalib.automata.fsa.impl.compact.CompactNFA;
import net.automatalib.automata.fsa.NFA
import net.automatalib.serialization.aut.AUTWriter 

import fr.irisa.circag.tchecker._
import fr.irisa.circag.DLTS
import fr.irisa.circag.Trace
import fr.irisa.circag.configuration
import fr.irisa.circag.statistics

import com.microsoft.z3
import fr.irisa.circag.isPrunedSafety

object DFAAssumeGuaranteeVerifier {
  private val logger = LoggerFactory.getLogger("CircAG")
  /**
    * ta |= lhs |> guarantee
    *
    * @param lts
    * @param assumptions List of complete DFAs
    * @param guarantee
    * @pre guarantee.alphabet <= lts.alphabet (checked by assertion)
    * @pre All reachable states of the assumptions and ta are accepting (checked by assertion)
    * @pre assumptions do not contain the assumption for the process itself (not checked)
    * @return A counterexample to the premise: None if the premise holds; and Some(cexTrace) otherwise
    */
  def checkInductivePremise(ta : TA, assumptions : List[DLTS], guarantee : DLTS) : Option[Trace] =
    { 
      require(guarantee.alphabet.toSet.subsetOf(ta.alphabet))
      require(assumptions.forall({dlts => dlts.dfa.isPrunedSafety}))
      statistics.Counters.incrementCounter("inductive-premise")
      logger.debug(s"Checking inductive premise for ${ta.systemName} whose assumption is over alphabet: ${guarantee.alphabet}")
      var beginTime = System.nanoTime()
      // require(assumptions.forall({dlts => !dlts.dfa.getStates().forall(_.isAccepting())}))
      val guaranteeAlphabet = Alphabets.fromList(guarantee.alphabet.toList)
      val compG = DLTS(
        s"_comp_${guarantee.name}", 
        DFAs.complement(guarantee.dfa, guaranteeAlphabet, FastDFA(guaranteeAlphabet)),
        guarantee.alphabet)
      val liftedAssumptions = 
        assumptions.map({ass => DLTS.liftAndStripNonAccepting(ass, ta.alphabet, Some(s"lifted_${ass.name}"))})
      // for (ass, liftedAss) <- assumptions.zip(liftedAssumptions) do {
      //   System.out.println(s"Displaying assumption ${ass.name} ")
      //   AUTWriter.writeAutomaton(ass.dfa, Alphabets.fromList(ass.alphabet.toList), System.out)
      //   System.out.println(s"Displaying lifted assumption ${ass.name} ")
      //   AUTWriter.writeAutomaton(liftedAss.dfa, Alphabets.fromList(liftedAss.alphabet.toList), System.out)
      // }
      
      val premiseProduct = TA.synchronousProduct(ta, compG::liftedAssumptions, Some("_accept_"))
      statistics.Timers.incrementTimer("inductive-premise", System.nanoTime() - beginTime)
      checkReachability(premiseProduct, s"${compG.name}_accept_")
    }

  /**
    * Check the final premise, that is, whether /\_{dtls in lhs} dtls implies property.
    *
    * @param lhs
    * @param property
    * @pre All states of the automata in lhs are accepting
    * @return None if the premise holds; and Some(cexTrace) otherwise
    */
  def checkFinalPremise(lhs : List[DLTS], property : DLTS) : Option[Trace] = {
      statistics.Counters.incrementCounter("final-premise")

      // Check precondition
      for dlts <- lhs do {
        val dfa = dlts.dfa
        dfa.getStates().foreach({s =>
          for a <- dlts.alphabet do {
            dfa.getSuccessors(s,a).foreach({
              sn =>
                assert(dfa.isAccepting(sn))
              })
          }
        })
      }
      val alph = Alphabets.fromList(property.alphabet.toList)
      val compG = DLTS(s"_comp_${property.name}", DFAs.complement(property.dfa, alph, FastDFA(alph)), property.alphabet)
      val premiseProduct = TA.synchronousProduct(TA.fromLTS(compG, acceptingLabelSuffix=Some("_accept_")), lhs)
      // System.out.println(premiseProduct)
      checkReachability(premiseProduct, s"${compG.name}_accept_")
  }
  /**
    * Attempt to find a trace in ta that synchronizes with word; the returned trace has alphabet word's alphabet | ta's alphabet.
    * 
    * @param ta
    * @param word
    * @param projectionAlphabet
    * @return
    */
  def extendTrace(ta : TA, word : Trace, projectionAlphabet : Option[Set[String]]) : Option[Trace] ={
    val wordDLTS = DLTS.fromTrace(word)
    val productTA = TA.synchronousProduct(ta, List(wordDLTS), acceptingLabelSuffix = Some("_accept_"))
    checkReachability(productTA, s"${wordDLTS.name}_accept_") 
  }

  /**
    * 
    * @param ta
    * @param word
    * @param projectionAlphabet
    * @return
    */
  def attemptToExtendTraceToAllProcesses(tas : Array[TA], word : Trace, projectionAlphabet : Option[Set[String]]) : Trace = {
    var currentTrace = word
    for ta <- tas do {
      val wordDLTS = DLTS.fromTrace(currentTrace)
      val productTA = TA.synchronousProduct(ta, List(wordDLTS), acceptingLabelSuffix = Some("_accept_"))
      checkReachability(productTA, s"${wordDLTS.name}_accept_") match {
        case None => ()
        case Some(newTrace) => currentTrace = newTrace
      }
    }
    currentTrace
  }

  /**
    * Check whether trace|_alph is accepted by ta|_alph where alph is syncAlphabet (default is trace.toSet)
    *
    * @param ta a process 
    * @param trace a trace
    * @param syncAlphabet alphabet on which synchronous product is to be defined
    * @return None if no such execution exists, and Some(trace) otherwise.
    */
  def checkTraceMembership(ta : TA, trace : Trace, syncAlphabet : Option[Set[String]] = None) : Option[Trace] = {  
    statistics.Counters.incrementCounter("trace-membership")
    val traceAlphabet = syncAlphabet.getOrElse(trace.toSet)
    val projTrace = trace.filter(traceAlphabet.contains(_))
    val traceProcess = DLTS.fromTrace(projTrace, Some(traceAlphabet))
    val productTA = TA.synchronousProduct(ta, List(traceProcess), Some("_accept_"))
    val result = this.checkReachability(productTA, s"${traceProcess.name}_accept_")
    result
  }

  /**
   * Check the reachability of a state labeled by label. Return such a trace if any.
   * 
   * @param ta
   * @param label
   */
  def checkReachability(ta : TA, label : String) : Option[Trace] = {
    val beginTime = System.nanoTime()    
    statistics.Counters.incrementCounter("model-checking")
    val modelFile =
      Files.createTempFile(configuration.get().getTmpDirPath(), "circag-query", ".ta").toFile()
    val pw = PrintWriter(modelFile)
    pw.write(ta.toString())
    pw.close()

    val certFile =
      Files.createTempFile(configuration.get().getTmpDirPath(), "circag-cert", ".cert").toFile()
    val cmd = "tck-reach -a reach %s -l %s -C symbolic -o %s"
            .format(modelFile.toString, label, certFile.toString)

    logger.debug(cmd)

    val output = cmd.!!
    val cex = scala.io.Source.fromFile(certFile).getLines().toList

    if (!configuration.globalConfiguration.keepTmpFiles){
      modelFile.delete()
      certFile.delete()
    }    
    statistics.Timers.incrementTimer("tchecker", System.nanoTime() - beginTime)
    if (output.contains("REACHABLE false")) then {
      None
    } else if (output.contains("REACHABLE true")) then {
      Some(TA.getTraceFromCounterExampleOutput(cex, ta.alphabet))
    } else {
      throw FailedTAModelChecking(output)
    }
  }
}

abstract class AGIntermediateResult extends Exception
class AGSuccess extends AGIntermediateResult {
  override def equals(x: Any): Boolean = {
    x match {
      case _ : AGSuccess => true
      case _ => false
    }
  }
}
class AGContinue extends AGIntermediateResult {
  override def equals(x: Any): Boolean = {
    x match {
      case _ : AGContinue => true
      case _ => false
    }
  }
}
case class AGFalse(cex : Trace) extends AGIntermediateResult

/**
  * AG Proof skeleton specifies the dependencies for each premise of the N-way AG rule,
  * and the alphabets to be used for the assumption DFA of each TA.
  * 
  * @param processDependencies the set of process indices on which the proof of process(i) must depend.
  * @param propertyDependencies the set of process indices on which the proof of the final premise must depend.
  * @param assumptionAlphabets alphabets of the assumption DFAs for each process
  */
class AGProofSkeleton(val nbProcesses : Int) {
  var processDependencies = Buffer[Set[Int]]()
  var propertyDependencies = Set[Int]()
  var assumptionAlphabets = Buffer[Set[String]]()

  def this(processAlphabets : Buffer[Set[String]], propertyAlphabet : Set[String], newAssumptionAlphabet : Set[String]) = {
    this(processAlphabets.size)
    update(processAlphabets, propertyAlphabet, newAssumptionAlphabet)
  }
  /**
    * Update the fields from the given assumption alphabet
    *
    * @param processAlphabets alphabets of the TAs
    * @param propertyAlphabet alphabet of the property
    * @param newAssumptionAlphabet the common assumption alphabet
    */
  def update(processAlphabets : Buffer[Set[String]], propertyAlphabet : Set[String], newAssumptionAlphabet : Set[String]) = {
    val nbProcesses = processAlphabets.size
    processDependencies = Buffer.tabulate(nbProcesses)({_ => Set[Int]()})
    // Compute simplified sets of assumptions for the new alphabet
    // adj(i)(j) iff (i = j) or (i and j have a common symbol) or (i has a common symbol with k such that adj(k)(j))
    // Index nbProcesses represents the property.
    var adj = Buffer.tabulate(nbProcesses+1)({_ => Buffer.fill(nbProcesses+1)(false)})
    for i <- 0 until nbProcesses do {
      adj(i)(i) = true
      for j <- 0 until i do {
        adj(i)(j) = !processAlphabets(i).intersect(processAlphabets(j)).isEmpty
        adj(j)(i) = adj(i)(j)
      }
    }
    adj(nbProcesses)(nbProcesses) = true
    for j <- 0 until nbProcesses do {
        adj(nbProcesses)(j) = !propertyAlphabet.intersect(processAlphabets(j)).isEmpty
        adj(j)(nbProcesses) = adj(nbProcesses)(j)
    }
    for k <- 0 until nbProcesses+1 do {
      for i <- 0 until nbProcesses+1 do {
        for j <- 0 until nbProcesses+1 do {
          if(adj(i)(k) && adj(k)(j)) then {
            adj(i)(j) = true
          }
        }
      }
    }
    for i <- 0 until nbProcesses do {
      processDependencies(i) = adj(i).zipWithIndex.filter({(b,i) => b}).map(_._2).toSet.diff(Set[Int](i, nbProcesses))
    }
    propertyDependencies = adj(nbProcesses).zipWithIndex.filter({(b,i) => b}).map(_._2).toSet - nbProcesses
    assumptionAlphabets = processAlphabets.map(_.intersect(newAssumptionAlphabet))
    if configuration.get().verbose then {
      System.out.println(s"Ass alphabets: $assumptionAlphabets")
      System.out.println(s"Prop dependencies: $propertyDependencies")
      System.out.println(s"Process deps: $processDependencies")
    }
  }
  
}

class DFAAssumeGuaranteeVerifier(ltsFiles : Array[File], err : String, assumptionGeneratorType : AssumptionGeneratorType = AssumptionGeneratorType.RPNI, useAlphabetRefinement : Boolean = false) {
  private val logger = LoggerFactory.getLogger("CircAG")

  val nbProcesses = ltsFiles.size
  val propertyAlphabet = Set[String](err)
  val processes = ltsFiles.map(TA.fromFile(_)).toBuffer

  val propertyDLTS = {
    val errDFA = {
      val alph= Alphabets.fromList(propertyAlphabet.toList)
      AutomatonBuilders
        .forDFA(FastDFA(alph))
        .withInitial("q0")
        .from("q0")
        .on(err)
        .to("q1")
        .withAccepting("q0")
        .create();
    }
    DLTS("property", errDFA, propertyAlphabet)
  }

  // Set of symbols that appear in the property alphabet, or in at least two processes
  val interfaceAlphabet =
    // Consider only symbols that appear at least in two processes (union of J_i's in CAV16)
    val symbolCount = HashMap[String, Int]()
    processes.foreach{p => p.alphabet.foreach{
      sigma => symbolCount.put(sigma,symbolCount.getOrElse(sigma,0)+1)
    }}
    symbolCount.filterInPlace((sigma,count) => count >= 2)
    propertyAlphabet | symbolCount.map({(sigma,_) => sigma}).toSet

  // Intersection of local alphabets with the interface alphabet: when all 
  // assumptions use these alphabets, the AG procedure is complete.
  // i.e. alpha_F = alphaM_i /\ alphaP cup J_i
  val completeAlphabets = processes.map({ 
    pr => interfaceAlphabet.intersect(pr.alphabet)
  }).toBuffer

  /**
    * Current alphabet for assumptions: the alphabet of each assumption for ta is ta.alphabet & assumptionAlphabet.
    */
  private var assumptionAlphabet = 
    if useAlphabetRefinement then {
      propertyAlphabet
    } else {
      interfaceAlphabet
    }

  /**
    * The assumption DLTS g_i for each process i.
    */
  var assumptions : Buffer[DLTS] = {
    (0 until ltsFiles.size)
    .map(
      { i =>
        val alph = assumptionAlphabet.intersect(processes(i).alphabet)
        val dfa = FastDFA(Alphabets.fromList(alph.toList))
        val state = dfa.addState(true)
        for sigma <- alph do {
          dfa.addTransition(state, sigma, state)
        }
        // Visualization.visualize(dfa, Alphabets.fromList(processes(i).alphabet.toList))

        DLTS(s"g_${i}", dfa, alph)
      }).toBuffer
  }


  val proofSkeleton = AGProofSkeleton(processes.map(_.alphabet), propertyAlphabet, assumptionAlphabet)
  private var dfaGenerator = DFAGenerator(proofSkeleton, assumptionGeneratorType)

  // Latest cex encountered in any premise check
  private var latestCex = List[String]()

  /**
    * Updates assumptionAlphabet, and consequently processDependencies, propertyDependencies, and resets constraint manager.
    *
    * @param newAlphabet
    */
  private def addSymbolToAssumptionAlphabet(newSymbols : Set[String]) : Unit = {
    assumptionAlphabet |= newSymbols
    proofSkeleton.update(processes.map(_.alphabet), propertyAlphabet, assumptionAlphabet)
    // Create a new constraint manager initialized with the incremental traces from the previous instance
    dfaGenerator = DFAGenerator(proofSkeleton, assumptionGeneratorType, dfaGenerator.incrementalTraces)
    configuration.resetCEX()
  }

  def updateConstraints(process : Int, cexTrace : Trace) : Unit = {
    val prefixInP = propertyDLTS.dfa.accepts(cexTrace.dropRight(1).filter(propertyAlphabet.contains(_)))
    val traceInP = propertyDLTS.dfa.accepts(cexTrace.filter(propertyAlphabet.contains(_)))
    if (prefixInP && !traceInP) then {
      // System.out.println("Case 22")
      dfaGenerator.addConstraint(process, cexTrace, 22)
    } else 
    if (cexTrace.size > 0 && !prefixInP && !traceInP) then {
      // System.out.println("Case 29")
      dfaGenerator.addConstraint(process, cexTrace, 29)
    } else {
      // System.out.println("Case 34")
      dfaGenerator.addConstraint(process, cexTrace, 34)
    }
  }

  /**
   * Check whether all processes accept the given trace
   */
  def checkCounterExample(trace : Trace) : Boolean = {
    var returnValue = true
    try {
      for (ta,i) <- processes.zipWithIndex do {
        DFAAssumeGuaranteeVerifier.checkTraceMembership(ta, trace, Some(assumptions(i).alphabet))
        match {
          case None => // ta rejects
            throw AGContinue()
          case _ => // ta accepts
            ()
        }
      }
    } catch {
      case _ : AGContinue => 
        returnValue = false
    }
    returnValue
  }

  /**
   * Check the AG rule once for the current assumption alphabet and DFAs
   */
  def applyAG() : AGIntermediateResult = {
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
    require(proofSkeleton.assumptionAlphabets.zipWithIndex.forall({(ass,i) => !ass.contains(i)}))
    logger.debug(s"applyAG with alphabets: ${assumptions.map(_.alphabet)}")
    try{
      for (ta,i) <- processes.zipWithIndex do {
        DFAAssumeGuaranteeVerifier.checkInductivePremise(ta, proofSkeleton.processDependencies(i).map(assumptions(_)).toList, assumptions(i))
        match {
          case None =>
            System.out.println(s"${GREEN}Premise ${i} passed${RESET}")
          case Some(cexTrace) => 
            latestCex = cexTrace
            System.out.println(s"${RED}Premise ${i} failed with cex: ${cexTrace}${RESET}")
            if (configuration.cex(i).contains(cexTrace)) then {
              for j <- proofSkeleton.processDependencies(i) do {
                System.out.println(s"Dependency: Assumption ${assumptions(j).name} for ${processes(j).systemName}")
                assumptions(j).visualize()
              }
              System.out.println(s"Assumption for this process ${processes(i).systemName}")
              assumptions(i).visualize()
              throw Exception("Repeated CEX")
            } else {
              configuration.cex(i) = configuration.cex(i) + cexTrace
            }
            val prefixInP = propertyDLTS.dfa.accepts(cexTrace.dropRight(1).filter(propertyAlphabet.contains(_)))
            val traceInP = propertyDLTS.dfa.accepts(cexTrace.filter(propertyAlphabet.contains(_)))
            if (!prefixInP && checkCounterExample(cexTrace.dropRight(1))) then {
              throw AGFalse(cexTrace.dropRight(1))
            } else if (!traceInP && checkCounterExample(cexTrace)) then {
              throw AGFalse(cexTrace)
            }
            updateConstraints(i, cexTrace)
            throw AGContinue()
        }
      }
      DFAAssumeGuaranteeVerifier.checkFinalPremise(proofSkeleton.propertyDependencies.map(assumptions(_)).toList, propertyDLTS)
      match {
        case None => 
          System.out.println(s"${GREEN}Final premise succeeded${RESET}")
          AGSuccess()
        case Some(cexTrace) =>
          latestCex = cexTrace
          System.out.println(s"${RED}Final premise failed with cex: ${cexTrace}${RESET}")
          // If all processes contain proj(cexTrace), then return false, otherwise continue
          if checkCounterExample(cexTrace) then {
            if configuration.get().verbose then
              System.out.println(s"\tCex confirmed: ${cexTrace}")
            throw AGFalse(cexTrace)
          } else {
            dfaGenerator.addFinalPremiseConstraint(cexTrace)
            throw AGContinue()
          }
      }
    } catch {
      case ex : AGContinue => 
        ex
      case ex : AGFalse => ex
    }
  }

  private def refineWithArbitrarySymbol() : Unit = {
    val newSymbols = interfaceAlphabet.diff(this.assumptionAlphabet)
    assert(!newSymbols.isEmpty)
    // if configuration.get().verbose then {
      System.out.println(s"${YELLOW}Extending alphabet by arbitrarily chosen symbol: ${newSymbols.head}${RESET}")
    // }
    this.addSymbolToAssumptionAlphabet(Set(newSymbols.head))
  }

  private def alphabetRefine(cexTrace : Trace) : AGIntermediateResult = {
    val currentAlphabets = assumptions.map(_.alphabet)
    if ( this.completeAlphabets == currentAlphabets ) then {
      // All alphabets are complete; we can conclude
      AGFalse(cexTrace)
    } else {
      // MATCH: Check if each pair of traces match when projected to their common alphabet
      def findMismatch(processTraces: Buffer[List[String]]) : Option[(Int,Int)] = {
        var result : Option[(Int,Int)] = None
        for i <- 0 until this.processes.size do {
          for j <- 0 until i do {
            val commonAlphabet = processes(i).alphabet.intersect(processes(j).alphabet)
            if (processTraces(i).filter(commonAlphabet) != processTraces(j).filter(commonAlphabet)) then {
              result = Some((i,j))
            }
          }
        }
        result
      }
      def findNewSymbol(cex : List[String]) : AGIntermediateResult = {
        // Extend the trace to the alphabet of each TA separately (projected to the TA's external alphabet)
        // This cannot fail when cex == cexTrace, but can afterwards
        try {
          val processTraces = processes.zipWithIndex.map{
            (p,i) => DFAAssumeGuaranteeVerifier.checkTraceMembership(p, cex) match {
              case Some(processTrace) => 
                val interfaceTrace = processTrace.filter(interfaceAlphabet.contains(_))
                if configuration.get().verbose then {
                  System.out.println(s"Concretized trace for process ${p.systemName}: ${processTrace}")
                  System.out.println(s"\tProjected to completeAlphabet: ${interfaceTrace}")
                }
                interfaceTrace
              case None if cex == cexTrace => throw Exception(s"Trace $cex fails the final premise but cannot be reproduced here")
              case _ => 
                refineWithArbitrarySymbol()
                throw AGContinue()
            }
          }
          findMismatch(processTraces) match {          
            case None => 
              // All processes agree on these traces: check also if cex is rejected by the property
              if (!propertyDLTS.dfa.accepts(cex.filter(propertyDLTS.alphabet.contains(_)))) then 
                AGFalse(cex)
              else {
                // If not, then we cannot conclude: so we add an arbitrary new symbol from the traces or from interface alphabet
                // Add some random symbol
                val newTraceSymbols = processTraces.map(_.toSet).fold(Set[String]())({(a,b) => a | b}).diff(assumptionAlphabet)
                if (!newTraceSymbols.isEmpty) then {
                  this.addSymbolToAssumptionAlphabet(Set(newTraceSymbols.head))
                } else {
                  refineWithArbitrarySymbol()
                }
                AGContinue()
              }
            case Some((i,j)) =>
              // Otherwise choose a symbol that appears in a process trace but not in the current alphabet, and iterate
              val traceSymbols = processTraces.map(_.toSet).fold(Set[String]())({(a,b) => a | b})
              val newSymbols = traceSymbols.diff(this.assumptionAlphabet)
              if (!newSymbols.isEmpty) then {
                val newSymbol = newSymbols.head
                // if (configuration.get().verbose)
                  System.out.println(s"${YELLOW}Adding new symbol to assumption alphabet: ${newSymbol}${RESET}")

                this.addSymbolToAssumptionAlphabet(Set(newSymbol))
                AGContinue()
              } else if (processTraces(i).size > cex.size || processTraces(j).size > cex.size ) then {
                // System.out.println(s"The following traces mismatch and one of them is longer than current cex: ${processTraces(i)} and ${processTraces(j)}")
                val k = if processTraces(i).size > cex.size then i else j
                findNewSymbol(processTraces(k))
              } else {
                // Add some random symbol from the interface alphabet
                refineWithArbitrarySymbol()
                AGContinue()
              }
          }
        } catch {
          case e : AGIntermediateResult => e
          case e => throw e
        }
      }
      findNewSymbol(cexTrace)
    }
  }

  /**
   * Apply automatic AG; retrun None on succes, and a confirmed cex otherwise.
   */
  def check() : Option[Trace] = {
    configuration.resetCEX()
    var currentState : AGIntermediateResult = AGContinue()
    while(currentState == AGContinue()) {
      var newAss = dfaGenerator.generateAssumptions()
      // If the constraints are unsat, then refine the alphabet and try again
      // They cannot be unsat if the alphabets are complete
      assert(newAss != None || configuration.get().alphabetRefinement)
      while(newAss == None) do {
        if configuration.get().verbose then {
          System.out.println("Refining alphabet due to constraints being unsat")
        }
        val newSymbols = this.latestCex.filter(interfaceAlphabet.contains(_)).toSet.diff(this.assumptionAlphabet)
        if (!newSymbols.isEmpty) then {
          System.out.println(s"${YELLOW}Extending alphabet with symbol: ${newSymbols.head}${RESET}")
          this.addSymbolToAssumptionAlphabet(Set(newSymbols.head))
        } else {
          refineWithArbitrarySymbol()
        }
        newAss = dfaGenerator.generateAssumptions()
      }
      newAss match {
        case Some(newAss) => this.assumptions = newAss
        case None => throw Exception("Not possible")
      }
      // for (ass,i) <- assumptions.zipWithIndex do {
      //   System.out.println(s"${ass.name} for process ${processes(i).systemName} alphabet: ${ass.alphabet}")
      //   ass.visualize()
      // }
      currentState = this.applyAG() 
      currentState match {
        case AGFalse(cex) =>
          currentState = alphabetRefine(cex) 
          if currentState == AGContinue() then {
            if configuration.get().verbose then
              System.out.println(s"New assumption alphabet: ${assumptionAlphabet}")
          }
        case _ => ()
      }
    }
    currentState match {
      case AGFalse(cex) => Some(cex)
      case e: AGSuccess =>
        if configuration.get().visualizeDFA then {
          for (ass,i) <- assumptions.zipWithIndex do {
            System.out.println(s"${ass.name} for process ${processes(i).systemName} alphabet: ${ass.alphabet}")
            ass.visualize()
          }
        }
        None
      case _ => throw Exception("Inconclusive")
    }
  }
}


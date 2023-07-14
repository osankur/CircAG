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

import net.automatalib.automata.fsa.impl.FastDFA
import net.automatalib.automata.fsa.impl.FastDFAState
import net.automatalib.words.impl.Alphabets;

import fr.irisa.circag._
import fr.irisa.circag.DLTS
import fr.irisa.circag.Trace
import fr.irisa.circag.configuration
import fr.irisa.circag.statistics

import fr.irisa.circag.isPrunedSafety

class DFAAutomaticVerifierAlphabetRefinement(
    _ltsFiles: Array[File],
    _err: String,
    assumptionGeneratorType: AssumptionGeneratorType =
      AssumptionGeneratorType.RPNI,
) extends DFAAutomaticVerifier(_ltsFiles, _err, assumptionGeneratorType) {

  protected var assumptionAlphabet = propertyAlphabet

  /** The assumption DLTS g_i for each process i.
    */
  assumptions = {
    (0 until this.ltsFiles.size)
      .map({ i =>
        val alph = assumptionAlphabet.intersect(processes(i).alphabet)
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


  private def refineWithArbitrarySymbol(): Unit = {
    val newSymbols = interfaceAlphabet.diff(this.assumptionAlphabet)
    assert(!newSymbols.isEmpty)
    // if configuration.get().verbose then {
    System.out.println(
      s"${YELLOW}Extending alphabet by arbitrarily chosen symbol: ${newSymbols.head}${RESET}"
    )
    // }
    this.addSymbolToAssumptionAlphabet(Set(newSymbols.head))
  }

  private def alphabetRefine(cexTrace: Trace): AGIntermediateResult = {
    val currentAlphabets = assumptions.map(_.alphabet)
    if (this.completeAlphabets == currentAlphabets) then {
      // All alphabets are complete; we can conclude
      AGFalse(cexTrace)
    } else {
      // MATCH: Check if each pair of traces match when projected to their common alphabet
      def findMismatch(
          processTraces: Buffer[List[String]]
      ): Option[(Int, Int)] = {
        var result: Option[(Int, Int)] = None
        for i <- 0 until this.processes.size do {
          for j <- 0 until i do {
            val commonAlphabet =
              processes(i).alphabet.intersect(processes(j).alphabet)
            if (processTraces(i).filter(commonAlphabet) != processTraces(j)
                .filter(commonAlphabet))
            then {
              result = Some((i, j))
            }
          }
        }
        result
      }
      def findNewSymbol(cex: List[String]): AGIntermediateResult = {
        // Extend the trace to the alphabet of each TA separately (projected to the TA's external alphabet)
        // This cannot fail when cex == cexTrace, but can afterwards
        try {
          val processTraces = processes.zipWithIndex.map { (p, i) =>
            p.checkTraceMembership(cex) match {
              case Some(processTrace) =>
                val interfaceTrace =
                  processTrace.filter(interfaceAlphabet.contains(_))
                if configuration.get().verbose then {
                  System.out.println(
                    s"Concretized trace for process ${p.systemName}: ${processTrace}"
                  )
                  System.out.println(
                    s"\tProjected to completeAlphabet: ${interfaceTrace}"
                  )
                }
                interfaceTrace
              case None if cex == cexTrace =>
                throw Exception(
                  s"Trace $cex fails the final premise but cannot be reproduced here"
                )
              case _ =>
                refineWithArbitrarySymbol()
                throw AGContinue()
            }
          }
          findMismatch(processTraces) match {
            case None =>
              // All processes agree on these traces: check also if cex is rejected by the property
              if (!propertyDLTS.dfa.accepts(
                  cex.filter(propertyDLTS.alphabet.contains(_))
                ))
              then AGFalse(cex)
              else {
                // If not, then we cannot conclude: so we add an arbitrary new symbol from the traces or from interface alphabet
                // Add some random symbol
                val newTraceSymbols = processTraces
                  .map(_.toSet)
                  .fold(Set[String]())({ (a, b) => a | b })
                  .diff(assumptionAlphabet)
                if (!newTraceSymbols.isEmpty) then {
                  this.addSymbolToAssumptionAlphabet(Set(newTraceSymbols.head))
                } else {
                  refineWithArbitrarySymbol()
                }
                AGContinue()
              }
            case Some((i, j)) =>
              // Otherwise choose a symbol that appears in a process trace but not in the current alphabet, and iterate
              val traceSymbols = processTraces
                .map(_.toSet)
                .fold(Set[String]())({ (a, b) => a | b })
              val newSymbols = traceSymbols.diff(this.assumptionAlphabet)
              if (!newSymbols.isEmpty) then {
                val newSymbol = newSymbols.head
                // if (configuration.get().verbose)
                System.out.println(
                  s"${YELLOW}Adding new symbol to assumption alphabet: ${newSymbol}${RESET}"
                )

                this.addSymbolToAssumptionAlphabet(Set(newSymbol))
                AGContinue()
              } else if (processTraces(i).size > cex.size || processTraces(
                  j
                ).size > cex.size)
              then {
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
          case e: AGIntermediateResult => e
          case e                       => throw e
        }
      }
      findNewSymbol(cexTrace)
    }
  }
  /** Updates assumptionAlphabet, and consequently processDependencies,
    * propertyDependencies, and resets dfa generator.
    *
    * @param newAlphabet
    */
  private def addSymbolToAssumptionAlphabet(newSymbols: Set[String]): Unit = {
    assumptionAlphabet |= newSymbols
    proofSkeleton.setAssumptionAlphabetsByCommonAlphabet(assumptionAlphabet)
    // Create a new constraint manager initialized with the incremental traces from the previous instance
    dfaGenerator = DFAGenerator(
      proofSkeleton,
      assumptionGeneratorType,
      dfaGenerator.incrementalTraces
    )
    configuration.resetCEX()
  }

  /** Apply automatic AG; retrun None on succes, and a confirmed cex otherwise.
    */
  override def proveGlobalPropertyByLearning(fixedAssumptions : Option[List[Int]] = None): Option[Trace] = {
    configuration.resetCEX()
    val fixedAssumptionsMap = HashMap[Int, DLTS]()
    fixedAssumptions.getOrElse(List()).foreach(i => 
      fixedAssumptionsMap.put(i, assumptions(i))      
    )

    var currentState: AGIntermediateResult = AGContinue()
    while (currentState == AGContinue()) {
      var newAss = dfaGenerator.generateAssumptions(fixedAssumptionsMap)
      // If the constraints are unsat, then refine the alphabet and try again
      // They cannot be unsat if the alphabets are complete
      assert(newAss != None || configuration.get().alphabetRefinement)
      while (newAss == None) do {
        if configuration.get().verbose then {
          System.out.println("Refining alphabet due to constraints being unsat")
        }
        val newSymbols = this.latestCex
          .filter(interfaceAlphabet.contains(_))
          .toSet
          .diff(this.assumptionAlphabet)
        if (!newSymbols.isEmpty) then {
          System.out.println(
            s"${YELLOW}Extending alphabet with symbol: ${newSymbols.head}${RESET}"
          )
          this.addSymbolToAssumptionAlphabet(Set(newSymbols.head))
        } else {
          refineWithArbitrarySymbol()
        }
        newAss = dfaGenerator.generateAssumptions(fixedAssumptionsMap)
      }
      newAss match {
        case Some(newAss) => this.assumptions = newAss
        case None         => throw Exception("Not possible")
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
              System.out.println(
                s"New assumption alphabet: ${assumptionAlphabet}"
              )
          }
        case _ => ()
      }
    }
    currentState match {
      case AGFalse(cex) => Some(cex)
      case e: AGSuccess =>
        if configuration.get().visualizeDFA then {
          for (ass, i) <- assumptions.zipWithIndex do {
            System.out.println(
              s"${ass.name} for process ${processes(i).systemName} alphabet: ${ass.alphabet}"
            )
            ass.visualize()
          }
        }
        None
      case _ => throw Exception("Inconclusive")
    }
  }


}


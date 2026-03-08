package fr.irisa.circag.dfa

import io.AnsiColor._
import org.slf4j.Logger
import org.slf4j.LoggerFactory
import scala.collection.mutable.{HashMap, Buffer, Map}
import scala.collection.immutable.Set
import scala.sys.process._
import os.Path
import java.nio.file.Files
import upickle.default._
import fr.irisa.circag.statistics
import fr.irisa.circag.configuration
import fr.irisa.circag.{Trace, DLTS, Alphabet}
import fr.irisa.circag.pruned
import fr.irisa.circag.ltl.MalformedLTL

case class Instance(atomic_propositions: List[String], 
  nb_formulas : Int, 
  traces : List[Trace], 
  constraints : List[Map[String, List[List[Int]]]]) derives ReadWriter


class DFABoltGenerator(
    system : SystemSpec,
    _proofSkeleton: DFAProofSkeleton,
    _dfaLearnerAlgorithm: DFALearningAlgorithm
) extends DFAGenerator(system, _proofSkeleton) {
  protected val logger = LoggerFactory.getLogger("CircAG")

  val traces = HashMap[Trace, Int]()
  val constraints = Buffer[Map[String, List[List[Int]]]]()
  var query_count = 0

  override def reset() : Unit = {
    traces.clear()
    constraints.clear()
  }

  private def getTraceIndex(trace : Trace) : Int = {
    traces.getOrElseUpdate(trace, traces.size)
  }

  private def getInstance() : Instance = {
    val alphabet = system.processes
      .map(p => p.alphabet)
      .foldLeft(Set.empty[String])((x, y) => x | y)
    val c : List[Map[String, List[List[Int]]]] = constraints.toList
    Instance(alphabet.toList, system.nbProcesses, traces.keys.toList, c)
  }


  override def refineByFinalPremiseCounterexample(trace: Trace) : Unit = {
    val lhs = 
      (0 until system.nbProcesses)
      .map{ i => 
          List(getTraceIndex(trace.dropRight(1).filter(system.processes(i).alphabet.contains)), 
          i)
        }
      .toList
    constraints.append(HashMap("left_predicates" -> lhs, "right_predicate" -> List()))
  }

  
  override def generateAssumptions(
      fixedAssumptions: Map[Int, DLTS] = Map()
  ): Option[Buffer[DLTS]] = { 
    val instance = getInstance()
    val tmpFile = os.temp(prefix=s"query${query_count}", suffix = ".json")
    os.write.over(tmpFile, write(instance))
    val cmd = s"bolt -u ${tmpFile.toString()} 5 5 horn-search 10 sat"
    logger.debug(s"${BLUE}${cmd}${RESET}")
    val output = cmd.!!
    val output_lines = output.split("\n")
    logger.debug(s"${output_lines.toList}")
    Some(output_lines
      .map{ ltlf => if ltlf == "_" then "true" else ltlf }
      .zipWithIndex
      .map{ (ltlf,i) =>
        val proc = s"echo ${ltlf}" #| "ltlf2dfa - "
        logger.debug(s"Running ${proc}")
        val output = StringBuffer()
        if (proc.run(BasicIO(false, output, None)).exitValue != 0 ){
          throw (MalformedLTL(output.toString()))
        }
        logger.debug(s"${output}")
        val dlts = DLTS.fromHOAString(output.toString(), Some(system.processes(i).alphabet))
        throw Exception("Spot's ltlf2dfa has accepting transitions. The DLTS must be converted to state-based acceptance.")
        DLTS(s"${dlts.name}${i}", dlts.dfa.pruned, dlts.alphabet)
      }
      .toBuffer
    )
  }

  override def refineByInductivePremiseCounterexample(processID : Int, cexTrace : Trace) : Unit = {
    val preds = 
      (0 until system.nbProcesses)
      .map{ i => 
          List(getTraceIndex(cexTrace.filter(system.processes(i).alphabet.contains)), 
          i)
        }
    val rhs = List(preds(processID))
    val lhs = preds.filter(x => x(1) != processID).toList
    constraints.append(HashMap("left_predicates" -> lhs, "right_predicate" -> rhs))
  }
}
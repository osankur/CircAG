package fr.irisa.circag.dfa

import scala.collection.convert.ImplicitConversions._
import io.AnsiColor._
import org.slf4j.Logger
import org.slf4j.LoggerFactory
import scala.collection.mutable.{HashMap, Buffer, Map}
import scala.collection.immutable.Set
import scala.sys.process._
import os.Path
import java.nio.file.Files
import java.io.File
import upickle.default._
import java.nio.file.Paths
import java.io.PrintWriter

import fr.irisa.circag.statistics
import fr.irisa.circag.configuration
import fr.irisa.circag.{Trace, DLTS, Alphabet}
import fr.irisa.circag.{pruned, isSafety}
import fr.irisa.circag.ltl.MalformedLTL
import fr.irisa.circag.TA

def stringOfConstraint(c : Map[String, List[List[Int]]], instance : Instance) : String = {
  val lhs = 
    c.getOrElse("left_predicates", List())
    .map( {l => s"${instance.traces(l.head)} |= phi_${l(1)}"})
    .mkString(" /\\ ")
  val rhs = 
    c.getOrElse("right_predicate", List[List[Int]]())  
    match {
    case List() => "false"
    case List(List(t,i)) => 
      s"${instance.traces(t)} |= phi_${i}"
    case _ => throw Exception("Malformed RHS")
  }
  s"$lhs -> $rhs"
}

case class Instance(atomic_propositions: List[String], 
  nb_formulas : Int, 
  traces : List[Trace], 
  constraints : List[Map[String, List[List[Int]]]]) derives ReadWriter {
    override def toString(): String = {
      val sb = StringBuffer()
      for (c,i) <- this.constraints.zipWithIndex do {
        sb.append(s"C_$i: ${stringOfConstraint(c, this)}\n")
      }
      sb.toString
    }
  }

/**
 * Use external tool Bolt to generate LTLf assumptions respecting given (Horn) constraints.
 * LTLf formulas are translated to DFAs using Spot.
 * 
 * FIXME Automatic learning can fail using this generator currently since resulting DFAs are not always prefix-closed.
 */
class DFABoltGenerator(
    system : SystemSpec,
    _proofSkeleton: DFAProofSkeleton,
    _dfaLearnerAlgorithm: DFALearningAlgorithm
) extends DFAGenerator(system, _proofSkeleton) {
  protected val logger = LoggerFactory.getLogger("CircAG")

  val traces = HashMap[Trace, Int]()
  val tracesPerProcess : Buffer[Buffer[Trace]] = Buffer.tabulate(system.nbProcesses)(_ => Buffer[Trace]())
  val constraints = Buffer[Map[String, List[List[Int]]]]()
  var query_count = 0

  // Check if given assumptions do satisfy the constraints
  private def checkAssumptions(assumptions : Buffer[DLTS], ltl_formulas : Array[String], instance : Instance) : Unit = {
    val traces : Buffer[Trace] = instance.traces.toBuffer
    for (c, i) <- instance.constraints.zipWithIndex do {
      val lhs = c
      .getOrElse("left_predicates", List[List[Int]]())
      .map{ l =>
          val t = traces(l(0))
          val b = assumptions(l(1)).dfa.accepts(t)
          b
        }
      val rhs = c.getOrElse("right_predicate", List[List[Int]]())
        .map { l =>
          val t = traces(l(0))
          val b = assumptions(l(1)).dfa.accepts(t)
          if b then logger.debug(s"$t |= ${ltl_formulas(l(1))}")
          else logger.debug(s"$t |/= ${ltl_formulas(l(1))}")
          b
        }
      if lhs.forall(p => p) && !rhs.forall(p => p) then {
        logger.error(s"Constraint $i does not hold. LHS: $lhs RHS: $rhs")
        logger.error(s"Constraint $i: ${{stringOfConstraint(c, instance)}}")
        logger.error(s"Formulas: ${ltl_formulas.toList}")
      }
      assert(!lhs.forall(p => p) || rhs.forall(p => p), s"Constraint $i does not hold. LHS: $lhs RHS: $rhs")
    }
  }

  override def reset() : Unit = {
    tracesPerProcess.clear()
    traces.clear()
    constraints.clear()
  }

  private def getTraceIndex(trace : Trace, processID : Int) : (Int, Int) = {
    val itrace = traces.getOrElseUpdate(trace, traces.size)
    // If the trace is new for processID, then add prefix-closure constraints
    if !tracesPerProcess(processID).contains(trace) then {
      for old_trace <- tracesPerProcess(processID) if old_trace.size > 0 do {
        if old_trace.startsWith(trace) then {
          val lhs = List(getTraceIndex(old_trace, processID).toList)
          val rhs = List(List(itrace, processID))
          // old_trace |= phi_processID -> trace |= phi_processID
          constraints.append(HashMap("left_predicates" -> lhs, "right_predicate" -> rhs))
        }
        if trace.startsWith(old_trace) then {
          val rhs = List(getTraceIndex(old_trace, processID).toList)
          val lhs = List(List(itrace, processID))
          // trace |= phi_processID -> old_trace |= phi_processID
          constraints.append(HashMap("left_predicates" -> lhs, "right_predicate" -> rhs))
        }
      }
      tracesPerProcess(processID).append(trace)
    }
    (itrace, processID)
  }

  private def getInstance() : Instance = {
    val alphabet = system.processes
      .map(p => p.alphabet)
      .foldLeft(Set.empty[String])((x, y) => x | y)
    val c : List[Map[String, List[List[Int]]]] = constraints.toList
    val traces_list = Buffer.tabulate(traces.size){_ => List() : Trace}
    for (trace, index) <- traces do {
      traces_list(index) = trace
    }
    Instance(alphabet.toList, system.nbProcesses, traces_list.toList, c)
  }

  override def generateAssumptions(
      fixedAssumptions: Map[Int, DLTS] = Map()
  ): Option[Buffer[DLTS]] = { 
    val instance = getInstance()
    logger.debug(instance.toString())
    val tmpFile = os.temp(prefix=s"query${query_count}_", suffix = ".json")
    query_count += 1
    os.write.over(tmpFile, write(instance))
    logger.debug(s"Query ${query_count} with traces: ${instance.traces}")
    val cmd = s"bolt -u ${tmpFile.toString()} 5 5 horn-search 10 sat"
    logger.debug(s"${BLUE}${cmd}${RESET}")
    val output = cmd.!!
    if output.contains("Formula not found") then return None
    val output_lines = output.split("\n")
    logger.debug(s"${output_lines.toList}")
    val assumptions = 
      output_lines
      .map{ ltlf => if ltlf == "_" then "true" else ltlf }
      .zipWithIndex
      .map{ (ltlf,i) =>
        val proc = s"echo ${ltlf}" #| "ltlf2dfa - "
        logger.debug(s"Computing dlts_${query_count} for phi_$i: ${ltlf}")
        val output = StringBuffer()
        if (proc.run(BasicIO(false, output, None)).exitValue != 0 ){
          throw (MalformedLTL(output.toString()))
        }
        // Spot's ltlf2dfa outputs a DFA in HOA format with accepting transitions
        // Moreover the empty word is always rejected:
        val hoa_string = output.toString()
        // logger.debug(s"\n${hoa_string}")
        val dlts = DLTS.fromHOAStringWithAcceptingTransitions(hoa_string, Some(system.processes(i).alphabet))
        // But we want the mpty word to be always accepted:
        dlts.dfa.setAccepting(dlts.dfa.getInitialState(), true)
        val pc_dlts = DLTS.makePrefixClosed(dlts.dfa, dlts.alphabet, false)
        val pruned = DLTS(s"${dlts.name}${i}", pc_dlts.pruned, dlts.alphabet)
        if !dlts.dfa.isSafety then {
          logger.error(s"Displaying non-safety DFA for $i")
          dlts.visualize()
          logger.error(s"Displaying its prefix-closure: ")
          DLTS("pc_dlts", pc_dlts, dlts.alphabet).visualize()
          logger.error(s"Displaying its pruning: ")
          pruned.visualize()
          assert(false)
        }
        pruned
      }
      .toBuffer
    // Defensive check:
    dumpAssumptions(assumptions)
    checkAssumptions(assumptions, output_lines, instance)
    Some(assumptions)
  }

  override def refineByInductivePremiseCounterexample(processID : Int, cexTrace : Trace) : Unit = {
    val lhs = Buffer[List[Int]]()
    for i <- 0 until system.nbProcesses if i != processID do {
      val projTrace = cexTrace.dropRight(1).filter(system.processes(i).alphabet.contains)
      // if projTrace is empty then the predicate is true trivially, so nothing is added to lhs
      if projTrace.size > 0 then {
        val elem =getTraceIndex(projTrace, i).toList
        lhs.append(elem)
      }
    }
    val rightProjTrace = cexTrace.filter(system.processes(processID).alphabet.contains)
    // if the rightProjTrace is empty, then the predicate is true trivially, so no constraint needs to be added at all
    if rightProjTrace.size > 0 then {
      val rhs = List(getTraceIndex(rightProjTrace, processID).toList)
      constraints.append(HashMap("left_predicates" -> lhs.toList, "right_predicate" -> rhs))
    }
  }

  override def refineByFinalPremiseCounterexample(trace: Trace) : Unit = {
    val lhs = Buffer[List[Int]]()
    for i <- 0 until system.nbProcesses do {
      logger.debug(s"Alphabet($i) = ${system.processes(i).alphabet}")
      val projTrace = trace.filter(system.processes(i).alphabet.contains)
      if projTrace.size > 0 then 
        lhs.append(getTraceIndex(projTrace, i).toList)
    }
    if lhs.size > 0 then
      constraints.append(HashMap("left_predicates" -> lhs.toList, "right_predicate" -> List()))
  }

  def dumpAssumptions(assumptions : Buffer[DLTS]) : Unit = {
    val dir = Paths.get(".", ".circag_log")
    Files.createDirectories(dir)
    for i <- 0 until nbProcesses do {
      val tck = TA.fromLTS(assumptions(i))
      val writer = PrintWriter(new File(dir.toFile(), s"_assumption${i}_${system.processes(i).systemName}.tck"))
      writer.write(tck.toString())
      writer.close()
    }
    logger.info(s"Assumptions written into directory ${dir.getFileName().toString()}")
  }

}
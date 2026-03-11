package fr.irisa.circag.dfa

import scala.collection.mutable.{HashMap, Buffer, Map}
import scala.collection.immutable.Set
import upickle.default._
import fr.irisa.circag.statistics
import fr.irisa.circag.configuration
import fr.irisa.circag.{Trace, DLTS, Alphabet}
import fr.irisa.circag.pruned

/**
  * A logging wrapper for DFADisjunctiveGenerator.
  */
class LoggingDFADisjunctiveGenerator(
    system : SystemSpec,
    _proofSkeleton: DFAProofSkeleton,
    _dfaLearnerAlgorithm: DFALearningAlgorithm
) extends DFADisjunctiveGenerator(system, _proofSkeleton, _dfaLearnerAlgorithm) {

  val traces = HashMap[Trace, Int]()
  val constraints = Buffer[Map[String, List[List[Int]]]]()
  var query_count = 0

  private def logToFile(instance : Instance, file : String) : Unit = {
    val dir = os.pwd / "output"
    os.makeDir.all(dir)
    os.write.over(dir / file, write(instance))
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
    val lhs = Buffer[List[Int]]()
    for i <- 0 until system.nbProcesses do {
      logger.debug(s"Alphabet($i) = ${system.processes(i).alphabet}")
      val projTrace = trace.filter(system.processes(i).alphabet.contains)
      if projTrace.size > 0 then 
        lhs.append(List(getTraceIndex(projTrace), i))
    }
    if lhs.size > 0 then
      constraints.append(HashMap("left_predicates" -> lhs.toList, "right_predicate" -> List()))
    super.refineByFinalPremiseCounterexample(trace)
  }

  override def generateAssumptions(
      fixedAssumptions: Map[Int, DLTS] = Map()
  ): Option[Buffer[DLTS]] = { 
    val instance = getInstance()
    logToFile(instance, s"query$query_count.json")
    query_count += 1
    super.generateAssumptions(fixedAssumptions)
  }

  override def refineByInductivePremiseCounterexample(processID : Int, cexTrace : Trace) : Unit = {
    val lhs = Buffer[List[Int]]()
    for i <- 0 until system.nbProcesses if i != processID do {
      val projTrace = cexTrace.dropRight(1).filter(system.processes(i).alphabet.contains)
      // if projTrace is empty then the predicate is true trivially, so nothing is added to lhs
      if projTrace.size > 0 then {
        val elem =List(getTraceIndex(projTrace), i)
        lhs.append(elem)
      }
    }
    val rightProjTrace = cexTrace.filter(system.processes(processID).alphabet.contains)
    // if the rightProjTrace is empty, then the predicate is true trivially, so no constraint needs to be added at all
    if rightProjTrace.size > 0 then {
      val rhs = List(List(getTraceIndex(rightProjTrace), processID))
      constraints.append(HashMap("left_predicates" -> lhs.toList, "right_predicate" -> rhs))
    }
    // The [refineByInductivePremiseCounterexample] function has optimizations which means the resulting query is not Horn in general.
    // The following adds the non-optimized Horn clause.
    super.addDisjunctiveConstraint(processID, cexTrace, 34)
  }
}
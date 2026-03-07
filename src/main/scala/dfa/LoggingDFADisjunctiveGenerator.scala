package fr.irisa.circag.dfa

import scala.collection.mutable.{HashMap, Buffer, Map}
import scala.collection.immutable.Set
import upickle.default._
import fr.irisa.circag.statistics
import fr.irisa.circag.configuration
import fr.irisa.circag.{Trace, DLTS, Alphabet}
import fr.irisa.circag.pruned

case class Instance(atomic_propositions: List[String], 
  nb_formulas : Int, 
  traces : List[Trace], 
  constraints : List[Map[String, List[List[Int]]]]) derives ReadWriter

def writeToFile(instance : Instance, file : String) : Unit = {
  val dir = os.pwd / "output"
  os.makeDir.all(dir)
  os.write.over(dir / file, write(instance))
}

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
          List(getTraceIndex(trace.filter(system.processes(i).alphabet.contains)), 
          i)
        }
      .toList
    constraints.append(HashMap("left_predicates" -> lhs, "right_predicate" -> List()))
    super.refineByFinalPremiseCounterexample(trace)
  }

  override def generateAssumptions(
      fixedAssumptions: Map[Int, DLTS] = Map()
  ): Option[Buffer[DLTS]] = { 
    val instance = getInstance()
    writeToFile(instance, s"query$query_count.json")
    query_count += 1
    super.generateAssumptions(fixedAssumptions)
  }

  override def refineByInductivePremiseCounterexample(processID : Int, cexTrace : Trace) : Unit = {
    val preds = 
      (0 until system.nbProcesses)
      .map{ i => 
          List(getTraceIndex(cexTrace.dropRight(1).filter(system.processes(i).alphabet.contains)), 
          i)
        }
    val lhs = preds.filter(x => x(1) != processID).toList
    val rhs = List(List(getTraceIndex(cexTrace.filter(system.processes(processID).alphabet.contains)), processID))
    constraints.append(HashMap("left_predicates" -> lhs, "right_predicate" -> rhs))
    super.refineByInductivePremiseCounterexample(processID, cexTrace);
  }
}
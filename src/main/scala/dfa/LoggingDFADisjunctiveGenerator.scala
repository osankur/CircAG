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
  constraints : List[Map[String, List[(Int, Int)]]]) derives ReadWriter

def writeToFile(instance : Instance, file : String) : Unit = {
  val dir = os.pwd / "output"
  os.makeDir.all(dir)
  os.write.over(dir / file, write(instance))
}

/**
  * A logging wrapper to the above.
  */
class LoggingDFADisjunctiveGenerator(
    system : SystemSpec,
    _proofSkeleton: DFAProofSkeleton,
    _dfaLearnerAlgorithm: DFALearningAlgorithm
) extends DFADisjunctiveGenerator(system, _proofSkeleton, _dfaLearnerAlgorithm) {

  val constraints : Buffer[(Trace, Option[Int])] = Buffer()
  var query_count = 0

  private def getInstance() : Instance = {
    val alphabet = system.processes
      .map(p => p.alphabet)
      .foldLeft(Set.empty[String])((x, y) => x | y)
    val traces = constraints.map(x => x._1)
    val indexed_constraints = 
      constraints
        .zipWithIndex
        .map({ x => x match {
          case ((_, None),i) => 
            val lhs = (0 until system.nbProcesses)
              .map{ j => (i, j)}
              .toList
            HashMap("left_predicates" -> lhs, "right_predicate" -> List())
          case ((_, Some(k)), i) =>
            val lhs = (0 until system.nbProcesses)
              .filter(j => j != k)
              .map{ j => (i, j)}
              .toList
            val rhs = List((i, k))
            HashMap("left_predicates" -> lhs, "right_predicate" -> rhs)
        }
      }).toList
    Instance(alphabet.toList, system.nbProcesses, traces.toList, indexed_constraints)
  }


  override def refineByFinalPremiseCounterexample(trace: Trace) : Unit = {
    constraints.append((trace, None))
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
    constraints.append((cexTrace, Some(processID)))
    super.refineByInductivePremiseCounterexample(processID, cexTrace)
  }
}
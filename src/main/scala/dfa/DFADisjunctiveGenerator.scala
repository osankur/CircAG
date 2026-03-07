package fr.irisa.circag.dfa

import scala.collection.mutable.{HashMap, Buffer, Map}
import collection.JavaConverters._
import collection.convert.ImplicitConversions._
import scala.util.control.Breaks.{break,breakable}
import org.slf4j.Logger
import org.slf4j.LoggerFactory

import io.AnsiColor._
import com.microsoft.z3

import net.automatalib.words.impl.Alphabets;
import net.automatalib.automata.fsa.impl.{
  FastDFA
}

import fr.irisa.circag.statistics
import fr.irisa.circag.configuration
import fr.irisa.circag.{Trace, DLTS, Alphabet}
import fr.irisa.circag.pruned

/**
  * Disjunctive DFA generator which keeps a list of disjunctive constraints excluding previous counterexamples.
  * DFAs are generated all at once using a big SAT query.
  */
class DFADisjunctiveGenerator(
    _system : SystemSpec,
    _proofSkeleton: DFAProofSkeleton,
    dfaLearnerAlgorithm: DFALearningAlgorithm
) extends DFAGenerator(_system, _proofSkeleton) {
  require(dfaLearnerAlgorithm == DFALearningAlgorithm.SAT)

  val logger = LoggerFactory.getLogger("CircAG")

  protected val z3ctx = {
    val cfg = HashMap[String, String]()
    cfg.put("model", "true")
    z3.Context(cfg);
  }

  // Boolean variable corresponding to each pair (pr,trace)
  protected val toVars = HashMap[(Int, Trace), z3.BoolExpr]()
  protected val toIndexedTraces = HashMap[z3.BoolExpr, (Int, Trace)]()

  protected var solver = z3ctx.mkSolver()

  // Set of all samples added so far
  protected val samples = Buffer.tabulate(nbProcesses)({ _ =>
    Buffer[(Trace, z3.BoolExpr)]()
  })

  protected var overallBound = nbProcesses

  this.reset()

  /** Return the unique SAT variable to the given pair (process, trace)
    *
    * @param process
    * @param trace
    * @return
    */
  private def varOfIndexedTrace(process: Int, trace: Trace): z3.BoolExpr = {
    if (toVars.contains((process, trace))) then {
      toVars((process, trace))
    } else {
      val v = z3ctx.mkBoolConst(z3ctx.mkSymbol(s"${(process, trace)}"))
      toVars.put((process, trace), v)
      toIndexedTraces.put(v, (process, trace))
      samples(process).append((trace, v))
      // updateTheoryConstraints(process, samples(process).size - 1)
      v
    }
  }

  /** Reinitialize the solver and samples.
    */
  def reset(): Unit = {
    this.solver = z3ctx.mkSolver()
    this.samples.foreach(_.clear())
    this.toVars.clear()
    this.toIndexedTraces.clear()

    // the empty word must be accepted by all
    solver.add(z3ctx.mkAnd((0 until nbProcesses).map({ i =>
      varOfIndexedTrace(i, List[String]())
    }): _*))
  }

  override def refineByInductivePremiseCounterexample(processID : Int, cexTrace : Trace) : Unit = {
    val prefixInP = system.property match{
      case None => false
      case Some(propertyDLTS) => 
        propertyDLTS.dfa.accepts(
          cexTrace.dropRight(1).filter(propertyDLTS.alphabet.contains(_))
        )
    }
    val traceInP = system.property match{
      case None => false
      case Some(propertyDLTS) => 
        propertyDLTS.dfa.accepts(cexTrace.filter(propertyDLTS.alphabet.contains(_)))
    }
    if (prefixInP && !traceInP) then {
      addDisjunctiveConstraint(processID, cexTrace, 22)
    } else if (cexTrace.size > 0 && !prefixInP && !traceInP) then {
      addDisjunctiveConstraint(processID, cexTrace, 29)
    } else {
      addDisjunctiveConstraint(processID, cexTrace, 34)
    }
  }

  private def addDisjunctiveConstraint(process: Int, trace: Trace, constraintType: Int): Unit = {
    constraintType match {
      case 34 =>
        assert(trace.size > 0)
        val prefix = trace.dropRight(1)
        val lhs =
          if prefix.size > 0 then
            proofSkeleton
              .processDependencies(process)
              .map({ j =>
                z3ctx.mkNot(varOfIndexedTrace(j, prefix))
              })
              .toSeq
          else {
            Seq(z3ctx.mkFalse())
          }

        val newConstr =
          z3ctx.mkOr(z3ctx.mkOr(lhs: _*), varOfIndexedTrace(process, trace))
        solver.add(newConstr)
      case 22 =>
        val prefix = trace.dropRight(1)
        val term1 =
          z3ctx.mkOr(
            proofSkeleton
              .processDependencies(process)
              .map({ j =>
                z3ctx.mkNot(varOfIndexedTrace(j, prefix))
              })
              .toSeq: _*
          )
        val term2 =
          z3ctx.mkAnd(
            varOfIndexedTrace(process, trace),
            z3ctx.mkOr(
              (proofSkeleton.propertyDependencies() - process)
                .map({ j =>
                  z3ctx.mkNot(varOfIndexedTrace(j, trace))
                })
                .toSeq: _*
            )
          )
        val newConstr = z3ctx.mkOr(term1, term2)
        solver.add(newConstr)
      case 29 =>
        val prefix = trace.dropRight(1)
        val term1 =
          z3ctx.mkOr(
            proofSkeleton
              .processDependencies(process)
              .map({ j =>
                z3ctx.mkNot(varOfIndexedTrace(j, prefix))
              })
              .toSeq: _*
          )
        val term2 =
          z3ctx.mkAnd(
            varOfIndexedTrace(process, trace),
            z3ctx.mkOr(
              (proofSkeleton.propertyDependencies() -- proofSkeleton
                .processDependencies(process) - process)
                .map({ j =>
                  z3ctx.mkNot(varOfIndexedTrace(j, trace))
                })
                .toSeq: _*
            )
          )
        val newConstraint = z3ctx.mkOr(term1, term2)
        solver.add(newConstraint)
    }
  }

  override def refineByFinalPremiseCounterexample(trace: Trace): Unit = {
    breakable{
      for j <- 0 until nbProcesses do {
          if system.processes(j).checkTraceMembership(trace, Some(proofSkeleton.assumptionAlphabets(j))) == None then {
            break
          }
      }
      throw AGResult.GlobalPropertyViolation(trace)
    }
    val newConstraint = z3ctx.mkOr(
      z3ctx.mkOr(
        proofSkeleton
          .propertyDependencies()
          .map({ j => z3ctx.mkNot(varOfIndexedTrace(j, trace)) })
          .toSeq: _*
      )
    )
    solver.add(newConstraint)
  }

  /** Generate assumptions satisfying the constraints, except that those
    * processes whose DLTSs are given as argument. Note that fixing some of the
    * assumptions can make the constraints unsatisfiable.
    *
    * @param fixedAssumptions
    *   process indices and their fixed assumptions
    * @return
    *   None if the constraints are unsat, and an assumption for each process
    *   otherwise.
    */
  override def generateAssumptions(
      fixedAssumptions: Map[Int, DLTS] = Map()
  ): Option[Buffer[DLTS]] = {
    if fixedAssumptions.size > 0 then 
      throw Exception(s"${this.getClass.getName()} does not support fixed assumptions")
    statistics.Counters.incrementCounter("DFA Generator")

    var beginTime = System.nanoTime()

    // Generate SAT query to guess nb.Processes automata of total size at most k
    //  States: 1..k; 
    //  Process i has states error_state(i-1)+1...error_state(i)
    //  (The first one is the init, and the last one is the error state)
    var k = 2 * nbProcesses
    var allDLTS : Option[Buffer[DLTS]] = None

    while allDLTS == None && k < configuration.get().maxDFASize do {
      solver.push()
      // val prefixes = Buffer.tabulate(this.nbProcesses)(_ => Set[Trace]())
      // State reached in process when reading given trace:
      val states_at = Buffer.tabulate(this.nbProcesses)(_ => HashMap[Trace, z3.IntExpr]())
      for process <- 0 until nbProcesses do {
        for (w, varw) <- samples(process) do {
          val proj_w = w.filter(proofSkeleton.assumptionAlphabets(process).contains(_))
          for i <- 0 to proj_w.size do {
            val prefix = proj_w.dropRight(i)
            // prefixes(process) = prefixes(process).incl(prefix)
            states_at(process).put(prefix, z3ctx.mkIntConst(s"q${process}${prefix.toString()}"))
          }
        }
      }

      val error_state = HashMap[Int, z3.IntExpr]()
      for i <- -1 until nbProcesses do {
        error_state.put(i, z3ctx.mkIntConst(s"error(${i})"))
      }

      // (process, sigma) is mapped to a next-state function N -> N
      val next = Buffer.tabulate(this.nbProcesses)(_ => HashMap[String, z3.FuncDecl[com.microsoft.z3.ArithSort]]())

      solver.add(z3ctx.mkEq(error_state(-1), z3ctx.mkInt(0)))
      for i <- -1 until nbProcesses-1 do {
        // error_state(i) + 2 <= error_state(i+1)
        solver.add(z3ctx.mkLe(z3ctx.mkAdd(error_state(i), z3ctx.mkInt(2)), error_state(i+1)))
      }
      solver.add(z3ctx.mkEq(error_state(nbProcesses-1), z3ctx.mkInt(k)))
      for process <- 0 to nbProcesses-1 do {
        for sigma <- proofSkeleton.assumptionAlphabets(process) do {
          next(process).put(sigma, z3ctx.mkFuncDecl(s"next${process}_${sigma}", z3ctx.mkIntSort(), z3ctx.mkIntSort()))
          for q <- 1 to k do {
            // error_state(i-1) < q <= error_state(i) -> error_state(i-1) < next(i)(sigma) <= error_state(i)
            val q_in_i = z3ctx.mkAnd(z3ctx.mkLe(z3ctx.mkInt(q), error_state(process)), z3ctx.mkGt(z3ctx.mkInt(q), error_state(process-1)))          
            solver.add(z3ctx.mkImplies(q_in_i, z3ctx.mkLe(z3ctx.mkApp(next(process)(sigma), z3ctx.mkInt(q)), error_state(process))))
            solver.add(z3ctx.mkImplies(q_in_i, z3ctx.mkGt(z3ctx.mkApp(next(process)(sigma), z3ctx.mkInt(q)), error_state(process-1))))
          }
        }
      }
      for process <- 0 until nbProcesses do {
        // Set initial states
        solver.add(z3ctx.mkEq(states_at(process)(List()), z3ctx.mkAdd(error_state(process-1), z3ctx.mkInt(1))))

        // Make error absorbing
        for sigma <- proofSkeleton.assumptionAlphabets(process) do {
          solver.add(z3ctx.mkEq(error_state(process), z3ctx.mkApp(next(process)(sigma), error_state(process))))
        }

        // If w and w.sigma are both in prefixes of process, then 
        // the next_{process, sigma}( states_at(w) ) = states_at(w.sigma)
        for (w, state_w) <- states_at(process) do {
          for sigma <- proofSkeleton.assumptionAlphabets(process) do {
            val wsigma = w.appended(sigma)
            if states_at(process).contains(wsigma) then {
              solver.add(z3ctx.mkEq(z3ctx.mkApp(next(process)(sigma), state_w), states_at(process)(wsigma)))
            }
          }
        }
        // (process, w) <=> states_at(w) is accepting
        for (w, accept_w) <- samples(process) do {
          val proj_w = w.filter(proofSkeleton.assumptionAlphabets(process).contains(_))
          solver.add(z3ctx.mkIff(accept_w, z3ctx.mkNot(z3ctx.mkEq(states_at(process)(proj_w), error_state(process)))))
        }
      }
      if solver.check() == z3.Status.SATISFIABLE then {
        val m = solver.getModel()
        val all_dlts = Buffer.tabulate[DLTS](nbProcesses)(
          process =>
            val m = solver.getModel()
            val sizeExpr = m.eval(z3ctx.mkSub(error_state(process), error_state(process-1)), false)
            assert(sizeExpr != null)
            val dfaSize = Integer.parseInt(sizeExpr.toString())
            val offset = Integer.parseInt(m.eval(error_state(process-1), false).toString()) + 1
          
            val listAlphabet = proofSkeleton.assumptionAlphabets(process).toList
            val newDFA =
              new FastDFA(Alphabets.fromList(listAlphabet))
            val states =
              (0 until dfaSize).map(i => newDFA.addState(i < dfaSize - 1))
            newDFA.setInitial(states(0), true)
            for s <- 0 until dfaSize do {
              for alpha <- listAlphabet do {
                val next_state = Integer.parseInt(m.eval(z3ctx.mkApp(next(process)(alpha), z3ctx.mkInt(s+offset)), false).toString())
                newDFA.setTransition(states(s), alpha, states(next_state - offset))
              }
            }
            val dlts = DLTS(s"assumption_${process}_${proofSkeleton.system.processes(process).systemName}", newDFA.pruned, proofSkeleton.assumptionAlphabets(process))
            dlts
        )
        allDLTS = Some(all_dlts)
      }
      solver.pop()
      k += 1
    }
    statistics.Timers.incrementTimer("z3", (System.nanoTime() - beginTime))
    allDLTS
  }
}
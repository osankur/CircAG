package fr.irisa.circag
import java.io.File
import scala.collection.mutable.StringBuilder
import scala.collection.mutable.Buffer

import io.AnsiColor
import fr.irisa.circag.dfa._
import fr.irisa.circag.ltl._

enum DFAProofState:
    override def toString() : String = {
        this match {
            // case DFAProofState.Unknown => s"${AnsiColor.BLUE}?${AnsiColor.RESET}"
            // case DFAProofState.Proved => s"${AnsiColor.GREEN}\u2713${AnsiColor.RESET}"
            // case DFAProofState.Disproved(cex) => s"${AnsiColor.RED}X (${cex}) ${AnsiColor.RESET}"
            case DFAProofState.Unknown => s"?"
            case DFAProofState.Proved => s"\u2705"
            case DFAProofState.PremiseSucceeded => s"(\u2705)?"
            case DFAProofState.PremiseFailed(cex) => s"(\u274C) ${cex}"
            case DFAProofState.Disproved(cex) => s"\u274C ${cex}"
        }
    }
    case Unknown, Proved, PremiseSucceeded
    case PremiseFailed(cex : Trace)
    case Disproved(cex : Trace)

enum LTLProofState:
    override def toString() : String = {
        this match {
            case LTLProofState.Unknown => s"?"
            case LTLProofState.Proved => s"\u2713"
            case LTLProofState.Disproved(cex) => s"\u274C (${cex})"
        }
    }
    case Proved, Unknown
    case Disproved(cex : Lasso)

enum ProofMode:
    case DFA, LTL

class Interactive(
    val filenames : List[String], 
    private var dfaProperty : Option[DLTS] = None, 
    private var ltlProperty : LTL = LTLTrue()
    )
{
    var proofMode = ProofMode.DFA
    val files = filenames.map(s => java.io.File(s))
    val nbProcesses = files.size
    files.foreach(f=> if !f.exists() then throw Exception(s"File ${f} could not be read"))
    var dfaVerifier = DFAAutomaticVerifier(files.toArray, dfaProperty, DFALearnerAlgorithm.RPNI)
    var ltlVerifier = LTLVerifier(files.toArray, ltlProperty)

    private var dfaProofStates = Buffer.fill(nbProcesses)(DFAProofState.Unknown)
    private var dfaPropertyProofState = DFAProofState.Unknown
    private var ltlProofStates = Buffer.fill(nbProcesses)(LTLProofState.Unknown)
    private var ltlPropertyProofState = LTLProofState.Unknown

    def getDFAProofState(processID : Int ) : DFAProofState = dfaProofStates(processID)
    def getLTLProofState(processID : Int ) : LTLProofState = ltlProofStates(processID)

    def reset() : Unit = {}

    def setProofMode(mode : ProofMode) : Unit = {
        proofMode = mode
    }

    def setLTLProperty(ltlProperty : LTL) : Unit = {
        this.ltlProperty = ltlProperty
        var ltlVerifier = LTLVerifier(files.toArray, ltlProperty)
    }

    /**
      * Sets the states of all processes whose assumptions were proven to proven.
      * Consider them in topological order: at each iteration, a cluster c of processes is considered such that
      * each i in c hdepends on the whole c and on possibly other processes that are further left.
      * i is proven if all in c are either Proven or PremiseSucceeded, and if all other dependencies are Proven.
      *
      * @param processID
      */
    private def updateDFAProofStates() : Unit = {
        val topOrder = dfaVerifier.proofSkeleton.getTopologicalOrder()
        topOrder.foreach(
            c => 
                val localSuccess = c.forall( i => dfaProofStates(i) == DFAProofState.PremiseSucceeded || dfaProofStates(i) == DFAProofState.Proved)                
                if localSuccess then {
                    for i <- c do {
                        if dfaVerifier
                        .proofSkeleton
                        .processDependencies(i)
                        .diff(c)
                        .forall(j => dfaProofStates(j) == DFAProofState.Proved) then {
                            dfaProofStates(i) = DFAProofState.Proved
                        }
                    }
                }                
        )
    }
    /**
      * Recursively set the DFA proof state of processID to Unknown,
      * and those whose depended on processID as well.
      *
      * @param processID
      */
    private def invalidateDFAProofState(processID : Int) : Unit = {
        if (dfaProofStates(processID) == DFAProofState.PremiseSucceeded || 
            dfaProofStates(processID) == DFAProofState.Proved) then {
                dfaProofStates(processID) = DFAProofState.Unknown
                for i <- 0 until nbProcesses do {
                    if dfaVerifier.proofSkeleton.processDependencies(i).contains(processID) then {
                        invalidateDFAProofState(i)
                    }
                }                
            }
        else {
            dfaProofStates(processID) = DFAProofState.Unknown
        }
    }

    /**
      * Check the premise for the DFA assumption of processID.
      *
      * @param processID
      */
    def checkDFAAssumption(processID : Int ) : Unit = {
        dfaVerifier.checkInductivePremise(processID) match {
            case None => 
                dfaProofStates(processID) = DFAProofState.PremiseSucceeded                
            case Some(cex) => 
                if dfaVerifier.checkCounterExample(cex) then 
                    dfaProofStates(processID) = DFAProofState.Disproved(cex)
                else  
                   dfaProofStates(processID) = DFAProofState.PremiseFailed(cex)
        }
        updateDFAProofStates()
    }
    /**
      * Discard all assumption DFAs but those with indices in fixedAssumptions, learn these automatically.
      *
      * @param proveGlobalProperty whether the global property is to be proved
      * @param fixedAssumptions process indices of assumptions that are not to be learned
      */
    def learnDFAAssumptions(proveGlobalProperty : Boolean = true, fixedAssumptions: List[Int] = List()) : String = {
        (0 until nbProcesses).toSet.diff(fixedAssumptions.toSet)
            .foreach(invalidateDFAProofState)
        try {
            dfaVerifier.learnAssumptions(proveGlobalProperty, fixedAssumptions) match {
                case AGResult.Success => 
                    (0 until nbProcesses).foreach(i => dfaProofStates(i) = DFAProofState.Proved)
                    if proveGlobalProperty then dfaPropertyProofState = DFAProofState.Proved
                    "Success"
                case AGResult.AssumptionViolation(i, cex) => 
                    dfaProofStates(i) = DFAProofState.Disproved(cex)
                    s"Assumption ${i} is violated by trace ${cex}"
                case AGResult.GlobalPropertyViolation(cex) => 
                    dfaPropertyProofState = DFAProofState.Disproved(cex)
                    s"Global property is violated by trace ${cex}"
                case _ => "Unknown result" // Un reachable
            }
        } catch {
            case _ : DFAUnsatisfiableConstraints => 
                "Assumptions cannot be learned due to unsatisfiable constraints"
        }
    }
    def checkDFAGlobalProperty(processID : Int ) : Unit = {
        dfaVerifier.checkFinalPremise() match {
            case None => dfaPropertyProofState = DFAProofState.Proved
            case Some(cex) => 
                dfaPropertyProofState = 
                    if dfaVerifier.checkCounterExample(cex) then 
                        DFAProofState.Disproved(cex)
                    else DFAProofState.PremiseFailed(cex)
        }
    }
    def checkLTLAssumption(processID : Int ) : Unit = {}
    def checkLTLProperty(processID : Int ) : Unit = {}

    /**
      * Set the assumption DFA of given process. Invalidates the proof for processID and all those that depend on it.
      *
      * @param processID
      * @param dlts
      */
    def setDFAAssumption(processID : Int, dlts : DLTS) : Unit = {
        dfaVerifier.setAssumption(processID, dlts)
        invalidateDFAProofState(processID)
    }
    // def setDFAAssumptionDependencies(processID : Int, deps : Set[Int]) : Unit = {
    //     dfaVerifier.proofSkeleton.setProcessDependencies(processID, deps)
    // }
    def setDFAGlobalProperty(dlts : DLTS) : Unit = {
        dfaPropertyProofState = DFAProofState.Unknown
        dfaVerifier.setGlobalProperty(dlts)
    }
    // def setDFAGlobalPropertyDependencies(deps : Set[Int]) : Unit = {
    //     dfaVerifier.proofSkeleton.setPropertyDependencies(deps)
    // }
    /**
      * Show the state of the proof
      */
    def show() : String = {
        val nbProcesses = filenames.size
        val processes = dfaVerifier.system.processes
        val sb = StringBuilder()        
        sb.append(s"System with ${nbProcesses} processes\n\n")
        for i <- 0 until nbProcesses do {
            sb.append(s"Process #${i} at ${filenames(i)}\n")
            sb.append(s"Name: ${processes(i).systemName}\nAlphabet: ${processes(i).alphabet}\n")
            proofMode match {
                case ProofMode.DFA => 
                    val assDFA = dfaVerifier.getAssumption(i)
                    sb.append(s"DFA Assumption ${assDFA.name} has alphabet: ${assDFA.alphabet}, and size: ${assDFA.dfa.size()}\n")
                    sb.append(s"DFA Proof depends on: ${dfaVerifier.proofSkeleton.processDependencies(i)}\n")
                    sb.append(s"DFA assumption Proved: ${this.dfaProofStates(i)}\n")                    
                case ProofMode.LTL => 
                    sb.append(s"LTL Assumption ${ltlVerifier.getAssumption(i)}\n")
                    sb.append(s"LTL assumption Proved: ${this.ltlProofStates(i)}\n")
            }
            sb.append("\n")
        }
        if proofMode == ProofMode.DFA then 
            sb.append(s"DFA Proof's topological order: ${dfaVerifier.proofSkeleton.getTopologicalOrder()}\n\n")
        sb.toString()
    }
}
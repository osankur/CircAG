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
    var dfaVerifier = DFAAutomaticVerifier(files.toArray, dfaProperty)
    var ltlVerifier = LTLVerifier(files.toArray, ltlProperty)

    private var dfaProofStates = Buffer.fill(nbProcesses)(DFAProofState.Unknown)
    private var ltlProofStates = Buffer.fill(nbProcesses)(LTLProofState.Unknown)

    def getDFAProofState(processID : Int ) : DFAProofState = dfaProofStates(processID)
    def getLTLProofState(processID : Int ) : LTLProofState = ltlProofStates(processID)

    def reset() : Unit = {}

    def setProofMode(mode : ProofMode) : Unit = {
        proofMode = mode
    }

    def setDFAProperty(dfaProperty : Option[DLTS]) : Unit = {
        this.dfaProperty = dfaProperty
        dfaVerifier = DFAAutomaticVerifier(files.toArray, dfaProperty)
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
      * Check the premise for the DFA assumption of processID, and set the DFA proof state.
      *
      * @param processID
      */
    def checkDFAAssumption(processID : Int ) : Unit = {
        dfaVerifier.checkInductivePremise(processID) match {
            case None => 
                dfaProofStates(processID) = DFAProofState.PremiseSucceeded                
            case Some(cex) => 
                dfaProofStates(processID) = DFAProofState.PremiseFailed(cex)
        }
        updateDFAProofStates()
    }
    def checkDFAProperty(processID : Int ) : Unit = {}
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
    def setDFAAssumptionDependencies(processID : Int, deps : Set[Int]) : Unit = {
        dfaVerifier.proofSkeleton.setProcessDependencies(processID, deps)
    }
    def setDFAPropertyDependencies(deps : Set[Int]) : Unit = {
        dfaVerifier.proofSkeleton.setPropertyDependencies(deps)
    }
    /**
      * Show the state of the proof
      */
    def show() : String = {
        val nbProcesses = filenames.size
        val processes = dfaVerifier.processes
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
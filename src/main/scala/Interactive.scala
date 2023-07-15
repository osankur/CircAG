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
            case DFAProofState.Proved => s"\u2713"
            case DFAProofState.Disproved(cex) => s"X (${cex})"
        }
    }
    case Proved, Unknown
    case Disproved(cex : Trace)

enum LTLProofState:
    override def toString() : String = {
        this match {
            case LTLProofState.Unknown => s"?"
            case LTLProofState.Proved => s"\u2713"
            case LTLProofState.Disproved(cex) => s"X (${cex})"
        }
    }
    case Proved, Unknown
    case Disproved(cex : Lasso)


class Interactive(
    val filenames : List[String], 
    private var dfaProperty : Option[DLTS] = None, 
    private var ltlProperty : LTL = LTLTrue()
    )
{

    val files = filenames.map(s => java.io.File(s))
    val nbProcesses = files.size
    files.foreach(f=> if !f.exists() then throw Exception(s"File ${f} could not be read"))
    var dfaVerifier = DFAAutomaticVerifier(files.toArray, dfaProperty)
    var ltlVerifier = LTLVerifier(files.toArray, ltlProperty)

    private var dfaProofStates = Buffer.fill(nbProcesses)(DFAProofState.Unknown)
    private var ltlProofStates = Buffer.fill(nbProcesses)(LTLProofState.Unknown)

    def reset() : Unit = {}

    def setDFAProperty(dfaProperty : Option[DLTS]) : Unit = {
        this.dfaProperty = dfaProperty
        dfaVerifier = DFAAutomaticVerifier(files.toArray, dfaProperty)
    }

    def setLTLProperty(ltlProperty : LTL) : Unit = {
        this.ltlProperty = ltlProperty
        var ltlVerifier = LTLVerifier(files.toArray, ltlProperty)
    }

    def checkDFAAssumption(processID : Int ) : Unit = {}
    def checkDFAProperty(processID : Int ) : Unit = {}
    def checkLTLAssumption(processID : Int ) : Unit = {}
    def checkLTLProperty(processID : Int ) : Unit = {}

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
            val assDFA = dfaVerifier.getAssumption(i)
            sb.append(s"DFA Assumption ${assDFA.name} has alphabet: ${assDFA.alphabet}, and size: ${assDFA.dfa.size()}\n")
            sb.append(s"DFA assumption Proved: ${this.dfaProofStates(i)}\n")
            sb.append(s"LTL Assumption ${ltlVerifier.getAssumption(i)}\n")
            sb.append(s"LTL assumption Proved: ${this.ltlProofStates(i)}\n")
            sb.append("\n")
        }
        sb.toString()
    }
}
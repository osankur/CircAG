package fr.irisa.circag
import java.io.File

import fr.irisa.circag.dfa._
import fr.irisa.circag.ltl._

object Interactive {
    var files : Array[java.io.File] = Array()
    var dfaVerifier = DFAAutomaticVerifier(Array(), None)
    var ltlProperty : LTL = LTLTrue()
    var ltlVerifier = LTLVerifier(Array(), ltlProperty)
    var dfaProperty = DLTS.fromErrorSymbol("_")

    def reset() : Unit = {

    }
    def readProcesses(filenames : Array[String]) : Unit = {
        reset()
        files = filenames.map(s => java.io.File(s))
        files.foreach(f=> if !f.exists() then throw Exception(s"File ${f} could not be read"))
        dfaVerifier = DFAAutomaticVerifier(files, None)
        ltlVerifier = LTLVerifier(Array(), ltlProperty)
    }

    def setDFAProperty(dfaProperty : DLTS) : Unit = {
        this.dfaProperty = dfaProperty
        dfaVerifier = DFAAutomaticVerifier(files, Some(dfaProperty))
    }

    def setLTLProperty(ltlProperty : LTL) : Unit = {
        this.ltlProperty = ltlProperty
    }

    /**
      * Show the state of the proof
      */
    def show() : Unit = {

    }
}
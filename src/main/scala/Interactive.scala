package fr.irisa.circag
import java.io.File

import fr.irisa.circag.dfa._

object Interactive {
    var files : Array[java.io.File] = Array()
    var dfaVerifier = DFAAutomaticVerifier(Array(), "")
    def reset() : Unit = {

    }
    def readProcesses(filenames : Array[String]) : Unit = {
        reset()
        files = filenames.map(s => java.io.File(s))
        files.foreach(f=> if !f.exists() then throw Exception(s"File ${f} could not be read"))
    }

    /**
      * Show the state of the proof
      */
    def show() : Unit = {

    }
}
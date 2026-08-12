package fr.irisa.circag.configuration


import java.io.File
import java.nio.file._

import collection.mutable.Buffer
import fr.irisa.circag.Trace
import fr.irisa.circag.dfa.DFALearningAlgorithm
import fr.irisa.circag.dfa.ConstraintStrategy
case class ParseError(msg: String) extends Exception(msg)

enum ProcessFormat:
  case TCheckerTA

case class Configuration(
    cmd : String = "",
    ltsFiles : Array[File] = Array[File](),
    err: List[String] = List(),
    ltlProperty : Option[String] = None,
    processFormat: ProcessFormat = ProcessFormat.TCheckerTA,
    keepTmpFiles: Boolean = true,
    verbose: Boolean = false,
    verbose_MembershipQueries : Boolean = false,
    tmpDirPath : Path = Files.createTempDirectory("circag"),
    dumpAssumptions : Boolean = false,
    visualizeAssumptions : Boolean = false,
    alphabetRefinement : Boolean = false,
    dfaLearningAlgorithm : DFALearningAlgorithm = DFALearningAlgorithm.RPNI,
    constraintStrategy : ConstraintStrategy = ConstraintStrategy.Eager,
    reachModelChecker : String = findExecutable("tck-reach"),
    livenessModelChecker : String = findExecutable("tck-liveness"),
    randomSeed : Int = 0,
    maxDFASize : Int = 128
) {
}

var globalConfiguration = Configuration()

def set(c : Configuration) : Unit = {
  globalConfiguration = c
}

def get() : Configuration = {
  globalConfiguration
}

def findExecutable(executableName: String): String = {
    val executablePath = s"lib/$executableName"
    if (new File(executablePath).exists()) {
      executablePath
    } else {
      val whereisResult = sys.process.Process(s"whereis $executableName").!!.trim
      if (whereisResult.nonEmpty) {
        whereisResult.split(" ")(0)
      } else {
        throw new Exception(s"$executableName executable not found")
      }
    }
  }
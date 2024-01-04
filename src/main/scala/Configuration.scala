package fr.irisa.circag.configuration


import java.io.File
import java.nio.file._
import collection.mutable.Buffer
import fr.irisa.circag.Trace
import fr.irisa.circag.dfa.DFALearningAlgorithm
import fr.irisa.circag.dfa.ConstraintStrategy
case class ParseError(msg: String) extends Exception(msg)

object FSM {
  enum FSMFormat:
    case SMV, AIG, Murphi, TCheckerTA, Verilog

  sealed trait ModelChecker
  case object TCheckerModelChecker extends ModelChecker {
    override def toString: String = "tck-reach"
  }
}

case class Configuration(
    cmd : String = "",
    ltsFiles : Array[File] = Array[File](),
    err: String = "",
    ltlProperty : Option[String] = None,
    ltsFormat: FSM.FSMFormat = FSM.FSMFormat.TCheckerTA,
    keepTmpFiles: Boolean = true,
    verbose: Boolean = false,
    verbose_MembershipQueries : Boolean = false,
    tmpDirName: String = "/tmp/circag",
    dumpAssumptions : Boolean = false,
    alphabetRefinement : Boolean = false,
    dfaLearningAlgorithm : DFALearningAlgorithm = DFALearningAlgorithm.RPNI,
    constraintStrategy : ConstraintStrategy = ConstraintStrategy.Eager,
    randomSeed : Int = 0
) {
  private var tmpDirPath: Option[Path] = None
  def getTmpDirPath(): Path = {
    tmpDirPath match {
      case None =>
        val p = FileSystems.getDefault().getPath(tmpDirName);
        p.toFile().mkdirs()
        for(file <- p.toFile().listFiles()){
          if (!file.isDirectory()) 
            file.delete()
        }
        tmpDirPath = Some(p)
        p
      case Some(f) => f
    }
  }
}

var globalConfiguration = Configuration()

def set(c : Configuration) : Unit = {
  globalConfiguration = c
}

def get() : Configuration = {
  globalConfiguration
}
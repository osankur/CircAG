package fr.irisa.circag.configuration


import java.io.File
import java.nio.file._
import collection.mutable.Buffer
import fr.irisa.circag.Trace
import fr.irisa.circag.tchecker.dfa.AssumptionGeneratorType
case class ParseError(msg: String) extends Exception(msg)

var g1 = false
val cex = Buffer.tabulate(4)({_ => Set[Trace]()})

def resetCEX() : Unit = {
  for i <- 0 until cex.size do {
    cex(i) = Set[Trace]()
  }
}

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
    ltsFormat: FSM.FSMFormat = FSM.FSMFormat.TCheckerTA,
    keepTmpFiles: Boolean = true,
    verbose: Boolean = false,
    verbose_MembershipQueries : Boolean = false,
    tmpDirName: String = "/tmp/circag",
    visualizeDFA : Boolean = false,
    alphabetRefinement : Boolean = true,
    learnerType : AssumptionGeneratorType = AssumptionGeneratorType.RPNI,
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
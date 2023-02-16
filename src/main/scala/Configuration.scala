package fr.irisa.circag.configuration


import java.io.File
import java.nio.file._

case class ParseError(msg: String) extends Exception(msg)

object FSM {
  sealed trait FSMFormat
  case object SMV extends FSMFormat
  case object AIG extends FSMFormat
  case object Murphi extends FSMFormat
  case object TCheckerTA extends FSMFormat
  case object Verilog extends FSMFormat

  sealed trait ModelChecker
  case object TCheckerModelChecker extends ModelChecker {
    override def toString: String = "tck-reach"
  }
}

case class Configuration(
    ltsFiles : Array[File] = Array[File](),
    err: String = "",
    ltsFormat: FSM.FSMFormat = FSM.TCheckerTA,
    keepTmpFiles: Boolean = false,
    verbose: Boolean = false,
    verbose_MembershipQueries : Boolean = false,
    tmpDirName: String = ".tmp/",
    visualizeDFA : Boolean = false
) {
  private var tmpDirFile: Option[File] = None
  def tmpDirPath(): File = {
    tmpDirFile match {
      case None =>
        val tmpDirPath = FileSystems.getDefault().getPath(tmpDirName);
        tmpDirPath.toFile().mkdirs()
        for(file <- tmpDirPath.toFile().listFiles()){
          if (!file.isDirectory()) 
            file.delete()
        }
        tmpDirFile = Some(tmpDirPath.toFile())
        tmpDirPath.toFile()
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
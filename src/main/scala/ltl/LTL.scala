package fr.irisa.circag.tchecker.ltl

import org.slf4j.Logger
import org.slf4j.LoggerFactory
import java.nio.file._
import scala.sys.process._

class MalformedLTL(msg : String) extends Exception(msg)

abstract class LTL {
    def isUniversal : Boolean = false
}
class LTLTrue extends LTL {
    override def toString() = "1"
}
class LTLFalse extends LTL {
    override def toString() = "0"
}
case class G(subformula : LTL) extends LTL{
    override def isUniversal = true
    override def toString() = {
        s"(G ${subformula.toString()})"
    }
}
case class X(subformula : LTL) extends LTL{
    override def toString() = {
        s"(X ${subformula.toString()})"
    }
}
case class F(subformula : LTL) extends LTL {
    override def toString() = {
        s"(F ${subformula.toString()})"
    }
}
case class U(left : LTL, right : LTL) extends LTL {
    override def toString() = {
        s"(${left.toString()} U ${right.toString()})"
    }
}
case class W(left : LTL, right : LTL) extends LTL {
    override def toString() = {
        s"(${left.toString()} W ${right.toString()})"
    }
}
case class R(left : LTL, right : LTL) extends LTL {
    override def toString() = {
        s"(${left.toString()} R ${right.toString()})"
    }
}
case class M(left : LTL, right : LTL) extends LTL {
    override def toString() = {
        s"(${left.toString()} M ${right.toString()})"
    }
}
case class And(left : LTL, right : LTL) extends LTL {
    override def toString() = {
        s"(${left.toString()} & ${right.toString()})"
    }
}
case class Or(left : LTL, right : LTL) extends LTL {
    override def toString() = {
        s"(${left.toString()} | ${right.toString()})"
    }
}
case class Not(subformula : LTL) extends LTL {
    override def toString() = {
        s"(!${subformula.toString()})"
    }
}
case class Atomic(atom : String) extends LTL {
    override def toString() = atom
}

object LTL {
   private val logger = LoggerFactory.getLogger("CircAG")

   def fromSpot(ltlString : String) : LTL = {
    def printToFile(f: java.io.File)(op: java.io.PrintWriter => Unit) = {
      val p = new java.io.PrintWriter(f)
      try { op(p) } finally { p.close() }
    }    
    val tmpFile = Files.createTempFile("tmp", ".ltl").toFile()
    printToFile(tmpFile)({ (p : java.io.PrintWriter) => p.println(ltlString)})
    val output = StringBuffer()
    val proc = s"ltlfilt --lbt ${tmpFile.getAbsolutePath()}"
    if (proc run BasicIO(false,output,None)).exitValue != 0 then {
      throw (MalformedLTL(output.toString()))
    } else {
      LTL.fromLBT(output.toString())
    }
   }

   def fromLBT(lbtString : String) : LTL = {
        val atomPattern = "\"(.*)\"".r
        def parse(tokens : Seq[String]) : (LTL, Seq[String]) = {
            require(!tokens.isEmpty)
            tokens.head match {
                case "G" => 
                    val (f, tail) = parse(tokens.tail)
                    (G(f),tail)
                case "F" => 
                    val (f, tail) = parse(tokens.tail)
                    (F(f),tail)
                case "X" => 
                    val (f, tail) = parse(tokens.tail)
                    (X(f),tail)
                case "!" => 
                    val (f, tail) = parse(tokens.tail)
                    (Not(f),tail)
                case "U" => 
                    val (left, tail) = parse(tokens.tail)
                    val (right, tail_) = parse(tail)
                    (U(left, right),tail_)
                case "M" => 
                    val (left, tail) = parse(tokens.tail)
                    val (right, tail_) = parse(tail)
                    (M(left, right),tail_)
                case "R" => 
                    val (left, tail) = parse(tokens.tail)
                    val (right, tail_) = parse(tail)
                    (R(left, right),tail_)
                case "V" => 
                    val (left, tail) = parse(tokens.tail)
                    val (right, tail_) = parse(tail)
                    (R(left, right),tail_)
                case "W" => 
                    val (left, tail) = parse(tokens.tail)
                    val (right, tail_) = parse(tail)
                    (W(left, right),tail_)
                case "&" => 
                    val (left, tail) = parse(tokens.tail)
                    val (right, tail_) = parse(tail)
                    (And(left, right),tail_)
                case "|" => 
                    val (left, tail) = parse(tokens.tail)
                    val (right, tail_) = parse(tail)
                    (Or(left, right),tail_)
                case atomPattern(atom) => 
                    (Atomic(atom), tokens.tail)
                case unknownToken => 
                    throw MalformedLTL(unknownToken)
            }
        }
        val tokens = lbtString.trim().split("\\s+").map(_.trim)
        parse(tokens)._1
    }
}
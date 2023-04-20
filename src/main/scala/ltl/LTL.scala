package fr.irisa.circag.tchecker.ltl

import org.slf4j.Logger
import org.slf4j.LoggerFactory
import java.nio.file._
import scala.sys.process._
import fr.irisa.circag.{Alphabet, Trace}

class MalformedLTL(msg : String) extends Exception(msg)

abstract class LTL {
    def isUniversal : Boolean = false
    def alphabet : Alphabet 
}
class LTLTrue extends LTL {
    override def toString() = "1"
    override def alphabet = Set[String]()
}
class LTLFalse extends LTL {
    override def toString() = "0"
    override def alphabet = Set[String]()
}
case class G(subformula : LTL) extends LTL{
    override def isUniversal = true
    override def toString() = {
        s"(G ${subformula.toString()})"
    }
    override def alphabet = subformula.alphabet
}
case class X(subformula : LTL) extends LTL{
    override def toString() = {
        s"(X ${subformula.toString()})"
    }
    override def alphabet = subformula.alphabet 
}
case class F(subformula : LTL) extends LTL {
    override def toString() = {
        s"(F ${subformula.toString()})"
    }
    override def alphabet = subformula.alphabet
}
case class U(left : LTL, right : LTL) extends LTL {
    override def toString() = {
        s"(${left.toString()} U ${right.toString()})"
    }
    override def alphabet = left.alphabet | right.alphabet
}
case class W(left : LTL, right : LTL) extends LTL {
    override def toString() = {
        s"(${left.toString()} W ${right.toString()})"
    }
    override def alphabet = left.alphabet | right.alphabet

}
case class R(left : LTL, right : LTL) extends LTL {
    override def toString() = {
        s"(${left.toString()} R ${right.toString()})"
    }
    override def alphabet = left.alphabet | right.alphabet

}
case class M(left : LTL, right : LTL) extends LTL {
    override def toString() = {
        s"(${left.toString()} M ${right.toString()})"
    }
    override def alphabet = left.alphabet | right.alphabet
}
case class And(subformulas : List[LTL]) extends LTL {
    override def toString() = {
        if subformulas.size == 0 then "1"
        else s"(${subformulas.map(_.toString()).mkString(" & ")})"
    }
    override def alphabet = 
        subformulas.map(_.alphabet).foldLeft(Set[String]())({ (a,b) => a|b})

}
case class Or(subformulas : List[LTL]) extends LTL {
    override def toString() = {
        if subformulas.size == 0 then "0"
        else s"(${subformulas.map(_.toString()).mkString(" | ")})"
    }
    override def alphabet = 
        subformulas.map(_.alphabet).foldLeft(Set[String]())({ (a,b) => a|b})
}
case class Implies(left : LTL, right : LTL) extends LTL {
    override def toString() = {
        s"(${left.toString()} -> ${right.toString()})"
    }
    override def alphabet = left.alphabet | right.alphabet
}

case class Not(subformula : LTL) extends LTL {
    override def toString() = {
        s"!${subformula.toString()}"
    }
    override def alphabet = subformula.alphabet
}
case class Atomic(atom : String) extends LTL {
    override def toString() = atom
    override def alphabet = Set(atom)
}

object And {
    def apply(args : LTL*) : And = {
        And(args.toList)
    }
}

object Or {
    def apply(args : LTL*) : Or = {
        Or(args.toList)
    }
}

object LTL {
   private val logger = LoggerFactory.getLogger("CircAG")

   def fromString(ltlString : String) : LTL = {
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
                    (And(List(left, right)),tail_)
                case "|" => 
                    val (left, tail) = parse(tokens.tail)
                    val (right, tail_) = parse(tail)
                    (Or(List(left, right)),tail_)
                case "i" => 
                    val (left, tail) = parse(tokens.tail)
                    val (right, tail_) = parse(tail)
                    (Implies(left, right),tail_)
                case atomPattern(atom) => 
                    (Atomic(atom), tokens.tail)
                case unknownToken => 
                    throw MalformedLTL(s"Token ${unknownToken} inside ${lbtString}")
            }
        }
        val tokens = lbtString.trim().split("\\s+").map(_.trim)
        parse(tokens)._1
    }

    def asynchronousTransform(ltl : LTL, alphabet : Alphabet) : LTL = {
        val alphabetList = alphabet.toList
        val alpha = Or(alphabetList.map(Atomic(_)))
        val notAlpha = Not(alpha) 
        ltl match {
            case _ : LTLTrue => LTLTrue()
            case _ : LTLFalse => LTLFalse()
            case Atomic(atom) => 
                if alphabet.contains(atom) then 
                    U(notAlpha, Atomic(atom))
                else
                    throw MalformedLTL(s"Cannot apply asynchronous transformation to formula: Atom ${atom} does not belong to given alphabet ${alphabet}")
            case Not(phi) => Not(asynchronousTransform(phi, alphabet))
            case And(phis) => And(phis.map(asynchronousTransform(_, alphabet)))
            case Or(phis) => Or(phis.map(asynchronousTransform(_, alphabet)))
            case Implies(phi,psi) => Implies(asynchronousTransform(phi, alphabet), asynchronousTransform(psi, alphabet))
            case U(phi,psi) => U(Implies(alpha, asynchronousTransform(phi, alphabet)), And(List(alpha, asynchronousTransform(psi, alphabet))))
            case X(phi) => U(notAlpha, And(List(alpha, X(U(notAlpha, And(List(alpha, asynchronousTransform(phi, alphabet))))))))
            case F(phi) => F(And(List(alpha, asynchronousTransform(phi, alphabet))))
            case G(phi) => G(Implies(alpha, asynchronousTransform(phi, alphabet)))
            case op => throw Exception(s"asynchronousTransform: Operator ${op.getClass()} not supported")
        }
    }
}
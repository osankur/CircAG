package fr.irisa.circag.ltl

import org.slf4j.Logger
import org.slf4j.LoggerFactory
import java.nio.file._
import scala.sys.process._
import fr.irisa.circag.{Alphabet, Trace, Lasso, TA,DLTS}
import scala.collection.mutable.Map
class MalformedLTL(msg : String) extends Exception(msg)

abstract class LTL {
    def isUniversal : Boolean = false
    def getAlphabet : Alphabet 
    def accepts(lasso : Lasso) : Boolean = {
        val ta = TA.fromLTS(DLTS.fromLasso(lasso))
        ta.checkLTL(this) == None
    }
}
case class LTLTrue() extends LTL {
    override def toString() = "1"
    override def getAlphabet = Set[String]()
}
case class LTLFalse() extends LTL {
    override def toString() = "0"
    override def getAlphabet = Set[String]()
}
case class G(subformula : LTL) extends LTL{
    override def isUniversal = true
    override def toString() = {
        s"(G ${subformula.toString()})"
    }
    override def getAlphabet = subformula.getAlphabet
}
case class X(subformula : LTL) extends LTL{
    override def toString() = {
        s"(X ${subformula.toString()})"
    }
    override def getAlphabet = subformula.getAlphabet 
}
case class F(subformula : LTL) extends LTL {
    override def toString() = {
        s"(F ${subformula.toString()})"
    }
    override def getAlphabet = subformula.getAlphabet
}
case class U(left : LTL, right : LTL) extends LTL {
    override def toString() = {
        s"(${left.toString()} U ${right.toString()})"
    }
    override def getAlphabet = left.getAlphabet | right.getAlphabet
}
case class W(left : LTL, right : LTL) extends LTL {
    override def toString() = {
        s"(${left.toString()} W ${right.toString()})"
    }
    override def getAlphabet = left.getAlphabet | right.getAlphabet

}
case class R(left : LTL, right : LTL) extends LTL {
    override def toString() = {
        s"(${left.toString()} R ${right.toString()})"
    }
    override def getAlphabet = left.getAlphabet | right.getAlphabet

}
case class M(left : LTL, right : LTL) extends LTL {
    override def toString() = {
        s"(${left.toString()} M ${right.toString()})"
    }
    override def getAlphabet = left.getAlphabet | right.getAlphabet
}
case class And(subformulas : List[LTL]) extends LTL {
    override def toString() = {
        if subformulas.size == 0 then "1"
        else s"(${subformulas.map(_.toString()).mkString(" & ")})"
    }
    override def getAlphabet = 
        subformulas.map(_.getAlphabet).foldLeft(Set[String]())({ (a,b) => a|b})

}
case class Or(subformulas : List[LTL]) extends LTL {
    override def toString() = {
        if subformulas.size == 0 then "0"
        else s"(${subformulas.map(_.toString()).mkString(" | ")})"
    }
    override def getAlphabet = 
        subformulas.map(_.getAlphabet).foldLeft(Set[String]())({ (a,b) => a|b})
}
case class Implies(left : LTL, right : LTL) extends LTL {
    override def toString() = {
        s"(${left.toString()} -> ${right.toString()})"
    }
    override def getAlphabet = left.getAlphabet | right.getAlphabet
}

case class Not(subformula : LTL) extends LTL {
    override def toString() = {
        s"(!${subformula.toString()})"
    }
    override def getAlphabet = subformula.getAlphabet
}
case class Atomic(atom : String) extends LTL {
    override def toString() = atom
    override def getAlphabet = Set(atom)
}

object And {
    def apply(args : LTL*) : LTL = {
        if args.size == 0 then LTLTrue()
        else And(args.toList)
    }
}

object Or {
    def apply(args : LTL*) : LTL = {
        if args.size == 0 then LTLFalse()
        else Or(args.toList)
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
            case LTLTrue() => LTLTrue()
            case LTLFalse() => LTLFalse()
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

    def substitute(ltl : LTL, st : Map[String, String]) : LTL = {
        ltl match {
            case LTLTrue() => LTLTrue()
            case LTLFalse() => LTLFalse()
            case Atomic(atom) => 
                if st.contains(atom) then 
                    Atomic(st(atom))
                else
                    Atomic(atom)
            case Not(phi) => Not(substitute(phi, st))
            case And(phis) => And(phis.map(substitute(_, st)))
            case Or(phis) => Or(phis.map(substitute(_, st)))
            case Implies(phi,psi) => Implies(substitute(phi, st), substitute(psi, st))
            case U(phi,psi) => U(substitute(phi, st), substitute(psi, st))
            case X(phi) => X(substitute(phi, st))
            case F(phi) => F(substitute(phi, st))
            case G(phi) => G(substitute(phi, st))
            case op => throw Exception(s"substitute: Operator ${op.getClass()} not supported")
        }
    }
}
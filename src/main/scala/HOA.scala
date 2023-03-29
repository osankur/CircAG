package fr.irisa.circag

import scala.collection.mutable.Buffer
import scala.collection.mutable.HashMap
import scala.collection.mutable.ArrayBuffer
import scala.collection.immutable.Set
import collection.convert.ImplicitConversions._
import java.io.ByteArrayInputStream
import dk.brics.automaton
import net.automatalib.brics.BricsNFA
import net.automatalib.automata.fsa.MutableDFA
import net.automatalib.automata.fsa.DFA;
import net.automatalib.automata.fsa.impl.compact.CompactDFA;
import net.automatalib.automata.fsa.impl.FastDFA
import net.automatalib.automata.fsa.impl.FastNFA
import net.automatalib.automata.fsa.impl.FastDFAState
import net.automatalib.automata.fsa.impl.FastNFAState
import net.automatalib.util.automata.fsa.DFAs
import net.automatalib.util.automata.fsa.NFAs
import net.automatalib.automata.fsa.impl.compact.CompactDFA;
import net.automatalib.util.automata.builders.AutomatonBuilders;
import net.automatalib.visualization.Visualization;
import net.automatalib.words.Alphabet;
import net.automatalib.words.impl.Alphabets;

import jhoafparser.consumer.HOAConsumerPrint;
import jhoafparser.parser.HOAFParser;
import jhoafparser.parser.generated.ParseException;
import jhoafparser.consumer.HOAConsumerStore
import jhoafparser.ast.BooleanExpression
import jhoafparser.ast.AtomLabel
import jhoafparser.ast.AtomAcceptance

import com.microsoft.z3

import fr.irisa.circag.statistics
import fr.irisa.circag.configuration
import fr.irisa.circag.Trace
import fr.irisa.circag.{LTS,NLTS,DLTS}

object HOA {

    def toLTS(automatonString : String) : NLTS = {
        val toVars = HashMap[Int, z3.BoolExpr]()
        val toSymbol = HashMap[z3.BoolExpr, Int]()
        val ctx = {
            val cfg = HashMap[String, String]()
            cfg.put("model", "true")
            z3.Context(cfg);
        }
        val solver = ctx.mkSolver()
        def varOfSymbol(symbol : Int) : z3.BoolExpr = {
            if toVars.contains(symbol) then {
                toVars(symbol)
            } else {
                val v = ctx.mkBoolConst(ctx.mkSymbol(symbol))
                toVars.put(symbol, v)
                toSymbol.put(v, symbol)
                v
            }
        }
        def toZ3(expr : BooleanExpression[AtomLabel]) : z3.BoolExpr = {
            expr.getType() match {
                case BooleanExpression.Type.EXP_TRUE => ctx.mkTrue()
                case BooleanExpression.Type.EXP_FALSE => ctx.mkFalse()
                case BooleanExpression.Type.EXP_ATOM => 
                    varOfSymbol(expr.getAtom().getAPIndex())
                case BooleanExpression.Type.EXP_AND => 
                    ctx.mkAnd(toZ3(expr.getLeft()), toZ3(expr.getRight()))
                case BooleanExpression.Type.EXP_OR => 
                    ctx.mkOr(toZ3(expr.getLeft()), toZ3(expr.getRight()))
                case BooleanExpression.Type.EXP_NOT => 
                    ctx.mkNot(toZ3(expr.getLeft()))
            }
        }
        // Register all APs and add pairwise disjointness constraint to solver
        def singletonValuations(expr : BooleanExpression[AtomLabel]) : Seq[Int] = {
            var constraints = toZ3(expr)
            var labels = Buffer[Int]()
            solver.push()
            solver.add(constraints)
            for (sigma, v) <- toVars do {
                solver.push()
                solver.add(v)
                if solver.check() == z3.Status.SATISFIABLE then {
                    labels.append(sigma)
                }
                solver.pop()
            }
            solver.pop()
            labels.toSeq
        }
        val autFactory = HOAConsumerStore()
        HOAFParser.parseHOA(new ByteArrayInputStream(automatonString.getBytes()), autFactory);
        val aut = autFactory.getStoredAutomaton()
        val header = aut.getStoredHeader()        
        if(aut.hasEdgesImplicit()) then {
            throw Exception("Implicit edges are not accepted")
        }
        if(aut.hasUniversalBranching()) then {
            throw Exception("Universal branching is not accepted")
        }
        val accCondition = header.getAcceptanceCondition()
        if(accCondition.getType() != BooleanExpression.Type.EXP_ATOM ) then {
            throw Exception("Only Buchi acceptance is accepted")
        }
        if(accCondition.getAtom().getType() != AtomAcceptance.Type.TEMPORAL_INF) then{
            throw Exception("Only Buchi acceptance is accepted")
        }
        val alphabet = header.getAPs().toBuffer
        for (sigma,i) <- alphabet.zipWithIndex do {
            // System.out.println(s"Symbol ${sigma} ")
            varOfSymbol(i)
        }
        for a <- 0 until header.getAPs().size
            b <- 0 until header.getAPs().size do {
                if a != b then {
                    solver.add(ctx.mkAnd(ctx.mkNot(ctx.mkAnd(toVars(a), toVars(b)))))
                }
            }
        val nfa = FastNFA(Alphabets.fromList(header.getAPs()))
        // System.out.println(dfa.getInputAlphabet())
        val newStates = Buffer[FastNFAState]()
        for i <- 1 to aut.getNumberOfStates() do {
            newStates.append(nfa.addState())
        }
        header.getStartStates().foreach(_.foreach({ i => nfa.setInitial(newStates(i), true) }))
        for (s,i) <- newStates.zipWithIndex do {
            if(aut.getStoredState(i).getAccSignature() != null) then
                nfa.setAccepting(s, true)
            for edge <- aut.getEdgesWithLabel(i) do {
                assert(edge.getConjSuccessors().size == 1)
                val succ = edge.getConjSuccessors().head
                val labels = singletonValuations(edge.getLabelExpr())
                // System.out.println(s"${s} -> $succ: ${labels}")
                for sigma <- labels do {
                    nfa.addTransition(s, alphabet(sigma).toString, newStates(succ))
                }
            }
        }
        val nlts = NLTS("_hoa_", nfa, alphabet.map(_.toString).toSet)
        if header.getName() != null then 
            nlts.comments = header.getName()
        nlts
    }  
}
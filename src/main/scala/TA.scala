package fr.irisa.circag
import org.slf4j.Logger
import org.slf4j.LoggerFactory
import io.AnsiColor._
import scala.util.boundary, boundary.break

import collection.JavaConverters._
import collection.convert.ImplicitConversions._
import scala.collection.mutable.ArrayBuffer
import scala.collection.mutable.ListBuffer
import scala.collection.mutable.Buffer
import scala.collection.immutable.Set
import scala.collection.mutable
import scala.sys.process._
import scala.io
import scala.collection.mutable.StringBuilder
import scala.collection.mutable.HashMap

import java.io.File
import java.io.InputStream
import java.nio.file._
import java.io.PrintWriter
import java.io.ByteArrayInputStream

import net.automatalib.automata.Automaton
import net.automatalib.automata.fsa.FiniteStateAcceptor
import net.automatalib.automata.fsa.impl.{FastDFA, FastNFA, FastDFAState, FastNFAState}
import net.automatalib.words.impl.Alphabets;

import fr.irisa.circag._
import fr.irisa.circag.ltl.LTL

case class BadTimedAutomaton(msg: String) extends Exception(msg)
case class FailedTAModelChecking(msg: String) extends Exception(msg)

/** 
  * Timed automaton representing a process.
  * Light weight representation storing the tuple 
  * (events, eventsOfProcesses, core, syncs) where 
  * - events is the list of all events,
  * - eventsOfProcesses maps process names to events that they include, 
  * - core is the list of lines of the input file except for the system name, events, and sync instructions,
  * - syncs contains lists of tuples encoding the syncs
  */
class TA (
  var systemName : String = "",
  var alphabet: Set[String] = Set(),
  var internalAlphabet: Set[String] = Set(),
  var core: String = "",
  var eventsOfProcesses : HashMap[String, Set[String]] = HashMap[String, Set[String]](),
  var syncs : List[List[(String, String)]] = List[List[(String, String)]]()){

  def getProcessNames() : List[String] = {
    eventsOfProcesses.keys().toList
  }

  override def toString(): String = {
    val sb = StringBuilder()
    sb.append("# alphabet:\n")
    sb.append(s"system:${systemName}\n\n")
    for sigma <- alphabet do {
      sb.append(s"event:${sigma}\n")
    }
    sb.append("# Internal alphabet:\n")
    for sigma <- internalAlphabet do {
      sb.append(s"event:${sigma}\n")
    }
    sb.append("\n")
    sb.append(core)
    for sync <- syncs do {
      sb.append("sync:" + sync.map(_ + "@" + _).mkString(":") + "\n")
    }
    sb.toString()
  }

  /**
   * Check the reachability of a state labeled by label. Return such a trace if any.
   * 
   * @param label
   */
  def checkReachability(label : String) : Option[Trace] = {
    val beginTime = System.nanoTime()    
    statistics.Counters.incrementCounter("model-checking")
    val modelFile =
      Files.createTempFile(configuration.get().tmpDirPath, "circag-query", ".tck").toFile()
    val pw = PrintWriter(modelFile)
    pw.write(this.toString())
    pw.close()

    val certFile =
      Files.createTempFile(configuration.get().tmpDirPath, "circag-cert", ".cert").toFile()
    val cmd = "tck-reach -a reach %s -l %s -C symbolic -o %s"
            .format(modelFile.toString, label, certFile.toString)

    TA.logger.debug(s"${BLUE}${cmd}${RESET}")
    // System.out.println(cmd)

    val output = cmd.!!
    val cex = scala.io.Source.fromFile(certFile).getLines().toList

    if (!configuration.globalConfiguration.keepTmpFiles){
      modelFile.delete()
      certFile.delete()
    }    
    statistics.Timers.incrementTimer("tchecker", System.nanoTime() - beginTime)
    if (output.contains("REACHABLE false")) then {
      None
    } else if (output.contains("REACHABLE true")) then {
      Some(TA.getTraceFromCounterExampleOutput(cex, this.alphabet))
    } else {
      throw FailedTAModelChecking(output)
    }
  }

  /**
    * Check whether trace|_alph is accepted by ta|_alph where alph is syncAlphabet (default is trace.toSet)
    *
    * @param trace a trace
    * @param syncAlphabet synchronization alphabet for the synchronous product. Default is trace.toSet.
    * @return None if no such execution exists, and Some(trace) otherwise.
    */
  def checkTraceMembership(trace : Trace, syncAlphabet : Option[Set[String]] = None) : Option[Trace] = {  
    statistics.Counters.incrementCounter("trace-membership")
    val syncAlpha = syncAlphabet.getOrElse(trace.toSet)
    // We project trace to syncAlpha because we want to create a process with a given alphabet (there cannot be letters outside of its alphabet)
    val projTrace = trace.filter(syncAlpha.contains(_))
    val traceProcess = DLTS.fromTrace(projTrace, Some(syncAlpha))
    val productTA = TA.synchronousProduct(this, List(traceProcess), Some("_accept_"))
    val result = productTA.checkReachability(s"${traceProcess.name}_accept_")
    result
  }

    /**
    * Check whether lasso|_alph is accepted by ta|_alph where alph is syncAlphabet (default is lasso.toSet)
    * @param lasso a lasso
    * @param syncAlphabet synchronization alphabet for the synchronous product. Default is lasso.toSet.
    * @pre the projection of lasso to syncAlphabet is infinite
    * @return None if no such execution exists, and Some(lasso) otherwise.
    */
  def checkLassoMembership(lasso : Lasso, syncAlphabet : Option[Set[String]] = None) : Option[Lasso] = {  
    statistics.Counters.incrementCounter("lasso-membership")
    val occurringSymbols = lasso._1.toSet ++ lasso._2.toSet
    val lassoAlphabet = syncAlphabet.getOrElse(occurringSymbols) | occurringSymbols
    require(!(lasso._2.toSet & lassoAlphabet).isEmpty)
    val lassoNLTS = NLTS.fromDLTS(DLTS.fromLasso(lasso,Some(lassoAlphabet)))
    val productTA = this.buchiIntersection(lassoNLTS, "_accept_")
    val result = productTA.checkBuchi(s"${lassoNLTS.name}_accept_")
    result
  }

  /**
    * Compute TA with a Buchi acceptance condition which recognizes the intersection of lts and this.
    * 
    * Because the model checker is base on accepting states and not accepting labels, we need to make sure
    * to exclude inf runs in which the lts stays forever in an accepting state (and not take any transition).
    * This the case e.g. if the lts is a^\omega an if the other process reads, say, \tau^\omega.
    * To do this, 
    * 1. we extend the alphabet of LTS to include all non-sync labels of TA;
    * 2. add a fresh dummy state D for each accepting state AC of LTS
    * 3. all sync labels from the D has the same effect as from AC
    * 4. all non-sync labels go from AC to D
    * 5. there are self-loops on all non-sync labels at all states but accepting states
    * 
    * @param lts
    * @param acceptingLabelSuffix
    * @return
    */
  def buchiIntersection(lts : NLTS, acceptingLabelSuffix : String) : TA = {
    val syncAlphabet = lts.alphabet & this.alphabet
    val nonSyncAlpha = (this.internalAlphabet | this.alphabet).diff(syncAlphabet) // internal alphabet of ta
    val fullAlphabet = (lts.alphabet | this.internalAlphabet | this.alphabet)
    // Make a copy of the NLTS; add dummy state and self-loops
    val statesMap = HashMap[FastNFAState,FastNFAState]()
    val dummyStatesMap = HashMap[FastNFAState,FastNFAState]()
    val newNFA = new FastNFA(Alphabets.fromList((fullAlphabet).toList))
    val dfa = lts.dfa
    lts.dfa.getStates()
      .foreach({ state =>
        val newstate = newNFA.addState(dfa.isAccepting(state))
        statesMap.put(state, newstate)
        if dfa.isAccepting(state) then    {
          dummyStatesMap.put(newstate, newNFA.addState(false))
        }
      })
    lts.dfa.getInitialStates().foreach(
      s => newNFA.setInitial(statesMap(s), true)
    )
    dfa
      .getStates()
      .foreach(
        { s =>
          for a <- lts.alphabet do {
            dfa
              .getSuccessors(s, a)
              .foreach(
                { snext =>
                  newNFA.addTransition(statesMap(s), a, statesMap(snext))
                  if (dfa.isAccepting(s)) then {
                    newNFA.addTransition(dummyStatesMap(statesMap(s)), a, statesMap(snext))
                  }
                }
              )
          }
        }
      )
    // add trans from accepting states to their dummy states
    newNFA.getStates().foreach(
      s =>
        if newNFA.isAccepting(s) then {
          for a <- nonSyncAlpha do {
            newNFA.addTransition(s, a, dummyStatesMap(s))
          }
        } else {
          for a <- nonSyncAlpha do {
            newNFA.addTransition(s, a, s)
          }
        }
    )
    val newNLTS = NLTS(lts.name, newNFA, fullAlphabet)
    TA.synchronousProduct(this, List(newNLTS),Some(acceptingLabelSuffix),syncOnInternalEvents=true)
  }
  /**
  * Check whether alpha*.(lasso|_alph) has non-empty intersection with ta|_alph where alph is syncAlphabet (default is lasso.toSet)
  * @param lasso a lasso
  * @param syncAlphabet synchronization alphabet for the synchronous product. Default is lasso.toSet.
  * @pre the projection of lasso to syncAlphabet is infinite
  * @return None if no such execution exists, and Some(lasso) otherwise.
  */
  def checkLassoSuffixMembership(lasso : Lasso, syncAlphabet : Option[Set[String]] = None) : Option[Lasso] = {  
    statistics.Counters.incrementCounter("lasso-suffix-membership")
    val lassoAlphabet = syncAlphabet.getOrElse(lasso._1.toSet ++ lasso._2.toSet)
    val projLasso = lasso.filter(lassoAlphabet.contains(_))
    val lassoProcess = NLTS.fromLassoAsSuffix(projLasso, Some(lassoAlphabet))
    val productTA = this.buchiIntersection(lassoProcess, "_accept_")
    val result = productTA.checkBuchi(s"${lassoProcess.name}_accept_")
    TA.logger.debug(s"checkLassoSuffixMembership: whether ${lasso} can be read in process ${systemName} *as a suffix* with sync alphabet ${lassoAlphabet}: ${result != None}")
    result
  }

  /**
    * Check whether all infinite runs of the TA satisfy the LTL formula.
    *
    * @param ltlFormula
    * @return None if the formula is satisfied, and a counterexample lasso violating the formula otherwise.
    */
  def checkLTL(ltlFormula: LTL): Option[Lasso] = {
    val accLabel = "_ltl_accept_"
    val fullAlphabet = this.alphabet | ltlFormula.getAlphabet
    val ltlNLTS = NLTS.fromLTL(ltl.Not(ltlFormula).toString(), Some(fullAlphabet))
    val productTA = this.buchiIntersection(ltlNLTS,accLabel)
    val r = productTA.checkBuchi(s"${ltlNLTS.name}${accLabel}")
    r
  }

  /** Check the existence of a lasso with infinitely many label. 
    *
    * @param ta process
    * @param label label to be seen infinitely often
    * @return None if the process has no lasso satisfying GF label, and otherwise Some(lasso) that is a witness.
    */
  def checkBuchi(label: String): Option[Lasso] = {
    val beginTime = System.nanoTime()
    statistics.Counters.incrementCounter("model-checking")
    val modelFile =
      Files
        .createTempFile(
          configuration.get().tmpDirPath,
          "circag-query",
          ".tck"
        )
        .toFile()
    val pw = PrintWriter(modelFile)
    pw.write(this.toString())
    pw.close()

    val certFile =
      Files
        .createTempFile(
          configuration.get().tmpDirPath,
          "circag-cert",
          ".cert"
        )
        .toFile()
    // val cmd = "tck-liveness -a ndfs %s -C symbolic -l %s -o %s"
    val cmd = "tck-liveness -a couvscc %s -C symbolic -l %s -o %s"
      .format(modelFile.toString, label, certFile.toString)
    TA.logger.debug(s"${BLUE}${cmd}${RESET}")

    val output = cmd.!!
    val cex = scala.io.Source.fromFile(certFile).getLines().toList

    if (!configuration.globalConfiguration.keepTmpFiles) {
      modelFile.delete()
      certFile.delete()
    }


    statistics.Timers.incrementTimer("tchecker", System.nanoTime() - beginTime)
    if (output.contains("CYCLE false")) then {
      None
    } else if (output.contains("CYCLE true")) then {
      Some(TA.getLassoFromCounterExampleOutput(cex, this.alphabet))
    } else {
      throw FailedTAModelChecking(output)
    }
  }

}

object TA{
  protected val logger = LoggerFactory.getLogger("CircAG")

  /** 
   * Parser that reads TChecker TA format. 
   */
  def fromFile(inputFile: java.io.File) : TA = {
    val ta = TA()
    val lines = scala.io.Source.fromFile(inputFile).getLines().toList
    val regEvent = "\\s*event:([^ ]*).*".r
    val regSync = "\\s*sync:(.*)\\s*".r
    val regProcess = "\\s*process:(.*)\\s*".r
    val regEdge = "\\s*edge:[^:]*:[^:]*:[^:]*:([^{]*).*".r
    val regSystem = "\\s*system:([^ ]*).*".r
    // System.out.println("File: " + inputFile.toString)
    ta.alphabet = lines.flatMap({
      case regEvent(event) if !event.startsWith("_") => Some(event.strip())
      case _               => None
    }).toSet
    ta.internalAlphabet = lines.flatMap({
      case regEvent(event) if event.startsWith("_") => Some(event.strip())
      case _               => None
    }).toSet
    ta.syncs = lines.flatMap({
      case regSync(syncs) =>
        Some(
          syncs
            .split(":")
            .toList
            .map(
              { l =>
                val elts = l.split("@").map(_.strip()).toArray
                (elts(0), elts(1))
              }
            )
        )
      case _ => None
    })

    ta.eventsOfProcesses = HashMap[String, Set[String]]()
    var currentProcess = ""
    lines.foreach {
      case regProcess(monitorProcessName) =>
        currentProcess = monitorProcessName
        ta.eventsOfProcesses += (monitorProcessName -> Set[String]())
      // System.out.println("Now reading process: " + monitorProcessName)
      case regEdge(sync) =>
        ta.eventsOfProcesses.put(currentProcess,
          (ta.eventsOfProcesses(currentProcess) + sync))
      // System.out.println("Adding sync: " + sync)
      case _ => ()
    }
    ta.core = lines.filter({
      case regSystem(name) => ta.systemName = name; false
      case regEvent(event) => false
      case regSync(event) => false
      case _               => true
    }).mkString("\n")
    val nbProcesses = ta.eventsOfProcesses.keys().size
    if nbProcesses > 1 then {
      throw BadTimedAutomaton("Timed automata can only have a single process")
    } else if nbProcesses == 0 then {
      throw BadTimedAutomaton("Timed automata must have at least one process")
    }
    return ta
  }

  /**
   * Build a TA object that represents the given LTS.
   */
  def fromLTS[S](dlts : LTS[S], acceptingLabelSuffix : Option[String] = None) : TA = {
    val ta = TA(dlts.name, dlts.alphabet.toSet)
    ta.eventsOfProcesses += (dlts.name -> ta.alphabet )
    val strStates = StringBuilder()  
    val strTransitions = StringBuilder()
    val initStates = dlts.dfa.getInitialStates().asScala
    strStates.append("process:" + dlts.name + "\n")
    dlts.dfa
      .getStates()
      .asScala
      .foreach(state =>
        {
          strStates
            .append("location:%s:q%s{".format(dlts.name, state.toString))
          val attributes = ArrayBuffer[String]()
          if (initStates.contains(state)) then {
            attributes.append("initial:")
          }
          if (dlts.dfa.isAccepting(state)) {
            acceptingLabelSuffix match {
              case Some(l) => attributes.append(s"labels:${dlts.name + l}")
              case _ => ()
            }
          }
          strStates.append(attributes.mkString(":"))
          strStates.append("}\n")
          for (sigma <- ta.alphabet) {
            val succs = dlts.dfa.getSuccessors(state, sigma);
            if (!succs.isEmpty()) then {
              for (succ <- succs) {
                strTransitions.append(
                  "edge:%s:q%s:q%s:%s\n".format(
                    dlts.name,
                    state.toString,
                    succ.toString,
                    sigma
                  )
                )
              }
            }
          }
        }
      )
      // If there is no accepting states, add a dummy accepting state
      if !dlts.dfa.getStates().exists({s => dlts.dfa.isAccepting(s)}) then {
        acceptingLabelSuffix match {
          case Some(l) =>
            strStates
              .append(s"location:${dlts.name}:_dummy_state_{labels:${dlts.name + l}}\n")
          case _ => ()
        }        
      }
      val taB = StringBuilder()
      if dlts.comments != "" then {
        dlts.comments.split("\n").foreach({ x => taB.append(s"# ${x}")})
      }
      taB.append(ta.core)
      taB.append("\n")
      taB.append(strStates.append(strTransitions.toString).toString)
    ta.core = taB.toString()
    ta
  }

  /**
   * Build TA from the NLTS corresponding to the Buchi automaton given in the HOA format.
   * @param automatonString the Buchi automaton description in the HOA format
   * @param fullAlphabet if not None, an alphabet containing all symbols that appear in automatonString
   * @param acceptingLabel if not None, the label of the accepting states in the produced TA
   */
  def fromHOA(automatonString : String, fullAlphabet : Option[Alphabet], acceptingLabel : Option[String]) : TA = {
    TA.fromLTS[FastNFAState](NLTS.fromHOA(automatonString, fullAlphabet), acceptingLabel)
  }

  /**
   * Build a TA representing an NBA that recognizes the given LTL formula.
   */
  def fromLTL(ltlString : String, fullAlphabet : Option[Alphabet], acceptingLabel : Option[String] ) : TA = {
    val nlts = NLTS.fromLTL(ltlString, fullAlphabet)
    this.fromLTS[FastNFAState](nlts, acceptingLabel)
  }
  def fromLTL(ltl : LTL, fullAlphabet : Option[Alphabet], acceptingLabel : Option[String]) : TA = {
    fromLTL(ltl.toString, fullAlphabet, acceptingLabel)
  }

  /**
    * @param ta timed automaton
    * @param dlts list of DLTSs with which sync product is to be computed
    * @param acceptingLabelSuffix if Some(suffix), then accepting states of each LTS are labeled by name_suffix.
    * @param syncOnInternalEvents whether to sync on events that are internal to ta as well
    * @pre ta.systemName and dlts.name's are pairwise distinct
    * @return Product of ta and the given DLTS
    */
  def synchronousProduct[S](ta : TA, dlts : List[LTS[S]], acceptingLabelSuffix : Option[String] = None, syncOnInternalEvents : Boolean = false) : TA = {
    val allNames = dlts.map(_.name) ++ ta.eventsOfProcesses.keys().toList
    if allNames.size > allNames.distinct.size then {
      throw Exception("Attempting synchronous product of processes of the same name")
    }
    val dltsTA = dlts.map({d => TA.fromLTS[S](d, acceptingLabelSuffix)})
    val jointAlphabet = 
      ta.alphabet
      // union of alphabets of the LTSs
      | dlts.foldLeft(Set[String]())( (alph, d) => alph | d.alphabet)
      // internal events
      | (if syncOnInternalEvents then {
          ta.internalAlphabet
        } else {
          Set()
        })
    val sb = StringBuilder()
    val systemName = s"_premise_${ta.systemName}"
    sb.append(ta.core)
    dltsTA.foreach({d => sb.append(d.core); sb.append("\n")})
    val eventsOfProcesses = HashMap[String,Set[String]]()
    dlts.foreach({d => eventsOfProcesses += (d.name -> d.alphabet.toSet)})
    ta.eventsOfProcesses.foreach({(p,e) => eventsOfProcesses += (p -> e)})
    val allProcesses = eventsOfProcesses.keys.toList
    val syncs = jointAlphabet.map(
      sigma => ta::dltsTA flatMap { ta => 
          if ta.alphabet.contains(sigma) || syncOnInternalEvents && ta.internalAlphabet.contains(sigma) then
            Some((ta.getProcessNames().head, sigma))
          else None
        }
    ).toList.filter(_.size > 1)
    TA(systemName, jointAlphabet, ta.internalAlphabet.diff(jointAlphabet), sb.toString(), eventsOfProcesses, syncs)
  }
  
  /**
    * Synchronous product of the given processes.
    * 
    * @param tas pocesses whose product is to be taken
    * @pre The TAs must have distinct process and variable names.
    * @pre Each TA has a single process
    * @return product TA
    */
  def synchronousProduct(tas : List[TA]) : TA = {
    require(tas.size > 0)
    require(tas.forall(p => p.eventsOfProcesses.keys().size == 1))
    def unionOfList[A](l : List[Set[A]]) : Set[A] = {
      l.foldLeft(Set[A]())({(a,b) => a | b})
    }
    // println("Product of:")
    // tas.foreach(ta => println(s"${ta.systemName} on alphabet ${ta.alphabet}"))
    val allProcesses = unionOfList(tas.map(_.eventsOfProcesses.keys().toSet)).toList
    val processCount = (tas.map(_.eventsOfProcesses.keys().size)).sum
    if allProcesses.size < processCount then {
      throw Exception("Attempted synchronous product of processes of the same name")
    }
    val jointAlphabet = tas.foldLeft(Set[String]())((alph,ta) => alph | ta.alphabet)
    val jointInternalAlphabet = tas.foldLeft(Set[String]())((alph,ta) => alph | ta.internalAlphabet)

    val eventsOfProcesses = HashMap[String,Set[String]]()
    val sb = StringBuilder()
    val systemName = s"_product_"
    tas.foreach({d => sb.append(d.core); sb.append("\n")})
    tas.foreach({_.eventsOfProcesses.foreach({(p,e) => eventsOfProcesses.put(p, e)})})
    val syncs = jointAlphabet.map(
      sigma => tas flatMap { ta => 
            if !ta.alphabet.contains(sigma) then None
            else Some((ta.getProcessNames().head, sigma))
        }
    ).toList.filter(_.size > 1)
    TA(systemName, jointAlphabet, jointInternalAlphabet, sb.toString(), eventsOfProcesses, syncs)
  }

  /**
   * Parser for TChecker counterexamples in which each state has a single succesor (trace, or lasso).
   * @return (states,edges) a map pair where states maps each integer node identifier to its fields 
   * (final, initial, intval, labels, vloc, zone) as a single string,
   * and edges maps each node to a pair of label and successor node identifier
   */
  def getGraphFromCounterExampleOutput(cexDescription : List[String], events : Set[String]) : (HashMap[Int, String],HashMap[Int,(String,Int)]) = {
      val states = HashMap[Int, String]() // state names
      val edges = HashMap[Int,(String,Int)]()
      val regEdge = "\\s*([0-9]+)\\s*->\\s*([0-9]+).*vedge=\"<(.*)>\".*".r
      val regState = "\\s*([0-9]+)\\s*\\[(.*)\\]\\s*".r
      cexDescription.foreach({
        case regState(i, content) => 
          // content contains the following attributes: final, initial, intval, labels, vloc, zone
          // println(s"Read state $i with content: $content")
          states.put(i.toInt, content)
        case regEdge(src,tgt,syncList) => 
          val singleSync = syncList.split(",").map(_.split("@")(1)).toSet//.intersect(events)
          if (singleSync.size == 1){
            val a = singleSync.toArray
            // word.append(a(0))
            edges.put(src.trim.toInt, (a(0), tgt.trim.toInt))
            // parents.put(tgt.trim.toInt, src.trim.toInt)
            // println(s"Added ${(tgt.trim.toInt, src.trim.toInt)}")
            // println(s"parents: ${parents}")
          } else if (singleSync.size > 1){
            throw FailedTAModelChecking("The counterexample trace has a transition with syncs containing more than one letter of the alphabet:\n" + syncList)
          } else {
            // Ignore internal transition
          }
        case line => //println(s"Ignoring line ${line}")
      })
      (states,edges)
  }
  /** 
   *  Given the counterexample description output by TChecker, given as a list of lines,
   *  return the trace, that is, the sequence of events in the alphabet encoded by the said counterexample.
   */
  def getTraceFromCounterExampleOutput(cexDescription : List[String], events : Set[String]) : Trace = {
      val word = ListBuffer[String]()
      val parents = HashMap[Int,Int]()
      val (nodes,edges) = getGraphFromCounterExampleOutput(cexDescription : List[String], events : Set[String])
      edges.foreachEntry{case (s,(sigma,t)) => 
        assert(!parents.contains(t))
        parents.put(t,s)
      }
      if edges.size > 0 then {
        val root =
            var node = parents.keys().nextElement()
            while ( parents.contains(node)) do {
              node = parents(node)
            }
            node
        var node = root
        while( edges.contains(node)) do {
          val (sigma, next) = edges(node)
          word.append(sigma)
          node = next
        }
      }
      word.toList.filter(events.contains(_))
  }


  /** Simplify the lasso by rendering the prefix simple and taking shortcuts 
  * @post modifies the maps
  * @returns new root and beginning of cycle node identifiers
  */
  private def simplifyLassoGraph(states : HashMap[Int, String], edges : HashMap[Int,(String,Int)], root : Int, beginCycle : Int ) : (Int,Int) = {
    var newRoot = root
    var newBeginCycle = beginCycle
    /* Check if some state in the cycle already appears in the prefix; if yes shortcut */
    def shortcutToCycle() : Unit = {
      var node = root
      var prevNode = node
      while( node != newBeginCycle) do {
        // check if label of node appears in the cycle
        boundary {
          var cnode = newBeginCycle
          if states(cnode) == states(node) then
            // println(s"\tDetected that $node == $cnode")
            if prevNode == node then
              // the first state of the prefix is in the cycle: set the newRoot to cnode
              newRoot = cnode
            else 
              // redirect prevNode to cnode instead of node
              edges.put(prevNode, (edges(prevNode)._1, cnode))
              // cnode == newBeginCycle remains the beginning of the cycle
            break()
          cnode = edges(cnode)._2
          while (cnode != newBeginCycle) do {
            if states(cnode) == states(node) then
              if prevNode == node then
                newRoot = cnode
              else 
                // redirect prevNode to cnode instead of node
                edges.put(prevNode, (edges(prevNode)._1, cnode))
                // define cnode as the beginning of the cycle
                newBeginCycle = cnode
              break()
            cnode = edges(cnode)._2
          }
        }
        prevNode = node 
        node = edges(node)._2
      }
    }
    /* remove cycles within the prefix */
    def shortcutWithinPrefix() : Unit = {
      // node which is to be tested
      var sourceNode = newRoot
      // predecessor of the said node
      var prevSourceNode = newRoot 
      // if any, a copy of sourceNode occurring in the prefix, at the right of sourceNode
      var copyNode : Option[Int] = None
      while (sourceNode != newBeginCycle) do {
        var node = edges(sourceNode)._2
        while (node != newBeginCycle) do {
          if ( states(node) == states(sourceNode) ) then {
            copyNode = Some(node)
          }
          node = edges(node)._2
        }
        copyNode match {
          case None => () // no copy, do nothing
          case Some(j) => 
            if prevSourceNode == sourceNode then
              newRoot = j
            else 
              // redirect the edge to node to j
              edges.put(prevSourceNode, (edges(prevSourceNode)._1, j))
        }
        prevSourceNode = sourceNode
        sourceNode = edges(sourceNode)._2
      }
    }
    shortcutToCycle()
    shortcutWithinPrefix()
    (newRoot, newBeginCycle)
  }

  /** 
   *  Given the counterexample description output by TChecker, given as a list of lines,
   *  return the trace, that is, the sequence of events in the alphabet encoded by the said counterexample.
   */
  def getLassoFromCounterExampleOutput(cexDescription : List[String], events : Set[String]) : Lasso = {
    val (states,edges) = getGraphFromCounterExampleOutput(cexDescription : List[String], events : Set[String])
    var root = -1
    var beginCycle = -1

    val prefix = ListBuffer[String]()
    val cycle = ListBuffer[String]()
    var indegree = HashMap[Int,Int]()
    edges.foreachEntry{
      case(s,(sigma,t)) => 
        indegree.put(t, indegree.getOrElse(t,0)+1)
        indegree.put(s, indegree.getOrElse(s,0))
    }
    if edges.size > 0 then {
      indegree.foreachEntry({
        (s,ind) => if ind == 0 then root = s
        else if ind == 2 then beginCycle = s 
        else if ind != 1 then throw Exception("Some node has indegree 3 or more")
      })
      // If there is no node with indegree 0, then the lasso is a cycle without a stem
      if root == -1 then {        
        root = indegree.keys().nextElement()
        beginCycle = root
      }
      // simplify the graph
      simplifyLassoGraph(states, edges, root, beginCycle) match {
        case (x,y) =>
          root = x
          beginCycle = y
      }
      var node = root
      var atPrefix = true
      // Iterate forward from root, stop at beginCycle unless this is the first time we are seeing it (atPrefix)
      while( edges.contains(node) && (node != beginCycle || atPrefix)) do {
        if node == beginCycle then {
          atPrefix = false
        }
        val (sigma, next) = edges(node)
        if atPrefix then 
          prefix.append(sigma)
        else 
          cycle.append(sigma)
        node = next
      }
    }
    (prefix.toList, cycle.toList)
  }
}

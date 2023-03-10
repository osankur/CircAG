package fr.irisa.circag.statistics
import collection.mutable.HashMap
var posQueries = Set[String]()
var negQueries = Set[String]()
var lastTrace : List[String] = null
var rpniTime : Long = 0
var z3Time : Long = 0
var liftingTime : Long = 0
var syncProductTime : Long = 0


object Timers {
    val timer = HashMap[String,Long]().withDefaultValue(0)

    def incrementTimer(timerName : String, value : Long) : Unit = {
        timer.put(timerName, value + timer.getOrElse[Long](timerName, 0))
    }
    def apply(counterName : String ) : Long = {
        timer.getOrElse(counterName, 0)
    }
    override def toString : String = {
        timer.map({(k,value) => s"${k}:${value/1e9d}"}).toString()
    }
}
object Counters {
    var counter = Map[String,Int]().withDefaultValue(0)

    def incrementCounter(counterName : String) : Unit = {
        counter += counterName -> (counter.getOrElse(counterName, 0) + 1)
    }
    def get(counterName : String) : Int = {
        counter.get(counterName) match {
            case None => 0
            case Some(x) => x
        }
    }
    def apply(counterName : String ) : Int = {
        counter.getOrElse(counterName, 0)
    }
    override def toString : String = {
        counter.toString
    }
}
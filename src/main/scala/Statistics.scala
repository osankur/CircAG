package fr.irisa.circag.statistics

var posQueries = Set[String]()
var negQueries = Set[String]()
var lastTrace : List[String] = null

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
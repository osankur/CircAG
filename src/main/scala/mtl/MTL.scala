package fr.irisa.circag.ltl

import org.slf4j.Logger
import org.slf4j.LoggerFactory
import java.nio.file._
import scala.sys.process._
import fr.irisa.circag.{Alphabet, Trace}

abstract class MTL extends LTL
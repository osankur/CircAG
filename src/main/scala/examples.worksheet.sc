import java.io.File
import fr.irisa.circag._
import fr.irisa.circag.ltl._

val tas = Array(File("examples/ltl-toy1/a.ta"), File("examples/ltl-toy1/b.ta"))
val checker = LTLAssumeGuaranteeVerifier(tas, G(F(Atomic("a"))))
checker.setAssumption(0, G(LTLTrue()))
checker.setAssumption(1, G(LTLTrue()))
checker.proofSkeleton.setProcessInstantaneousDependencies(0, Set(1))
assert(checker.checkFinalPremise() != None)

val ass0 = LTL.fromString("G (( b-> X a) & (c -> !F b))")
val ass1 = LTL.fromString("G (( d-> X b) & F(c | d) & (c -> ! F c))")
val ta0 = TA.fromFile(File("examples/ltl-toy1/a.ta"))
ta0.checkLTL(ass0)
checker.setAssumption(0, ass0)
checker.setAssumption(1, ass1)
// assert(checker.checkInductivePremise(0, false) == None)
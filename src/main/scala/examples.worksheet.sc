import java.io.File
import fr.irisa.circag.dfa._
import fr.irisa.circag._
import fr.irisa.circag.ltl._

val tas = Array(File("examples/ltl-toy1/a.ta"), File("examples/ltl-toy1/b.ta"))
val checker = LTLVerifier(tas, G(F(Atomic("a"))))
checker.setAssumption(0, G(LTLTrue()))
checker.setAssumption(1, G(LTLTrue()))
checker.proofSkeleton.setProcessInstantaneousDependencies(0, Set(1))
checker.checkFinalPremise()

val ass0 = LTL.fromString("G (( b-> X a) & (c -> !F b))")
val ass1 = LTL.fromString("G (( d-> X b) & F(c | d) & (c -> ! F c))")
val ta0 = TA.fromFile(File("examples/ltl-toy1/a.ta"))
ta0.checkLTL(ass0)
checker.setAssumption(0, ass0)
checker.setAssumption(1, ass1)
// assert(checker.checkInductivePremise(0, false) == None)


val filenames = Array("examples/seq-toy/lts0.ta", "examples/seq-toy/lts1.ta", "examples/seq-toy/lts2.ta", "examples/seq-toy/lts3.ta")
val int = Interactive(filenames.toList)
val nbProcesses = filenames.size
for i <- 0 until nbProcesses do {
    int.setDFAAssumption(i, DLTS.fromTChecker(File(filenames(i))))
}
int.setDFAAssumptionDependencies(0,Set[Int]())
int.setDFAAssumptionDependencies(1,Set(2))
int.setDFAAssumptionDependencies(2, Set(1,0))
int.setDFAAssumptionDependencies(3, Set(1))
int.show()
int.checkDFAAssumption(0)
int.checkDFAAssumption(1)
int.show()
int.setDFAAssumption(3, DLTS.fromTChecker(File(filenames(3))))
int.show()
int.checkDFAAssumption(0)
int.checkDFAAssumption(1)
int.checkDFAAssumption(2)
int.checkDFAAssumption(3)
int.show()
int.setDFAAssumption(2, DLTS.fromTChecker(File(filenames(2))))
int.show()
int.checkDFAAssumption(0)
int.checkDFAAssumption(1)
int.checkDFAAssumption(2)
int.checkDFAAssumption(3)
int.setDFAAssumption(2, DLTS.fromTChecker(File(filenames(2))))
int.show()
int.checkDFAAssumption(2)
int.show()

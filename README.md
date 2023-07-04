# Automatic Circular Assume Guarantee Model Checker

## Installation
You need
- Scala 3.1
- Java 1.7
- sbt 1.8
- maven
  
And the following must be on your path:
- [tchecker](https://github.com/ticktac-project/tchecker)
- [spot](https://spot.lre.epita.fr/)
 
Once you have all this, execute the following in `lib` directory

    mvn install:install-file -Dfile=jhoafparser-1.1.1.jar -DgroupId=jhoafparser -DartifactId=jhoafparser -Dversion=1.1.1 -Dpackaging=jar -DgeneratePom=true

and type

    sbt assembly

This should create the fat executable jar target/scala-3*/CircAG.jar.

## DFA-based N-way Assume-Guarantee Reasoning with Learning
The algorithm of the CAV16 paper is currently implemented with and without alphabet refinement. This can be tried as follows.

    java -jar target/scala-3.2.2/CircAG.jar dfa-aag --lts "examples/toy/lts1.ta,examples/toy/lts2.ta,examples/toy/lts3.ta" --err "err" --verbose false

Here, the list of automata are given wuth the option --lts: each file must contain a single process TChecker file (with or without clocks).
All variables and clocks must have distinct names. These processes synchronize on all declared events but those that start with _.
The --err option is used to pass the label that defines the safety property: AG!err.

The difference with CAV16 is that a SAT solver is used to compute a satisfying valuation to the constraints but then a separate passive learning algorithm (RPNI) is used to learn each assumption DFA separately.

You can specify the passive DFA learning algorithm using the option `--learnerType RPNI` or `--learnerType SAT`.

You can add the option `--visualizeDFA true` to see the assumption DFAs that were learned.

### Other examples
Two toy examples easy to understand:

    java -jar target/scala-3.2.2/CircAG.jar dfa-aag --lts "examples/toy/lts1.ta,examples/toy/lts2.ta,examples/toy/lts3.ta" --err "err" --verbose false --ar false
    java -jar target/scala-3.2.2/CircAG.jar dfa-aag --lts "examples/seq-toy/lts0.ta,examples/seq-toy/lts1.ta,examples/seq-toy/lts2.ta,examples/seq-toy/lts3.ta" --err "err" --ar false

To enable automatic alphabet refinement, use `--ar true`.

A small but less trivial example that does not currently terminate :(

    java -jar target/scala-3.2.2/CircAG.jar dfa-aag --lts "examples/ums/machine.ta,examples/ums/scheduler.ta,examples/ums/user.ta" --err "err" --ar false

## Utilities
The synchronized product of the processes can be output to stdout as a single TChecker file using

    run product --lts "examples/ums/machine.ta,examples/ums/scheduler.ta,examples/ums/user.ta"

## Jupyter Notebook
Install:

    pip3 install spylon-kernel
    python3 -m spylon_kernel install --user
    pip3 install pyspark
    jupyter notebook

## Debug level
Use the following property to set debug level to debug
    
     -Dorg.slf4j.simpleLogger.defaultLogLevel=debug

## Tasks
- Formalize the LTL AAG algorithm
- Formalize the MTL AAG algorithm
- Any other good passive learning algorithms for DFA?
- Implement one or several passive learning algorithms for LTL. The simplest one is based on SAT (see Neider et al.)
- Implement one or several passive learning algorithms for MTL.
- Understand why the above example does not terminate: do we really need to keep the alphabet very small?
- DFA case studies: reproduce CAV16 examples, and find a good one where our algorithm scales better.
- LTL case study: write a SDN case study with very simple assumption formulas but very large combined state space
- TChecker currently does not generate counterexamples for Buchi. Ask Frederic or do it yourself.
- Update LTL proof skeleton so that the proven DFA assumptions can be used in LTL/MTL proofs
- API for interactive / semi-atomated proof system
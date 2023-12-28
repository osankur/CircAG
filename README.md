# Automatic Circular Assume Guarantee Model Checker

## Installation
You need
- Some standard Linux or Mac operating system
- Scala 3.3
- Java 1.7
- sbt 1.8
- maven
  
And the executables of the following must be on your path:
- [tchecker](https://github.com/ticktac-project/tchecker)

  we use `tck-reach`, and `tck-liveness`
- [spot](https://spot.lre.epita.fr/)

  we use `ltlfilt` and `ltl2tgba`
 
Once you have all this, execute the following in `lib` directory. This installs the provided hoaf parser library into the maven repository.

    mvn install:install-file -Dfile=jhoafparser-1.1.1.jar -DgroupId=jhoafparser -DartifactId=jhoafparser -Dversion=1.1.1 -Dpackaging=jar -DgeneratePom=true

Then run the following in the main directory

    sbt assembly

This will create a fat executable jar target/scala-3*/CircAG.jar.

### Submodules: Samples2LTL and Scarlet
To check out and test the samples2LTL and Scarlet submodules, run:

    git submodule init
    git submodule update
    cd samples2ltl
    pip3 install -r requirements.txt
    python3 samples2LTL.py --sat --traces traces/alt.trace
    cd ../Scarlet
    pip3 install -r requirements.txt
    cd ..
    python3 -m Scarlet.ltllearner

## DFA-based Assume-Guarantee Reasoning with Learning
The algorithm of the CAV16 paper is currently implemented with and without alphabet refinement. This can be tried as follows.

    java -jar target/scala-3.3/CircAG.jar dfa-aag --lts "examples/toy/lts1.ta,examples/toy/lts2.ta,examples/toy/lts3.ta" --err "err" --verbose false

Here, the list of automata are given wuth the option --lts: each file must contain a single process TChecker file (with or without clocks).
All variables and clocks must have distinct names. These processes synchronize on all declared events but those that start with _.
The --err option is used to pass the label that defines the safety property: AG!err.

The difference with CAV16 is that a SAT solver is used to compute a satisfying valuation to the constraints but then a separate passive learning algorithm (RPNI) is used to learn each assumption DFA separately.

You can specify the passive DFA learning algorithm using the option `--dfaLearningAlgorithm RPNI` or `--dfaLearningAlgorithm SAT`.

You can add the option `--visualizeDFA true` to see the assumption DFAs that were learned.

### Other examples
Two toy examples easy to understand and another example with slightly larger automata and alphabets:

    java -jar target/scala-3.3.1/CircAG.jar dfa-aag --lts "examples/toy/lts1.ta,examples/toy/lts2.ta,examples/toy/lts3.ta" --err "err" --verbose false
    java -jar target/scala-3.3.1/CircAG.jar dfa-aag --lts "examples/seq-toy/lts0.ta,examples/seq-toy/lts1.ta,examples/seq-toy/lts2.ta,examples/seq-toy/lts3.ta" --err "err"
    java -jar target/scala-3.3.1/CircAG.jar dfa-aag --lts "examples/ums/machine.ta,examples/ums/scheduler.ta,examples/ums/user.ta" --err "err"

## LTL-based Assume-Guarantee Reasoning with Learning
We assume proof skeletons in which there is one big circular cluster, and possibly noncircular which point to each other (no cycle) and to the circular cluster.
Any process whose proof depends on the circular cluster is also considered to be circular.

## Utilities
The synchronized product of the processes can be output to stdout as a single TChecker file using

    run product --lts "examples/ums/machine.ta,examples/ums/scheduler.ta,examples/ums/user.ta"

## Scala3 Console
To use the API as an interactive proof system, you can use the Scala console:

    scala3 -cp target/scala-3.1.2/CircAG.jar -Dfile.encoding=UTF-8

Alternatively, just run `interactive.sh`.

## Debug level
Use the following property while running the jar to set debug level to debug
    
     -Dorg.slf4j.simpleLogger.defaultLogLevel=debug
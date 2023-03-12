## Automatic Circular Assume Guarantee Model Checker
You need 
- Scala 3.1
- Java 1.7
- sbt 1.8

You can use sbt to compile and run as shown below. To create a jar, run `sbt assembly`.

## DFA-based N-way Assume-Guarantee Reasoning with Learning
The algorithm of the CAV16 paper is currently implemented. This can be tried as follows.

    sbt run dfa-aag --lts "examples/ums/machine.ta,examples/ums/scheduler.ta,examples/ums/user.ta" --err "err" --ar false

Here, the list of automata are given wuth the option --lts: each file must contain a single process TChecker file (with or without clocks).
All variables and clocks must have distinct names. These processes synchronize on all declared events but those that start with _.
The --err option is used to pass the label that defines the safety property: AG!err.

The difference with CAV16 is that a SAT solver is used to compute a satisfying valuation to the constraints but then a separate passive learning algorithm (RPNI) is used to learn each assumption DFA separately.

You can add the option `visualizeDFA true` to see the assumption DFAs that were learned.
### Other examples
Two toy examples easy to understand:

    run dfa-aag --lts "examples/toy/lts1.ta,examples/toy/lts2.ta,examples/toy/lts3.ta" --err "err" --verbose true --ar false
    run dfa-aag --lts "examples/seq-toy/lts0.ta,examples/seq-toy/lts1.ta,examples/seq-toy/lts2.ta,examples/seq-toy/lts3.ta" --err "err" --ar false

To enable automatic alphabet refinement, use `--ar true`.

## Utilities
The synchronized product of the processes can be output to stdout as a single TChecker file using

    run product --lts "examples/ums/machine.ta,examples/ums/scheduler.ta,examples/ums/user.ta"

## Tasks
- Write TChecker script to decompose a given model into components as separate files. Here processes accessing the same shared variables must be kept together. The minimal alphabet must be inferred as well for all components.
- Write various assumption generators based on a SAT solver, passive algs from learnlib, minimal separating automata etc.
- Connect to spot for omega-regular properties
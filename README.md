# Automatic Circular Assume Guarantee Model Checker
This is an automatic assume-guarantee model checker using either DFA assumptions to check properties over finite traces or LTL assumptions
over infinite traces. Both algorithms are described in the following paper:

- Ocan Sankur. Automatic Assume-Guarantee Reasoning for Safety andLiveness Using Passive Learning. 2024.

The tool can be used in two modes. First, it offers a fully automatic algorithm which learns assumptions to apply the assume-guarantee rule and prove (or disprove) the desired property.
Moreover, the API can be used in the Scala console interactively to prove properties on systems with manually selected assumptions. It is also possible to specify some of the assumptions, and let the algorithm learn the rest of them.

The assume-guarantee proof rules were originally described in the following papers:

- Abd Elkader, Karam, Orna Grumberg, Corina S. Păsăreanu, and Sharon Shoham. "Automated circular assume-guarantee reasoning with n-way decomposition and alphabet refinement." In Computer Aided Verification: 28th International Conference, CAV 2016, Toronto, ON, Canada, July 17-23, 2016, Proceedings, Part I 28, pp. 329-351. Springer International Publishing, 2016.

- McMillan, Kenneth L. "A methodology for hardware verification using compositional model checking." Science of Computer Programming 37, no. 1-3 (2000): 279-309.

We currently use the model checker (TChecker)[https://github.com/ticktac-project/tchecker] for all model checking queries. This has the advantage of being open source, but also having a simple input format supporting synchronized products of labeled transition systems (which is required by the proof rules). However, it is easy to extend the tool to other model checkers. There are plans to do this in the future.
We use the [LearnLib](https://github.com/LearnLib/) for DFA learning and automata manipulation, and [Samples2LTL](https://github.com/ivan-gavran/samples2LTL)
for learning LTL formulas.

## Dependencies and Installation
You need
- Scala 3.3
- Java 1.7
- sbt 1.8
- maven
  
And the executables of the following must be on your path:
- [tchecker](https://github.com/ticktac-project/tchecker)

  we use `tck-reach`, and `tck-liveness`
- [spot](https://spot.lre.epita.fr/)

  we use `ltlfilt` and `ltl2tgba`

Other dependencies will be installed by sbt.

Once you have all this, execute the following in the `lib` directory. This installs the provided hoaf parser library into the maven repository.

    mvn install:install-file -Dfile=jhoafparser-1.1.1.jar -DgroupId=jhoafparser -DartifactId=jhoafparser -Dversion=1.1.1 -Dpackaging=jar -DgeneratePom=true

Then run the following in the main directory

    sbt assembly

This will create the executable jar `CircAG.jar`.

### Submodules
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


## License
This program is distributed under GNU GPL 3.0 (see [LICENSE](LICENSE)).

The current repository contains the binary `jhoafparser-1.1.1.jar` of the [Java parser for the HOA format](https://automata.tools/hoa/jhoafparser/) which is under GNU GPL 2.1.

## DFA-based Assume-Guarantee Reasoning with Learning
The DFA algorithm can be run as follows.

    java -jar CircAG.jar dfa --files "examples/toy/lts1.tck,examples/toy/lts2.tck,examples/toy/lts3.tck" --err "err" --verbose false

Here, the list of automata are given with the option --files: each file must contain a single process TChecker file (with or without clocks).
All variables and clocks must have distinct names. These processes synchronize on all declared events but those that start with _.
The --err option is used to pass the label that defines the safety property: AG!err.

A passive learning algorithm (RPNI or SAT) is used to learn assumption DFAs for each process separately. You can specify the passive DFA learning algorithm using the option `--dfaLearningAlgorithm RPNI` or `--dfaLearningAlgorithm SAT`. 
You can add the option `--visualizeDFA true` to see the assumption DFAs that were learned at the end of a successful verification.

### Other examples
    java -jar CircAG.jar dfa --files "examples/toy/lts1.tck,examples/toy/lts2.tck,examples/toy/lts3.tck" --err "err"
    java -jar CircAG.jar dfa --files "examples/seq-toy/lts0.tck,examples/seq-toy/lts1.tck,examples/seq-toy/lts2.tck,examples/seq-toy/lts3.tck" --err "err"
    java -jar CircAG.jar dfa --files "examples/ums-2/machine.tck,examples/ums-2/scheduler.tck,examples/ums-2/user.tck" --err "err"
    java -jar CircAG.jar dfa --files "examples/simple-sdn/device.tck,examples/simple-sdn/switch.tck,examples/simple-sdn/controller.tck,examples/simple-sdn/supervisor.tck,examples/simple-sdn/observer.tck" --err "err"
    java -jar CircAG.jar dfa --files "examples/sdn/device.tck,examples/sdn/switch.tck,examples/sdn/controller.tck,examples/sdn/supervisor.tck,examples/sdn/observer.tck" --err "err"
    java -jar CircAG.jar dfa --files "examples/ums-1/machine.tck,examples/ums-1/scheduler.tck,examples/ums-1/user.tck" --err "err"

## LTL-based Assume-Guarantee Reasoning with Learning
We assume proof skeletons in which there is one big circular cluster, and possibly noncircular which point to each other (no cycle) and to the circular cluster. Any process whose proof depends on the circular cluster is also considered to be circular.

In the command-line mode, a complete graph of dependencies is considered so that all processes are circular.

    java -jar CircAG.jar ltl --files "examples/muo/user.tck,examples/muo/machine.tck" --ltlProperty "G F cycle"
    java -jar CircAG.jar ltl --files "examples/ums-1/machine.tck,examples/ums-1/scheduler.tck,examples/ums-1/user.tck" --ltlProperty "G(start1 -> F end1)
    java -jar CircAG.jar ltl --files "examples/sdn/device.tck,examples/sdn/switch.tck,examples/sdn/controller.tck,examples/sdn/supervisor.tck,examples/sdn/observer.tck" --ltlProperty "G(ask -> F go)

## Utilities
The synchronized product of the processes can be output to stdout as a single TChecker file using

    java -jar CircAG.jar product --files "examples/ums/machine.tck,examples/ums/scheduler.tck,examples/ums/user.tck"

## Scala3 Console
To use the API as an interactive proof system, you can use the Scala console:

    scala3 -cp CircAG.jar -Dfile.encoding=UTF-8

Alternatively, just run `interactive.sh`.

## Debug level
Use the following property while running the jar to set debug level to debug
    
     -Dorg.slf4j.simpleLogger.defaultLogLevel=debug

# Author
Ocan Sankur 
learnerType=SAT
java -Dorg.slf4j.simpleLogger.defaultLogLevel=debug -jar target/scala-3.2.2/CircAG.jar dfa-aag --lts "examples/toy/lts1.ta,examples/toy/lts2.ta,examples/toy/lts3.ta" --err "err" --verbose true  --learnerType $learnerType --keepTmpFiles 
java -jar target/scala-3.2.2/CircAG.jar dfa-aag --lts "examples/seq-toy/lts0.ta,examples/seq-toy/lts1.ta,examples/seq-toy/lts2.ta,examples/seq-toy/lts3.ta" --err "err" --learnerType $learnerType

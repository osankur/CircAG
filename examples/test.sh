EXEC=../CircAG.jar
MEM_LIMIT=8g
TIME_LIMIT=7200
ulimit -t ${TIME_LIMIT} %-v ${MEM_LIMIT}
echo "Running tests with timeout=${TIME_LIMIT}s, memory: ${MEM_LIMIT}"
set -x
time java -Xmx"${MEM_LIMIT}" -jar $EXEC ltl --files "ums-1/user.tck,ums-1/scheduler.tck,ums-1/machine.tck" --ltlProperty "G(start1 -> F end1)"
time java -Xmx"${MEM_LIMIT}" -jar $EXEC ltl --files "ums-1/user.tck,ums-1/scheduler.tck,ums-1/machine.tck" --ltlProperty "F(rel1)"
time java -Xmx"${MEM_LIMIT}" -jar $EXEC ltl --files "sdn/device.tck,sdn/switch.tck,sdn/controller.tck,sdn/supervisor.tck,sdn/observer.tck" --ltlProperty "G(ask -> F go)"
time java -Xmx"${MEM_LIMIT}" -jar $EXEC ltl --files "sdn/device.tck,sdn/switch.tck,sdn/controller.tck,sdn/supervisor.tck,sdn/observer.tck" --ltlProperty "G(change -> F ack)"
time java -Xmx"${MEM_LIMIT}" -jar $EXEC ltl --files "sdn/device.tck,sdn/switch.tck,sdn/controller.tck,sdn/supervisor.tck,sdn/observer.tck" --ltlProperty "G F send"
time java -Xmx"${MEM_LIMIT}" -jar $EXEC ltl --files "ums-2/machine.tck,ums-2/scheduler.tck,ums-2/user.tck" --ltlProperty "G(start1 -> F end1)"
time java -Xmx"${MEM_LIMIT}" -jar $EXEC ltl --files "ums-2/machine.tck,ums-2/scheduler.tck,ums-2/user.tck" --ltlProperty "F(rel1)"
time java -Xmx"${MEM_LIMIT}" -jar $EXEC dfa --files "sdn/device.tck,sdn/switch.tck,sdn/controller.tck,sdn/supervisor.tck,sdn/observer.tck" --err "err"
time java -Xmx"${MEM_LIMIT}" -jar $EXEC dfa --files "ums-1/user.tck,ums-1/scheduler.tck,ums-1/machine.tck" --err "err"
time java -Xmx"${MEM_LIMIT}" -jar $EXEC dfa --files "ums-2/machine.tck,ums-2/scheduler.tck,ums-2/user.tck" --err "err"
---- MODULE progress_model_obe ----
EXTENDS Integers, Naturals, Sequences

CONSTANTS Threads


Instructions == {"Load", "Store", "Terminate"}

VARIABLES fairExecutionSet, checkLock, pc, instructions, terminated

vars == <<fairExecutionSet, checkLock, pc, instructions, terminated>>


InitThreadVars ==
    /\  pc = [t \in Threads |-> 1]
    /\  instructions = <<<< "Load", "Terminate">>, <<"Store", "Terminate">>>>
    /\  terminated = [t \in Threads |-> FALSE]

 Init == 
    /\  InitThreadVars
    /\  checkLock = FALSE \* initialize the lock to be unlocked
    /\  fairExecutionSet = {}


AddToFairExecutionSet(t) ==
    IF t \notin fairExecutionSet THEN
        /\  fairExecutionSet' = fairExecutionSet \union {t}
    ELSE
        /\  UNCHANGED fairExecutionSet


RemoveFromFairExecutionSet(t) ==
    IF t \in fairExecutionSet THEN
        /\  fairExecutionSet' = fairExecutionSet \ {t}
    ELSE
        /\  UNCHANGED fairExecutionSet



AtomicExchange(t, checkVal, jumpInst, doExch, exchVal) ==
    /\  LET newPc == IF checkLock = checkVal THEN jumpInst ELSE pc[t] + 1
            newCheckLock == IF doExch THEN exchVal ELSE checkLock
        IN
            /\ pc' = [pc EXCEPT ![t] = newPc]
            /\ checkLock' = newCheckLock

Step(t) ==
    /\  IF terminated[t] = FALSE THEN
            IF instructions[t][pc[t]] = "Load" THEN
                /\  AtomicExchange(t, FALSE, pc[t], FALSE, FALSE)
                /\  AddToFairExecutionSet(t)
                /\  UNCHANGED terminated
            ELSE IF instructions[t][pc[t]] = "Store" THEN
                /\  AtomicExchange(t, TRUE, pc[t] + 1, TRUE, TRUE)
                /\  AddToFairExecutionSet(t)
                /\  UNCHANGED terminated
            ELSE IF instructions[t][pc[t]] = "Terminate" THEN
                /\ RemoveFromFairExecutionSet(t)
                /\ terminated' = [terminated EXCEPT ![t] = TRUE]
                /\ UNCHANGED <<pc, checkLock>>
            ELSE
                /\ UNCHANGED vars
        ELSE 
            /\ UNCHANGED vars
    /\  UNCHANGED instructions





FairStep ==
    IF fairExecutionSet = {} THEN
        /\ \E t \in Threads:
            /\ Step(t)
    ELSE
        /\ \E t \in fairExecutionSet:
            /\ Step(t)

UnfairStep ==
    /\  \E t \in Threads:
        /\ Step(t)

\* Deadlock means reaching a state in which Next is not enabled.
Next == 
    \/ FairStep
    \*\/ UnfairStep

 EventuallyTerminated ==
     \A t \in Threads: []<>(terminated[t] = TRUE) \* always eventually all threads are terminated, which is not satisfied in this model



(* Specification *)
Spec == 
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next) \* Weak fairness guarnatees that if Next action are be enabled continuously(always enable), it would eventually happen 
    
Liveness == EventuallyTerminated

\* To sovle :
====

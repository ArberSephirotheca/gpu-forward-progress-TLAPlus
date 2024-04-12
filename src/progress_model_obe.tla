---- MODULE progress_model_obe ----
EXTENDS Integers, Naturals, Sequences

CONSTANT Threads

Instructions == {"Acquire", "Release", "Terminate"}

VARIABLES fairExecutionSet, checkLock, pc, instructions, terminated

vars == <<fairExecutionSet, checkLock, pc, instructions, terminated>>


InitThreadVars ==
    /\  pc = [t \in Threads |-> 1]
    /\  instructions = [t \in Threads |-> << "Acquire", "Release", "Terminate">>]
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
            IF instructions[t][pc[t]] = "Acquire" THEN
                /\  AtomicExchange(t, TRUE, 1, TRUE, TRUE)
                /\  AddToFairExecutionSet(t)
                /\  UNCHANGED terminated
            ELSE IF instructions[t][pc[t]] = "Release" THEN
                /\  AtomicExchange(t, FALSE, 3, TRUE, FALSE)
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
    /\ \E t \in fairExecutionSet:
        /\ Step(t)

UnfairStep ==
    /\  \E t \in Threads:
        /\ Step(t)

Next == 
    \/ FairStep
    \/ UnfairStep

\* EventuallyTerminated ==
\*     \A t \in Threads: <>[](terminated[t] = TRUE) \* eventually all threads are always terminated, which is not satisfied in this model



(* Specification *)
Spec == 
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next) \* Weak fairness guarnatees that the Next action will be enabled continuously
    /\ SF_vars(FairStep) \* Even the Fair Step is not continuously enabled, strong fairness guarnatees that it will be enabled infinitely often


\* To sovle :
====

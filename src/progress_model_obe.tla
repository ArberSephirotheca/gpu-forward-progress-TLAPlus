---- MODULE progress_model_obe ----
EXTENDS Integers, Naturals, Sequences

CONSTANT Threads

Instructions == {"Acquire", "Relese", "Terminate"}

VARIABLES fairExecutionSet, checkLock, pc, instructions, terminated

vars == <<fairExecutionSet, checkLock, pc, instructions, terminated>>


InitThreadVars ==
    /\  pc = [t \in Threads |-> 1]
    /\  instructions = [t \in Threads |-> << "Acquire", "Relese", "Terminate">>]
    /\  terminated = [t \in Threads |-> FALSE]

 Init == 
    /\  InitThreadVars
    /\  checkLock = FALSE \* initialize the lock to be unlocked
    /\  fairExecutionSet = {}


AddToFairExecutionSet(t) ==
    /\  t \in Threads
    /\  t \notin fairExecutionSet
    /\  fairExecutionSet' = fairExecutionSet \union {t}

RemoveFromFairExecutionSet(t) ==
    /\  t \in Threads
    /\  t \in fairExecutionSet
    /\  fairExecutionSet' = fairExecutionSet \ {t}


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
            ELSE IF instructions[t][pc[t]] = "Relese" THEN
                /\  AtomicExchange(t, FALSE, 3, TRUE, FALSE)
                /\  AddToFairExecutionSet(t)
                /\  UNCHANGED terminated
            ELSE IF instructions[t][pc[t]] = "Terminate" THEN
                /\ RemoveFromFairExecutionSet(t)
                /\ UNCHANGED <<pc, checkLock>>
            ELSE
                /\ UNCHANGED vars
        ELSE 
            /\ UNCHANGED vars
    /\  UNCHANGED instructions


\* RECURSIVE FairStepN(_, _)
\* FairStepN(n, t) ==
\*     /\  IF n = 0 THEN
\*             /\  UNCHANGED vars
\*         ELSE
\*             Step
FairStep ==
    /\  \E t \in fairExecutionSet:
        /\ Step(t)

UnfairStep ==
    /\  \E t \in Threads:
        /\ t \notin fairExecutionSet
        /\ Step(t)

Next == 
    \/ FairStep
    \/ UnfairStep

EventuallyTerminated ==
    \A t \in Threads: <>[](terminated[t] = TRUE) \* eventually all threads are always terminated, which is not satisfied in this model



(* Specification *)
Spec == 
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next) \* Weak fairness guarnatees that the Next action will be enabled continuously
    /\ SF_vars(FairStep) \* Even the Fair Step is not continuously enabled, strong fairness guarnatees that it will be enabled infinitely often

====

THEOREM 
---- MODULE MCProgressModel ----
EXTENDS Integers, Naturals, Sequences, MCThreads

VARIABLES fairExecutionSet

vars == <<fairExecutionSet, checkLock, pc, terminated, barrier>>

InitScheduler ==
    /\  fairExecutionSet = {}

Init ==
    /\  InitScheduler
    /\  InitThreads

UpdateFairExecutionSet(t) ==
    IF t \notin fairExecutionSet /\ terminated[t] = FALSE THEN
        /\  fairExecutionSet' = fairExecutionSet \union {t}
    ELSE IF t \in fairExecutionSet /\ terminated[t] = TRUE THEN
        /\  fairExecutionSet' = fairExecutionSet \ {t}
    ELSE
        /\  UNCHANGED fairExecutionSet


FairStep ==
    LET threadNotAtBarrier == {t \in fairExecutionSet: barrier[t] = "NULL"} \* threads in fair execution set that are not at barrier
        IN
        /\  IF threadNotAtBarrier = {} THEN \* all threads at fair execution set are at barrier, randomly select a thread that is not at barrier to step
                /\ \E t \in Threads:
                    /\  Step(t)
                    /\  UpdateFairExecutionSet(t)
            ELSE   
                /\ \E t \in threadNotAtBarrier:
                    /\  Step(t)
                    /\  UpdateFairExecutionSet(t)



\* Deadlock means reaching a state in which Next is not enabled.
Next ==
    /\  FairStep

 EventuallyTerminated ==
    \A t \in Threads: []<>(terminated[t] = TRUE) \* always eventually all threads are terminated



(* Specification *)
Spec == 
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next) \* Weak fairness guarnatees that if Next action are be enabled continuously(always enable), it would eventually happen 
    
Liveness == EventuallyTerminated
====

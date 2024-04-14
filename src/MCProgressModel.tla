---- MODULE MCProgressModel ----
EXTENDS Integers, Naturals, Sequences, MCThreads

VARIABLES fairExecutionSet


schedulerVars == <<fairExecutionSet>>

Init ==
    /\  fairExecutionSet = {}
    /\ InitThreads


UpdateFairExecutionSet(t) ==
    IF t \notin fairExecutionSet /\ terminated[t] = FALSE THEN
        /\  fairExecutionSet' = fairExecutionSet \union {t}
    ELSE IF t \in fairExecutionSet /\ terminated[t] = TRUE THEN
        /\  fairExecutionSet' = fairExecutionSet \ {t}
    ELSE
        /\  UNCHANGED fairExecutionSet


FairStep ==
    /\  IF fairExecutionSet = {} THEN
            /\ \E t \in Threads:
                /\  Step(t)
                /\  UpdateFairExecutionSet(t)
        ELSE
            /\ \E t \in fairExecutionSet:
                /\  Step(t)
                /\  UpdateFairExecutionSet(t)



\* Deadlock means reaching a state in which Next is not enabled.
Next ==
    /\  FairStep

 EventuallyTerminated ==
     \A t \in Threads: []<>(terminated[t] = TRUE) \* always eventually all threads are terminated, which is not satisfied in this model



(* Specification *)
Spec == 
    /\ Init
    /\ [][Next]_schedulerVars
    /\ WF_schedulerVars(Next) \* Weak fairness guarnatees that if Next action are be enabled continuously(always enable), it would eventually happen 
    
Liveness == EventuallyTerminated

====

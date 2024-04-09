---- MODULE GPUModule ----
EXTENDS Naturals, Sequences

CONSTANT ThreadIds, AXBInst

VARIABLES F, pc

(* Initialization of the variables *)
Init == 
    /\ F = {}
    /\ pc = "start"

(* Define the actions *)
Step(tid, axb) == 
    /\ pc = "start"
    /\ tid \in ThreadIds
    /\ axb \in AXBInst
    /\ F' = F \cup {tid}
    /\ pc' = "start"

Terminate(tid) == 
    /\ pc = "start"
    /\ tid \in ThreadIds
    /\ F' = F \ {tid}
    /\ pc' = "start"

(* Next action definition using non-deterministic choice *)
Next == 
    \/ \E tid \in ThreadIds, axb \in AXBInst : Step(tid, axb)
    \/ \E tid \in ThreadIds : Terminate(tid)

(* Specification *)
Spec == Init /\ [][Next]_<<F, pc>>

(* Add fairness conditions if necessary *)
Fairness == 
    /\ WF_<<F, pc>>(Step)
    /\ SF_<<F, pc>>(Terminate)

====

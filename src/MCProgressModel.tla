---- MODULE MCProgressModel ----
EXTENDS Integers, Naturals, Sequences, MCThreads, TLC

VARIABLES fairExecutionSet, selected

vars == <<fairExecutionSet, pc, state, selected, threadLocals, globalVars>>


InitOBE ==
    /\  fairExecutionSet = {} 
    /\  selected = -1

InitHSA ==
    /\  fairExecutionSet = {0}
    /\  selected = -1

InitScheduler ==
    /\  IF Scheduler = "OBE" THEN
            /\  InitOBE
        ELSE IF Scheduler = "HSA" THEN 
            /\  InitHSA
        ELSE
            /\  FALSE
    
Init ==
    /\  InitGPU
    /\  InitThreads
    /\  InitScheduler

OBEUpdateFairExecutionSet(t) ==
    \* get the workgroup id of thread t, and update fair execution set based on the workgroup id of t
    LET workgroupId == WorkGroupId(t) IN 
        \* if thread t's workgroup is not in fairExecutionSet and there exist one thread in the workgroup that is not terminated, add the workgroup to fairExecutionSet
        IF workgroupId \notin fairExecutionSet /\ \E st \in ThreadsWithinWorkGroup(workgroupId): pc[st] < Len(ThreadInstructions[st]) THEN
            /\  fairExecutionSet' = fairExecutionSet \union {workgroupId}
        \* if thread t's workgroup is in fairExecutionSet and all threads in the workgroup are terminated, remove the workgroup from fairExecutionSet
        ELSE IF workgroupId \in fairExecutionSet /\ \A st \in ThreadsWithinWorkGroup(workgroupId): state[st] = "terminated" THEN
            /\  fairExecutionSet' = fairExecutionSet \ {workgroupId}
        ELSE
            /\  UNCHANGED fairExecutionSet


HSAUpdateFairExecutionSet(t) ==
    \* get the workgroup id that has lowest id and contains non-terminated thread
    LET threadsNotTerminated == {tid \in Threads : state[tid] # "terminated"} IN
            IF threadsNotTerminated # {} THEN 
                /\  fairExecutionSet' = {WorkGroupId(Min(threadsNotTerminated))}
            ELSE 
                /\  fairExecutionSet' = {}
    
UpdateFairExecutionSet(t) == 
    /\  IF Scheduler = "OBE" THEN
        /\  OBEUpdateFairExecutionSet(t)
        ELSE IF Scheduler = "HSA" THEN 
        /\  HSAUpdateFairExecutionSet(t)
        ELSE
        /\  Print("Uknown Scheduler", FALSE)

\* This fairness property ensures that every workgroup in the fair execution set will be scheduled at some point indefinitely
\* So we don't have a unfairness problem where some workgroup in the fair execution set is never scheduled/only scheduled once
PickAnyWorkGroupInFairExecutionSet ==
            <>[](\A wg \in fairExecutionSet: selected = wg)      
    
Execute(t) == 
        /\  Step(t)
        /\  UpdateFairExecutionSet(t)
        /\  selected' = WorkGroupId(t)


FairStep ==
    LET ThreadsReady == {t \in Threads: state[t] = "ready"}
    IN
        \*  if there is any thread that is not terminated, execute it
        IF ThreadsReady # {} THEN
            \E t \in ThreadsReady:
                /\  Execute(t)
        ELSE
            /\ UNCHANGED vars
\* Deadlock means reaching a state in which Next is not enabled.
Next ==
    FairStep


Fairness ==
    /\  <>[](ENABLED <<FairStep>>_vars) => ([]<><<FairStep>>_vars /\ PickAnyWorkGroupInFairExecutionSet)
    
(* Specification *)
Spec == 
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

\* eventually all threads are always terminatedac
EventuallyAlwaysTerminated ==
    \A t \in Threads: <>[](pc[t] = Len(ThreadInstructions[t]))

Liveness == 
    /\  EventuallyAlwaysTerminated

====
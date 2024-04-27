---- MODULE MCProgressModel ----
EXTENDS Integers, Naturals, Sequences, MCThreads, MCLayout

VARIABLES fairExecutionSet, curExeSubgroupTs, selected

vars == <<fairExecutionSet, curExeSubgroupTs, pc, terminated, barrier, selected, liveVars>>


InitOBE ==
    /\  fairExecutionSet = {} \* fair execution set(subgroup) for workgroup 0, initially empty
    /\  curExeSubgroupTs = [workgroup \in 1..NumWorkGroups |-> {}] \* threads in the same subgroup that are currently executing
    /\ selected = -1

InitHSA ==
    /\  fairExecutionSet = {t \in Threads : t = Min(ThreadsWithinWorkGroup(0))}
    /\  curExeSubgroupTs = [workgroup \in 1..NumWorkGroups |-> {}]
    /\  selected = -1

InitScheduler ==
    /\  InitOBE
    
Init ==
    /\  InitProgram
    /\  InitThreads
    /\  InitScheduler

UpdateFairExecutionSet(t) ==
    \* get the subgroup id of thread t, and update fair execution set based on the subgroup id of t
    LET workgroupId == WorkGroupId(t) IN 
        \* if thread t's workgroup is not in fairExecutionSet and there exist one thread in the workgroup that is not terminated, add the workgroup to fairExecutionSet
        IF workgroupId \notin fairExecutionSet /\ \E st \in ThreadsWithinWorkGroup(workgroupId): terminated[st] = FALSE THEN
            /\  fairExecutionSet' = fairExecutionSet \union {workgroupId}
        \* if thread t's workgroup is in fairExecutionSet and all threads in the workgroup are terminated, remove the workgroup from fairExecutionSet
        ELSE IF workgroupId \in fairExecutionSet /\ \A st \in ThreadsWithinWorkGroup(workgroupId): terminated[st] = TRUE THEN
            /\  fairExecutionSet' = fairExecutionSet \ {workgroupId}
        ELSE
            /\  UNCHANGED fairExecutionSet

\* Update the set of threads in the same subgroup that are currently executing
UpdatecurExeSubgroupTs(t) == 
    LET workgroupId == WorkGroupId(t)+1 IN 
        IF t \in curExeSubgroupTs[workgroupId]  THEN  \* if t is in curExeSubgroupTs and it made a step, remove it
            /\  curExeSubgroupTs'[workgroupId] = [curExeSubgroupTs EXCEPT ![workgroupId] = curExeSubgroupTs[workgroupId] \ {t}]
        ELSE IF curExeSubgroupTs[workgroupId] = {} THEN  \* if curExeSubgroupTs is empty, add other threads in the same subgroup except t
            /\  curExeSubgroupTs' = [curExeSubgroupTs EXCEPT ![workgroupId] = ThreadsWithinSubgroup(SubgroupId(t), WorkGroupId(t)) \{t}]
        ELSE 
            /\  UNCHANGED curExeSubgroupTs

Execute(t) == 
        /\  selected' = t
        /\  Step(t)
        /\  UpdateFairExecutionSet(t)
        /\  UpdatecurExeSubgroupTs(t)


FairStep ==
    \* threads within the same subgroup that are executing that are not at barrier
    LET lockstepExecThreads == {t \in (UNION {curExeSubgroupTs[i] : i \in DOMAIN curExeSubgroupTs}) : barrier[t] = "NULL" /\  pc[t] = LowestPcWithinSubgroup(SubgroupId(t), WorkGroupId(t)) } 
        \* threads in fair execution set that are not at barrier
        FairExecutionThreads == {t \in Threads: WorkGroupId(t) \in fairExecutionSet /\ barrier[t] = "NULL" /\ pc[t] = LowestPcWithinSubgroup(SubgroupId(t), WorkGroupId(t))} 
        IN
        \*  lockstep execution first, then threads in fair execution set that are not at barrier, then any thread
        /\  IF lockstepExecThreads # {} THEN 
                /\
                    \E t \in lockstepExecThreads:
                        Execute(t)
            ELSE IF FairExecutionThreads # {} THEN
                /\
                    \E t \in FairExecutionThreads:
                        Execute(t)
            ELSE
                \/
                    \E t \in Threads:
                        Execute(t)


\* Deadlock means reaching a state in which Next is not enabled.
Next ==
    /\  FairStep

Fairness ==
    /\  WF_vars(FairStep)

(* Specification *)
Spec == 
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

\* ProgressProperty ensures that the selected thread must make progress
ProgressProperty == [][\A t \in Threads: (selected' = t) => (terminated'[t] = TRUE \/ pc'[t] > pc[t])]_vars

\* eventually all threads are always terminated
EventuallyAlwaysTerminated ==
    \A t \in Threads: <>[](terminated[t] = TRUE)

\* all threads that appears in the fair execution will lead these threads to be terminated at some point
FairExecutionEventuallyTerminated ==
    \A t \in Threads: WorkGroupId(t) \in fairExecutionSet ~> (terminated[t] = TRUE) 

Liveness == 
    /\  FairExecutionEventuallyTerminated
    /\  ProgressProperty

====

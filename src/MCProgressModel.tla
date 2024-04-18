---- MODULE MCProgressModel ----
EXTENDS Integers, Naturals, Sequences, MCThreads, MCLayout

VARIABLES fairExecutionSetOne, fairExecutionSetTwo, curExeSubgroupTs

vars == <<fairExecutionSetOne, fairExecutionSetTwo, curExeSubgroupTs, checkLock, pc, terminated, barrier>>

\* fairness at workgroup level, assume two workgroups
InitOBE ==
    /\  fairExecutionSetOne = {} \* fair execution set(subgroup) for workgroup 0, initially empty
    /\  fairExecutionSetTwo = {} \* fair execution set(subgroup) for workgroup 1, initially empty
    /\  curExeSubgroupTs = {} \* threads in the same subgroup that are currently executing


\* fairness at workgroup level, assume two workgroups
InitHSA ==
    /\  fairExecutionSetOne = {t \in Threads : t = Min(ThreadsWithinWorkGroup(0))}
    /\  fairExecutionSetTwo = {t \in Threads : t = Min(ThreadsWithinWorkGroup(1))}
    /\ curExeSubgroupTs = {}

InitScheduler ==
    /\  InitOBE
    
Init ==
    /\  InitScheduler
    /\  InitThreads

UpdateFairExecutionSet(t) ==
    \* get the subgroup id of thread t, and update fair execution set based on the subgroup id of t
    LET subgroupId == SubgroupId(t) IN 
        \* if t is in workgroup 0 and its subgroup is not in fairExecutionSetOne and there exist one thread in the subgroup that is not terminated, add the subgroup to fairExecutionSetOne
        IF t \in ThreadsWithinWorkGroup(0) /\ subgroupId \notin fairExecutionSetOne /\ \E st \in ThreadsWithinSubgroup(subgroupId, 0): terminated[st] = FALSE THEN
            /\  fairExecutionSetOne' = fairExecutionSetOne \union {subgroupId}
            /\  UNCHANGED fairExecutionSetTwo
        \* if t is in workgroup 0 and its subgroup is in fairExecutionSetOne and all threads in the subgroup are terminated, remove the subgroup from fairExecutionSetOne
        ELSE IF t \in ThreadsWithinWorkGroup(0) /\ subgroupId \in fairExecutionSetOne /\ \E st \in ThreadsWithinSubgroup(subgroupId, 0): terminated[st] = TRUE THEN
            /\  fairExecutionSetOne' = fairExecutionSetOne \ {subgroupId}
            /\  UNCHANGED fairExecutionSetTwo
        \* if t is in workgroup 1 and its subgroup is not in fairExecutionSetTwo and there exist one thread in the subgroup that is not terminated, add the subgroup to fairExecutionSetTwo
        ELSE IF t \in ThreadsWithinWorkGroup(1) /\ subgroupId \notin fairExecutionSetTwo /\ \E st \in ThreadsWithinSubgroup(subgroupId, 1): terminated[st] = FALSE THEN
            /\  fairExecutionSetTwo' = fairExecutionSetTwo \union {subgroupId}
            /\  UNCHANGED fairExecutionSetOne
        \* if t is in workgroup 1 and its subgroup is in fairExecutionSetTwo and all threads in the subgroup are terminated, remove the subgroup from fairExecutionSetTwo
        ELSE IF t \in ThreadsWithinWorkGroup(1) /\ subgroupId \in fairExecutionSetTwo /\ \E st \in ThreadsWithinSubgroup(subgroupId, 1): terminated[st] = TRUE THEN
            /\  fairExecutionSetTwo' = fairExecutionSetTwo \ {subgroupId}
            /\  UNCHANGED fairExecutionSetOne
        ELSE
            /\  UNCHANGED fairExecutionSetOne
            /\  UNCHANGED fairExecutionSetTwo

\* Update the set of threads in the same subgroup that are currently executing
UpdatecurExeSubgroupTs(t) == 
    IF t \in curExeSubgroupTs THEN  \* if t is in curExeSubgroupTs and it made a step, remove it
        /\  curExeSubgroupTs' = curExeSubgroupTs \ {t}
    ELSE IF curExeSubgroupTs = {} THEN  \* if curExeSubgroupTs is empty, add other threads in the same subgroup except t
        /\  curExeSubgroupTs' = ThreadsWithinSubgroup(SubgroupId(t), WorkGroupId(t)) \{t}
    ELSE
        /\ UNCHANGED curExeSubgroupTs

FairStep ==
    \* threads within the same subgroup that are executing that are not at barrier
    LET lockstepExecThreads == {t \in curExeSubgroupTs : barrier[t] = "NULL"} 
        \* threads in fair execution set that are not at barrier
        threadNotAtBarrier == {t \in Threads: WorkGroupId(t) = 0 /\ SubgroupId(t) \in fairExecutionSetOne /\ barrier[t] = "NULL"} 
            \union {t \in Threads: WorkGroupId(t) = 1 /\ SubgroupId(t) \in fairExecutionSetTwo /\ barrier[t] = "NULL"} 
        IN
        \*  lockstep execution first, then threads in fair execution set that are not at barrier, then any thread
        /\  IF lockstepExecThreads # {} THEN \* Randomly select a thread in lockstep execution that is not at barrier to step
                /\ \E t \in lockstepExecThreads:
                    /\  pc[t] = LowestPcWithinSubgroup(SubgroupId(t), WorkGroupId(t)) \* choose the thread with the lowest pc wtihin the subgroup
                    /\  Step(t)
                    /\  UpdateFairExecutionSet(t)
                    /\  UpdatecurExeSubgroupTs(t)
            ELSE IF threadNotAtBarrier # {} THEN \* Randomly select a thread in fair execution set that is not at barrier to step
                /\  \E t \in threadNotAtBarrier:
                    /\  Step(t)
                    /\  UpdateFairExecutionSet(t)
                    /\  UpdatecurExeSubgroupTs(t)
            ELSE   
                /\ \E t \in Threads:
                    /\  Step(t)
                    /\  UpdateFairExecutionSet(t)
                    /\  UpdatecurExeSubgroupTs(t)



\* Deadlock means reaching a state in which Next is not enabled.
Next ==
    /\  FairStep

 \* always eventually all threads are terminated
AlwaysEventuallyTerminated ==
    \A t \in Threads: []<>(terminated[t] = TRUE)

(* Specification *)
Spec == 
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next) \* Weak fairness guarnatees that if Next action are be enabled continuously(always enable), it would eventually happen 
    
Liveness == AlwaysEventuallyTerminated
====

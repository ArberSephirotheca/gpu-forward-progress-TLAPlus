---- MODULE MCProgressModel ----
EXTENDS Integers, Naturals, Sequences, MCThreads, MCLayout

VARIABLES fairExecutionSetOne, fairExecutionSetTwo, curExeSubgroupTsOne, curExeSubgroupTsTwo

vars == <<fairExecutionSetOne, fairExecutionSetTwo, curExeSubgroupTsOne, curExeSubgroupTsTwo, checkLock, pc, terminated, barrier>>

\* fairness at workgroup level, assume two workgroups
InitOBE ==
    /\  fairExecutionSetOne = {} \* fair execution set(subgroup) for workgroup 0, initially empty
    /\  fairExecutionSetTwo = {} \* fair execution set(subgroup) for workgroup 1, initially empty
    /\  curExeSubgroupTsOne = {} \* threads in the same subgroup that are currently executing
    /\  curExeSubgroupTsTwo = {} \* threads in the same subgroup that are currently executing


\* fairness at workgroup level, assume two workgroups
InitHSA ==
    /\  fairExecutionSetOne = {t \in Threads : t = Min(ThreadsWithinWorkGroup(0))}
    /\  fairExecutionSetTwo = {t \in Threads : t = Min(ThreadsWithinWorkGroup(1))}
    /\  curExeSubgroupTsOne = {}
    /\  curExeSubgroupTsTwo = {}

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
    LET workgroupId == WorkGroupId(t) IN 
        IF t \in curExeSubgroupTsOne /\ workgroupId = 0 THEN  \* if t is in curExeSubgroupTs and it made a step, remove it
            /\  curExeSubgroupTsOne' = curExeSubgroupTsOne \ {t}
            /\ UNCHANGED curExeSubgroupTsTwo
        ELSE IF curExeSubgroupTsOne = {} /\ workgroupId = 0 THEN  \* if curExeSubgroupTs is empty, add other threads in the same subgroup except t
            /\  curExeSubgroupTsOne' = ThreadsWithinSubgroup(SubgroupId(t), WorkGroupId(t)) \{t}
            /\  UNCHANGED curExeSubgroupTsTwo
        ELSE IF t \in curExeSubgroupTsTwo /\ workgroupId = 1 THEN  \* if t is in curExeSubgroupTs and it made a step, remove it
            /\  curExeSubgroupTsTwo' = curExeSubgroupTsTwo \ {t}
            /\ UNCHANGED curExeSubgroupTsOne
        ELSE IF curExeSubgroupTsTwo = {} /\ workgroupId = 1 THEN  \* if curExeSubgroupTs is empty, add other threads in the same subgroup except t
            /\  curExeSubgroupTsTwo' = ThreadsWithinSubgroup(SubgroupId(t), WorkGroupId(t)) \{t}
            /\  UNCHANGED curExeSubgroupTsOne
        ELSE
            /\  UNCHANGED curExeSubgroupTsOne
            /\  UNCHANGED curExeSubgroupTsTwo

FairStep ==
    \* threads within the same subgroup that are executing that are not at barrier
    LET lockstepExecThreadsOne == {t \in curExeSubgroupTsOne : barrier[t] = "NULL"} 
        lockstepExecThreadsTwo == {t \in curExeSubgroupTsTwo : barrier[t] = "NULL"}
        \* threads in fair execution set that are not at barrier
        GroupOneThreadNotAtBarrier == {t \in Threads: WorkGroupId(t) = 0 /\ SubgroupId(t) \in fairExecutionSetOne /\ barrier[t] = "NULL" /\ pc[t] = LowestPcWithinSubgroup(SubgroupId(t), WorkGroupId(t))} 
        GroupTwoThreadNotAtBarrier == {t \in Threads: WorkGroupId(t) = 1 /\ SubgroupId(t) \in fairExecutionSetTwo /\ barrier[t] = "NULL" /\ pc[t] = LowestPcWithinSubgroup(SubgroupId(t), WorkGroupId(t))} 
        IN
        \*  lockstep execution first, then threads in fair execution set that are not at barrier, then any thread
        /\  IF lockstepExecThreadsOne # {} /\ lockstepExecThreadsTwo # {} THEN \* Randomly select a thread in lockstep execution that is not at barrier to step
                \/
                    \E t \in lockstepExecThreadsOne:
                        /\  pc[t] = LowestPcWithinSubgroup(SubgroupId(t), WorkGroupId(t)) \* choose the thread with the lowest pc wtihin the subgroup
                        /\  Step(t)
                        /\  UpdateFairExecutionSet(t)
                        /\  UpdatecurExeSubgroupTs(t)
                \/
                    \E t \in lockstepExecThreadsTwo:
                        /\  pc[t] = LowestPcWithinSubgroup(SubgroupId(t), WorkGroupId(t)) \* choose the thread with the lowest pc wtihin the subgroup
                        /\  Step(t)
                        /\  UpdateFairExecutionSet(t)
                        /\  UpdatecurExeSubgroupTs(t)
            ELSE IF GroupOneThreadNotAtBarrier # {} /\ GroupTwoThreadNotAtBarrier # {} THEN \* Randomly select a thread in fair execution set that is not at barrier to step
                \/
                    \E t \in GroupOneThreadNotAtBarrier:
                        /\  Step(t)
                        /\  UpdateFairExecutionSet(t)
                        /\  UpdatecurExeSubgroupTs(t)
                \/
                    \E t \in GroupTwoThreadNotAtBarrier:
                        /\  Step(t)
                        /\  UpdateFairExecutionSet(t)
                        /\  UpdatecurExeSubgroupTs(t)
            ELSE IF lockstepExecThreadsOne # {} /\ GroupTwoThreadNotAtBarrier # {} THEN 
                \/
                    \E t \in lockstepExecThreadsOne:
                        /\  pc[t] = LowestPcWithinSubgroup(SubgroupId(t), WorkGroupId(t)) \* choose the thread with the lowest pc wtihin the subgroup
                        /\  Step(t)
                        /\  UpdateFairExecutionSet(t)
                        /\  UpdatecurExeSubgroupTs(t)
                \/
                    \E t \in GroupTwoThreadNotAtBarrier:
                        /\  Step(t)
                        /\  UpdateFairExecutionSet(t)
                        /\  UpdatecurExeSubgroupTs(t)
            ELSE IF lockstepExecThreadsTwo # {} /\ GroupOneThreadNotAtBarrier # {} THEN
                \/
                    \E t \in lockstepExecThreadsTwo:
                        /\  pc[t] = LowestPcWithinSubgroup(SubgroupId(t), WorkGroupId(t)) \* choose the thread with the lowest pc wtihin the subgroup
                        /\  Step(t)
                        /\  UpdateFairExecutionSet(t)
                        /\  UpdatecurExeSubgroupTs(t)
                \/
                    \E t \in GroupOneThreadNotAtBarrier:
                        /\  Step(t)
                        /\  UpdateFairExecutionSet(t)
                        /\  UpdatecurExeSubgroupTs(t)
            ELSE IF lockstepExecThreadsOne # {} /\ GroupTwoThreadNotAtBarrier = {} THEN
                \/
                    \E t \in lockstepExecThreadsOne:
                        /\  pc[t] = LowestPcWithinSubgroup(SubgroupId(t), WorkGroupId(t)) \* choose the thread with the lowest pc wtihin the subgroup
                        /\  Step(t)
                        /\  UpdateFairExecutionSet(t)
                        /\  UpdatecurExeSubgroupTs(t)
                \/
                    \E t \in Threads:
                        /\  Step(t)
                        /\  UpdateFairExecutionSet(t)
                        /\  UpdatecurExeSubgroupTs(t)
            ELSE IF lockstepExecThreadsTwo # {} /\ GroupOneThreadNotAtBarrier = {} THEN
                \/
                    \E t \in lockstepExecThreadsTwo:
                        /\  pc[t] = LowestPcWithinSubgroup(SubgroupId(t), WorkGroupId(t)) \* choose the thread with the lowest pc wtihin the subgroup
                        /\  Step(t)
                        /\  UpdateFairExecutionSet(t)
                        /\  UpdatecurExeSubgroupTs(t)
                \/
                    \E t \in Threads:
                        /\  Step(t)
                        /\  UpdateFairExecutionSet(t)
                        /\  UpdatecurExeSubgroupTs(t)
            ELSE IF GroupOneThreadNotAtBarrier # {} /\ GroupTwoThreadNotAtBarrier = {} THEN
                \/
                    \E t \in GroupOneThreadNotAtBarrier:
                        /\  Step(t)
                        /\  UpdateFairExecutionSet(t)
                        /\  UpdatecurExeSubgroupTs(t)
                \/
                    \E t \in Threads:
                        /\  Step(t)
                        /\  UpdateFairExecutionSet(t)
                        /\  UpdatecurExeSubgroupTs(t)
            ELSE IF GroupTwoThreadNotAtBarrier # {} /\ GroupOneThreadNotAtBarrier = {} THEN
                \/
                    \E t \in GroupTwoThreadNotAtBarrier:
                        /\  Step(t)
                        /\  UpdateFairExecutionSet(t)
                        /\  UpdatecurExeSubgroupTs(t)
                \/
                    \E t \in Threads:
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

EventuallyAlwaysTerminated ==
    \A t \in Threads: <>[](terminated[t] = TRUE) \* eventually all threads are always terminated

(* Specification *)
Spec == 
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next) \* Weak fairness guarnatees that if Next action are be enabled continuously(always enable), it would eventually happen 
    
Liveness == EventuallyAlwaysTerminated
====

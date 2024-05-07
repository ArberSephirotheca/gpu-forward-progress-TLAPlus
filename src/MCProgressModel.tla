---- MODULE MCProgressModel ----
EXTENDS Integers, Naturals, Sequences, MCThreads, MCLayout, TLC

VARIABLES fairExecutionSet, selected\*,curExeSubgroupTs*\

vars == <<fairExecutionSet, pc, terminated, barrier, selected, lastTimeExecuted, liveVars, globalVars>>


InitOBE ==
    /\  fairExecutionSet = {} 
    /\ selected = -1

InitHSA ==
    /\  fairExecutionSet = {0}
    /\  selected = -1

InitScheduler ==
    /\  IF Scheduler = "OBE" THEN
            /\  InitOBE
            /\  Print("OBE Scheduler", TRUE)
        ELSE IF Scheduler = "HSA" THEN 
            /\  InitHSA
            /\  Print("HSA Scheduler", TRUE)
        ELSE
            /\  FALSE
    
Init ==
    /\  InitProgram
    /\  InitThreads
    /\  InitScheduler

OBEUpdateFairExecutionSet(t) ==
    \* get the workgroup id of thread t, and update fair execution set based on the workgroup id of t
    LET workgroupId == WorkGroupId(t) IN 
        \* if thread t's workgroup is not in fairExecutionSet and there exist one thread in the workgroup that is not terminated, add the workgroup to fairExecutionSet
        IF workgroupId \notin fairExecutionSet /\ \E st \in ThreadsWithinWorkGroup(workgroupId): pc[st] < Len(ThreadInstructions[st]) THEN
            /\  fairExecutionSet' = fairExecutionSet \union {workgroupId}
        \* if thread t's workgroup is in fairExecutionSet and all threads in the workgroup are terminated, remove the workgroup from fairExecutionSet
        ELSE IF workgroupId \in fairExecutionSet /\ \A st \in ThreadsWithinWorkGroup(workgroupId): pc[st] = Len(ThreadInstructions[st]) THEN
            /\  fairExecutionSet' = fairExecutionSet \ {workgroupId}
        ELSE
            /\  UNCHANGED fairExecutionSet


HSAUpdateFairExecutionSet(t) ==
    \* get the workgroup id of thread t, and form a set of threads that does not terminate yet
    LET elimiantedWorkgroup == {workgroupId \in fairExecutionSet: \A st \in ThreadsWithinWorkGroup(workgroupId): pc[st] = Len(ThreadInstructions[st])}
        threadsNotTerminated == {tid \in Threads : pc[tid] < Len(ThreadInstructions[tid])} IN
            IF threadsNotTerminated # {} THEN 
                /\  fairExecutionSet' = {WorkGroupId(Min(threadsNotTerminated))}
            ELSE 
                /\  fairExecutionSet' = {}
            \* IF elimiantedWorkgroup # {} /\ threadsNotTerminated # {} THEN 
            \*     /\  fairExecutionSet' = (fairExecutionSet \ elimiantedWorkgroup) \union {WorkGroupId(Min(threadsNotTerminated))}
            \* ELSE IF elimiantedWorkgroup # {} THEN 
            \*     /\  fairExecutionSet' = fairExecutionSet \ elimiantedWorkgroup
        \* if thread t's workgroup is in fairExecutionSet and all threads in the workgroup are terminated, remove the workgroup from fairExecutionSet
        \* IF workgroupId \in fairExecutionSet /\ \A st \in ThreadsWithinWorkGroup(workgroupId): terminated[st] = TRUE THEN
        \*         \* if all threads are terminated, just remove the current workgroup from set 
        \*     /\  IF threadsNotTerminated = {} THEN 
        \*             /\  fairExecutionSet' = fairExecutionSet \ {workgroupId}
        \*         \*  else remove the current workgroup from set and add the workgroup that live thread with lowest id belongs to
        \*         ELSE 
        \*             /\  fairExecutionSet' = (fairExecutionSet \ {workgroupId}) \union {WorkGroupId(Min(threadsNotTerminated))}
        \* \* else, no dothing
        \* ELSE
        \*     \* /\  Print(ThreadsWithinWorkGroup(workgroupId), TRUE)
        \*     /\  UNCHANGED fairExecutionSet
    
UpdateFairExecutionSet(t) == 
    /\  IF Scheduler = "OBE" THEN
        /\  OBEUpdateFairExecutionSet(t)
        ELSE IF Scheduler = "HSA" THEN 
        /\  HSAUpdateFairExecutionSet(t)
        ELSE
        /\  Print("Uknown Scheduler", FALSE)

\* \* Update the set of threads in the same subgroup that are currently executing
\* UpdatecurExeSubgroupTs(t) == 
\*     LET workgroupId == WorkGroupId(t)+1 IN 
\*         IF t \in curExeSubgroupTs[workgroupId]  THEN  \* if t is in curExeSubgroupTs and it made a step, remove it
\*             /\  curExeSubgroupTs'[workgroupId] = [curExeSubgroupTs EXCEPT ![workgroupId] = curExeSubgroupTs[workgroupId] \ {t}]
\*         ELSE IF curExeSubgroupTs[workgroupId] = {} THEN  \* if curExeSubgroupTs is empty, add other threads in the same subgroup except t
\*             /\  curExeSubgroupTs' = [curExeSubgroupTs EXCEPT ![workgroupId] = ThreadsWithinSubgroup(SubgroupId(t), WorkGroupId(t)) \{t}]
\*         ELSE 
\*             /\  UNCHANGED curExeSubgroupTs

Execute(t) == 
        /\  selected' = t
        /\  lastTimeExecuted' = [tid \in Threads |-> IF tid = t THEN 0 ELSE lastTimeExecuted[tid] - 1]
        /\  Step(t)
        /\  UpdateFairExecutionSet(t)
        \* /\  UpdatecurExeSubgroupTs(t)


FairStep ==
    \* threads within the same subgroup that are executing that are not at barrier
    \* LET lockstepExecThreads == {t \in (UNION {curExeSubgroupTs[i] : i \in DOMAIN curExeSubgroupTs}) : barrier[t] = "NULL" /\  pc[t] = LowestPcWithinSubgroup(SubgroupId(t), WorkGroupId(t)) } 
        \* threads in fair execution set that are not at barrier or threads that all workgroup threads are at barrier
    LET FairExecutionThreads == {t \in Threads: WorkGroupId(t) \in fairExecutionSet /\ (barrier[t] = "NULL" \/ (\A st \in ThreadsWithinSubgroup(SubgroupId(t), WorkGroupId(t)) : barrier[st] # "NULL")) /\ terminated[t] = FALSE}
        FairExecutionStuckThreads == {t \in Threads:  WorkGroupId(t) \in fairExecutionSet /\ barrier[t] # "NULL" /\ terminated[t] = FALSE}
        \* ThreadsNotTerminated == {t \in Threads : terminated[t] = FALSE /\ barrier[t] = "NULL"}
        ThreadsNotTerminated == {t \in Threads: barrier[t] = "NULL" /\ terminated[t] = FALSE /\  WorkGroupId(t) \notin fairExecutionSet }
        IN
        \*  lockstep execution first, then threads in fair execution set that are not at barrier, then any thread
        \* /\  IF lockstepExecThreads # {} THEN 
        \*         /\
        \*             \E t \in lockstepExecThreads:
        \*                 Execute(t)
        \* IF FairExecutionThreads # {} THEN
        \*     /\
        \*         \E t \in FairExecutionThreads:
        \*             Execute(t)
        \* ELSE
        \* /\  IF FairExecutionThreads # {} THEN 
        \*     \/  \E t \in FairExecutionThreads:
        \*         /\  Execute(t)
        \*     \/  \E t \in ThreadsNotTerminated:
        \*         /\  Execute(t)

        \*     ELSE IF ThreadsNotTerminated # {} THEN
        \*         \E t \in ThreadsNotTerminated:
        \*             /\  Execute(t)
        \*     ELSE
        \*         /\  TRUE
        \*         /\  UNCHANGED vars
            \* Make sure to always pick thread in fair execution set that will make progress
            \* IF (FairExecutionThreads \ FairExecutionStuckThreads) # {} THEN
            \*     \E t \in (FairExecutionThreads \ FairExecutionStuckThreads):
            \*         /\  Execute(t)
            \* ELSE IF FairExecutionStuckThreads # {} THEN
            \*     \E t \in FairExecutionStuckThreads:
            \*         /\  Execute(t)
            \* ELSE
            \*     \E t \in ThreadsNotTerminated:
            \*         /\  Execute(t)
            IF FairExecutionThreads \intersect MinIndices(lastTimeExecuted , FairExecutionThreads) # {} THEN 
                \E t \in FairExecutionThreads \intersect MinIndices(lastTimeExecuted , FairExecutionThreads):
                    /\  Execute(t)
            ELSE IF FairExecutionThreads # {} THEN
                \E t \in FairExecutionThreads:
                    /\  Execute(t)

            ELSE IF ThreadsNotTerminated # {} THEN
                \E t \in ThreadsNotTerminated:
                    /\  Execute(t)
            ELSE 
                /\  UNCHANGED vars

UnfairStep == 
    LET ThreadsNotTerminated == {t \in Threads: barrier[t] = "NULL" 
        /\ terminated[t] = FALSE 
        /\  WorkGroupId(t) \notin fairExecutionSet } IN
        \*  if there is any thread that is not terminated, execute it
        IF ThreadsNotTerminated # {} THEN
            \E t \in ThreadsNotTerminated:
                /\  Execute(t)
        ELSE
            /\ UNCHANGED vars
\* Deadlock means reaching a state in which Next is not enabled.
Next ==
    \/  FairStep
    \/  UnfairStep

Fairness ==
    /\  SF_vars(FairStep)

(* Specification *)
Spec == 
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

\* ProgressProperty ensures that the selected thread must make progress
ProgressProperty == 
    \* [][\A t \in Threads: (selected' = t) => (pc'[t] = Len(ThreadInstructions[t]) \/ pc'[t] > pc[t])]_vars
    [][\A t \in Threads: (selected' = t) => (vars' # vars)]_vars

\* eventually all threads are always terminated
EventuallyAlwaysTerminated ==
    \A t \in Threads: <>[](pc[t] = Len(ThreadInstructions[t]))

\* all threads that appears in the fair execution will lead these threads to be terminated at some point
FairExecutionEventuallyTerminated ==
    \A t \in Threads: WorkGroupId(t) \in fairExecutionSet ~> (pc[t] = Len(ThreadInstructions[t])) 

\* For all threads within the fair execution set, it will be scheduled at some point
FairExecutionEventuallyChoosen ==
    \A t \in Threads: WorkGroupId(t) \in fairExecutionSet ~> (selected = t)
Liveness == 
    /\  EventuallyAlwaysTerminated
    /\  FairExecutionEventuallyChoosen
    \* /\  ProgressProperty
    \* /\  EventuallyAlwaysTerminated

====

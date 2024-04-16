---- MODULE MCThreads ----
LOCAL INSTANCE Integers
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE MCLayout
LOCAL INSTANCE TLC
VARIABLES checkLock, pc, terminated, barrier

(* Thread Configuration *)
InstructionSet == {"NOOP", "Load", "Store", "Lock", "Unlock", "WorkgroupBarrier", "AtomicCAS", "Terminate"}
BarrierSet == {"NULL", "SubgroupBarrier", "WorkgroupBarrier"}
ThreadInstructions ==  [t \in 1..NumThreads |-> IF LocalInvocationId(t) = 0 THEN <<"NOOP", "WorkgroupBarrier", "Terminate">> ELSE <<"WorkgroupBarrier", "Terminate">>]
Threads == {tid : tid \in 1..NumThreads}

LOCAL INSTANCE ThreadsConf


(* Thread variables and functions start here *)
threadVars == << checkLock, pc, terminated, barrier >>

InitThreadVars ==
    /\  pc = [t \in Threads |-> 1]
    /\  terminated = [t \in Threads |-> FALSE]
    /\  barrier = [t \in Threads |-> "NULL"]

InitThreads == 
    /\  InitThreadVars
    /\  checkLock = FALSE


ThreadsWithinWorkGroup(wgid) == {tid \in Threads : WorkGroupId(tid) = wgid}

ThreadsWithinSubgroup(sid, wgid) == {tid \in Threads : SubgroupId(tid) = sid} \intersect ThreadsWithinWorkGroup(wgid)

UpdateBarrier(tid, barrierState) ==
    /\  barrierState \in BarrierSet
    /\  barrier' = [barrier EXCEPT ![tid] = barrierState]
    
SubgroupBarrier(t) ==
    /\  IF barrier[t] = "SubgroupBarrier" THEN \* already waiting at a subgroup barrier
            LET affectedThreadsBarrier == {barrier[affectedThreads]: affectedThreads \in ThreadsWithinSubgroup(SubgroupId(t), WorkGroupId(t))}
                affectedThreads == ThreadsWithinSubgroup(SubgroupId(t), WorkGroupId(t))
            IN 
                IF \A affected \in affectedThreadsBarrier : affected = "SubgroupBarrier" THEN \* if all threads in the subgroup are waiting at the barrier, release them
                    /\  barrier' = [\* release all threads in the subgroup, marking barrier as null
                            tid \in Threads |->
                                IF tid \in affectedThreads THEN 
                                    "NULL" 
                                ELSE 
                                    barrier[tid]
                        ]
                    /\  pc' = [ \* increment the program counter for all threads in the subgroup
                            tid \in Threads |->
                                IF tid \in affectedThreads THEN 
                                    pc[tid] + 1
                                ELSE 
                                    pc[tid]
                        ]
                ELSE
                    /\  UNCHANGED barrier \* else, do nothing as some threads are still not at the barrier
        ELSE
            /\  UpdateBarrier(t, "SubgroupBarrier") \* set the barrier for the thread
    /\  UNCHANGED <<pc, checkLock, terminated>>


WorkgroupBarrier(t) ==
    /\  IF barrier[t] = "WorkgroupBarrier" THEN \* already waiting at a workgroup barrier
            LET affectedThreadsBarrier == {barrier[affectedThreads]: affectedThreads \in ThreadsWithinWorkGroup(WorkGroupId(t))}
                affectedThreads == ThreadsWithinWorkGroup(WorkGroupId(t))
            IN 
                IF \A affected \in affectedThreadsBarrier : affected = "WorkgroupBarrier" THEN \* if all threads in the workgroup are waiting at the barrier, release them
                    /\  barrier' = [
                            tid \in Threads |->
                                IF tid \in affectedThreads THEN 
                                    "NULL" 
                                ELSE 
                                    barrier[tid]
                        ]
                    /\  pc' = [ \* increment the program counter for all threads in the subgroup
                            tid \in Threads |->
                                IF tid \in affectedThreads THEN 
                                    pc[tid] + 1
                                ELSE 
                                    pc[tid]
                        ]
                ELSE
                    /\  UNCHANGED barrier \* else, do nothing as some threads are still not at the barrier
        ELSE
            /\  UpdateBarrier(t, "WorkgroupBarrier") \* set the barrier for the thread
    /\  UNCHANGED <<pc, checkLock, terminated>>

    
AtomicExchange(t, checkVal, jumpInst, doExch, exchVal) ==
    /\  LET newPc == IF checkLock = checkVal THEN jumpInst ELSE pc[t] + 1
            newCheckLock == IF doExch THEN exchVal ELSE checkLock
        IN
            /\ pc' = [pc EXCEPT ![t] = newPc]
            /\ checkLock' = newCheckLock

AtomicCAS(mem, compare, data) == 
    /\  IF mem = compare THEN
            /\  mem' = data
        ELSE
            /\  mem' = mem

NOOP(t) == 
    /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
    /\  UNCHANGED <<checkLock, terminated, barrier>>

Load(t) == 
    /\  AtomicExchange(t, FALSE, pc[t], FALSE, FALSE)
    /\  UNCHANGED <<terminated, barrier>>

Store(t) == 
    /\  AtomicExchange(t, TRUE, pc[t] + 1, TRUE, TRUE)
    /\  UNCHANGED <<terminated, barrier>>

Terminate(t) ==
    /\ terminated' = [terminated EXCEPT ![t] = TRUE]
    /\ UNCHANGED <<pc, checkLock, barrier>>

Step(t) ==
    IF terminated[t] = FALSE THEN
        IF ThreadInstructions[t][pc[t]] = "Load" THEN
            Load(t)
        ELSE IF ThreadInstructions[t][pc[t]] = "Store" THEN
            Store(t)
        ELSE IF ThreadInstructions[t][pc[t]] = "Terminate" THEN
            Terminate(t)
        ELSE IF ThreadInstructions[t][pc[t]] = "NOOP" THEN 
            NOOP(t)
        ELSE
            /\ UNCHANGED threadVars
    ELSE 
        /\ UNCHANGED threadVars


(* This property ensures all the instructions in all threads are bounded to the instruction set *)
AllInstructionsWithinSet ==
    \A t \in Threads:
        \A ins \in DOMAIN ThreadInstructions[t]:
            ThreadInstructions[t][ins] \in InstructionSet


(* This property ensures all the barriers in all threads are bounded to the barrier set *)
AllBarrierWithinSet ==
    \A t \in Threads:
        barrier[t] \in BarrierSet

====
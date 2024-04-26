---- MODULE MCThreads ----
LOCAL INSTANCE Integers
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE MCLayout
LOCAL INSTANCE TLC

VARIABLES pc, terminated, barrier, liveVars
INSTANCE MCProgram



(* Thread Configuration *)
InstructionSet == {"Assignment", "OpAtomicLoad", "OpAtomicStore", "OpAtomicCompareExchange" ,"OpAtomicExchange", "OpBranchConditional", "Terminate"}
VariableScope == {"local", "shared", "direct"}
ScopeOperand == {"workgroup", "subgroup"}
ThreadInstructions ==  [t \in 1..NumThreads |-> <<"Assignment", "OpAtomicCompareExchange", "OpBranchConditional", "OpAtomicStore", "Terminate">> ]
ThreadArguments == [t \in 1..NumThreads |-> <<<<Var("local", Append(ToString(t), "old"), 1)>>, << Append(ToString(t), "old"), "lock", 0, 1>>, <<BinaryExpr("NotEqual",  Append(ToString(t), "old"), 1), 2, 4>>, <<"lock", 0>> >>]
Threads == {tid : tid \in 1..NumThreads}

LOCAL INSTANCE ThreadsConf



(* Thread variables and functions start here *)
threadVars == <<pc, terminated, barrier>>

InitThreadVars ==
    /\  pc = [t \in Threads |-> 1]
    /\  terminated = [t \in Threads |-> FALSE]
    /\  barrier = [t \in Threads |-> "NULL"]

    
InitThreads == 
    /\  InitThreadVars

ThreadsWithinWorkGroup(wgid) == {tid \in Threads : WorkGroupId(tid) = wgid}

ThreadsWithinSubgroup(sid, wgid) == {tid \in Threads : SubgroupId(tid) = sid} \intersect ThreadsWithinWorkGroup(wgid)

LowestPcWithinSubgroup(sid, wgid) == Min({pc[tid]: tid \in ThreadsWithinSubgroup(sid, wgid)})

MinThreadWithinWorkGroup(workgroupId) ==
    Min(ThreadsWithinWorkGroup(workgroupId))

\* UpdateBarrier(tid, barrierState) ==
\*     /\  barrierState \in BarrierSet
\*     /\  barrier' = [barrier EXCEPT ![tid] = barrierState]
    
\* SubgroupBarrier(t) ==
\*     /\  IF barrier[t] = "SubgroupBarrier" THEN \* already waiting at a subgroup barrier
\*             LET affectedThreadsBarrier == {barrier[affectedThreads]: affectedThreads \in ThreadsWithinSubgroup(SubgroupId(t), WorkGroupId(t))}
\*                 affectedThreads == ThreadsWithinSubgroup(SubgroupId(t), WorkGroupId(t))
\*             IN 
\*                 IF \A affected \in affectedThreadsBarrier : affected = "SubgroupBarrier" THEN \* if all threads in the subgroup are waiting at the barrier, release them
\*                     /\  barrier' = [\* release all threads in the subgroup, marking barrier as null
\*                             tid \in Threads |->
\*                                 IF tid \in affectedThreads THEN 
\*                                     "NULL" 
\*                                 ELSE 
\*                                     barrier[tid]
\*                         ]
\*                     /\  pc' = [ \* increment the program counter for all threads in the subgroup
\*                             tid \in Threads |->
\*                                 IF tid \in affectedThreads THEN 
\*                                     pc[tid] + 1
\*                                 ELSE 
\*                                     pc[tid]
\*                         ]
\*                 ELSE
\*                     /\  UNCHANGED <<barrier, pc>> \* else, do nothing as some threads are still not at the barrier
\*         ELSE
\*             /\  UpdateBarrier(t, "SubgroupBarrier") \* set the barrier for the thread
\*             /\  UNCHANGED <<pc>>
\*     /\  UNCHANGED <<checkLock, terminated>>


\* WorkgroupBarrier(t) ==
\*     /\  IF barrier[t] = "WorkgroupBarrier" THEN \* already waiting at a workgroup barrier
\*             LET affectedThreadsBarrier == {barrier[affectedThreads]: affectedThreads \in ThreadsWithinWorkGroup(WorkGroupId(t))}
\*                 affectedThreads == ThreadsWithinWorkGroup(WorkGroupId(t))
\*             IN 
\*                 IF \A affected \in affectedThreadsBarrier : affected = "WorkgroupBarrier" THEN \* if all threads in the workgroup are waiting at the barrier, release them
\*                     /\  barrier' = [
\*                             tid \in Threads |->
\*                                 IF tid \in affectedThreads THEN 
\*                                     "NULL" 
\*                                 ELSE 
\*                                     barrier[tid]
\*                         ]
\*                     /\  pc' = [ \* increment the program counter for all threads in the subgroup
\*                             tid \in Threads |->
\*                                 IF tid \in affectedThreads THEN 
\*                                     pc[tid] + 1
\*                                 ELSE 
\*                                     pc[tid]
\*                         ]
\*                 ELSE
\*                     /\  UNCHANGED <<barrier, pc>> \* else, do nothing as some threads are still not at the barrier
\*         ELSE
\*             /\  UpdateBarrier(t, "WorkgroupBarrier") \* set the barrier for the thread
\*             /\  UNCHANGED <<pc>>
\*     /\  UNCHANGED <<checkLock, terminated>>


Assignment(t, var) == 
    /\  IsVar(var)
    /\  LET workgroupId == WorkGroupId(t)+1
        IN 
            IF VarExists(workgroupId, var) THEN 
                /\  liveVars' = [liveVars EXCEPT ![workgroupId] =  (liveVars[workgroupId] \ {GetVar(workgroupId, var.name)}) \union {var}]
            ELSE 
                /\  liveVars' =  [liveVars EXCEPT ![workgroupId] = liveVars[workgroupId] \union {var}]
    /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
    /\  UNCHANGED <<terminated, barrier>>

OpAtomicLoad(t, result, pointer) ==
    /\  IsVar(result)
    /\  IsVar(pointer)
    /\  Assignment(t, Var(result.scope, result.name, pointer.value))
    /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
    /\  UNCHANGED <<terminated, barrier>>

OpAtomicStore(t, pointer, value) == 
    /\  IsVar(pointer)
    /\  value \in Nat
    /\  Assignment(t, Var(pointer.scope, pointer.name, value))
    /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
    /\  UNCHANGED <<terminated, barrier>>

(* result and pointer are variable, value is literal *)
    

OpAtomicExchange(t, result, pointer, value) == 
    /\  IsVar(result)
    /\  IsVar(pointer)
    /\  value \in Nat
    /\  Assignment(t, Var(result.scope, result.name, pointer.value))
    /\  Assignment(t, Var(pointer.scope, pointer.name, value))
    /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
    /\  UNCHANGED <<terminated, barrier>>

(* result and pointer are variable, compare and value are literal *)
OpAtomicCompareExchange(t, result, pointer, compare, value) ==
    /\  IsVar(result)
    /\  IsVar(pointer)
    /\  compare \in Nat
    /\  value \in Nat
    /\  IF pointer.value = compare THEN
            /\  Assignment(t, Var(result.scope, result.name, pointer.value))
            /\  Assignment(t, Var(pointer.scope, pointer.name, value))
        ELSE
            /\  Assignment(t, Var(result.scope, result.name, pointer.value))
    /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
    /\  UNCHANGED <<terminated, barrier>>

(* condition is an expression, trueLabel and falseLabel are integer representing pc *)
OpBranchConditional(t, condition, trueLabel, falseLabel) ==
    /\  trueLabel \in Nat
    /\  falseLabel \in Nat
    /\  IF EvalExpr(WorkGroupId(t)+1, condition) THEN
            /\  pc' = [pc EXCEPT ![t] = trueLabel]
        ELSE
            /\  pc' = [pc EXCEPT ![t] = falseLabel]
    /\  UNCHANGED <<terminated, barrier>>


Terminate(t) ==
    /\  terminated' = [terminated EXCEPT ![t] = TRUE]

Step(t) ==
    LET workgroupId == WorkGroupId(t)+1
    IN
        IF terminated[t] = FALSE THEN
            IF  ThreadInstructions[t][pc[t]] = "Terminate" THEN
                Terminate(t)
            ELSE IF ThreadInstructions[t][pc[t]] = "Assignment" THEN
                Assignment(t, ThreadArguments[t][pc[t]][1])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpAtomicExchange" THEN
                OpAtomicExchange(t, GetVar(workgroupId,ThreadArguments[t][pc[t]][1]), GetVar(workgroupId,ThreadArguments[t][pc[t]][2]), ThreadArguments[t][pc[t]][3])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpAtomicCompareExchange" THEN
                OpAtomicCompareExchange(t, GetVar(workgroupId,ThreadArguments[t][pc[t]][1]), GetVar(workgroupId,ThreadArguments[t][pc[t]][2]), ThreadArguments[t][pc[t]][3], ThreadArguments[t][pc[t]][4])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpAtomicLoad" THEN
                OpAtomicLoad(t, GetVar(workgroupId,ThreadArguments[t][pc[t]][1]), GetVar(workgroupId,ThreadArguments[t][pc[t]][2]))
            ELSE IF ThreadInstructions[t][pc[t]] = "OpAtomicStore" THEN
                OpAtomicStore(t, GetVar(workgroupId,ThreadArguments[t][pc[t]][1]), ThreadArguments[t][pc[t]][2])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpBranchConditional" THEN
                OpBranchConditional(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE
                /\ UNCHANGED threadVars
        ELSE 
            /\ UNCHANGED threadVars


(* This property ensures all the instructions in all threads are bounded to the instruction set *)
AllInstructionsWithinSet ==
    \A t \in Threads:
        \A ins \in DOMAIN ThreadInstructions[t]:
            ThreadInstructions[t][ins] \in InstructionSet

====
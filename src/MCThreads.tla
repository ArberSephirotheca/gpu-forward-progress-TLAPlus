---- MODULE MCThreads ----
LOCAL INSTANCE Integers
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE MCLayout
LOCAL INSTANCE TLC

VARIABLES pc, terminated, barrier, liveVars
INSTANCE MCProgram



(* Thread Configuration *)
InstructionSet == {"Assignment", "OpAtomicLoad", "OpAtomicStore", "OpAtomicCompareExchange" ,"OpAtomicExchange", "OpBranchConditional", "OpControlBarrier", "Terminate"}
VariableScope == {"local", "shared", "literal"}
ScopeOperand == {"workgroup", "subgroup"}
ThreadInstructions ==  [t \in 1..NumThreads |-> <<"Assignment", "OpAtomicCompareExchange", "OpBranchConditional", "OpAtomicStore", "Terminate">> ]
ThreadArguments == [t \in 1..NumThreads |-> <<<<Var("local", Append(ToString(t), "old"), 1)>>, << Var("local", Append(ToString(t), "old"), ""), Var("shared", "lock", ""), Var("literal", "", 0), Var("literal", "", 1)>>, <<BinaryExpr("NotEqual",  Var("local", Append(ToString(t), "old"), ""), Var("literal", "", 0)), Var("literal", "", 2), Var("literal", "", 4)>>, <<Var("shared", "lock", ""), Var("literal", "", 0)>> >>]
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
\*     /\  UNCHANGED <<terminated>>


Assignment(t, vars) == 
    /\  LET workgroupId == WorkGroupId(t)+1
            currLiveVars == liveVars[WorkGroupId(t)+1]
        IN
            LET eliminatedVars == {currVar \in currLiveVars : \E var \in vars: currVar.name = var.name}
            IN
                /\  liveVars' =  [liveVars EXCEPT ![workgroupId] = (liveVars[workgroupId] \ eliminatedVars) \union vars]
    /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
    /\  UNCHANGED <<terminated, barrier>>

OpAtomicLoad(t, result, pointer) ==
    /\  
        \/  IsLocal(result)
        \/  IsShared(result)
    /\  VarExists(WorkGroupId(t)+1, result.name)
    /\  
        \/  IsLocal(pointer)
        \/  IsShared(pointer)
    /\  VarExists(WorkGroupId(t)+1, pointer.name)
    /\  LET pointerVar == GetVar(WorkGroupId(t)+1, pointer.name)
            resultVar == GetVar(WorkGroupId(t)+1, result.name)
        IN
            /\  Assignment(t, Var(resultVar.scope, resultVar.name, pointerVar.value))
    /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
    /\  UNCHANGED <<terminated, barrier>>

OpAtomicStore(t, pointer, value) == 
    /\  
        \/  IsLocal(pointer)
        \/  IsShared(pointer)
    /\  VarExists(WorkGroupId(t)+1, pointer.name)
    /\  IsLiteral(value)
    /\  LET pointerVar == GetVar(WorkGroupId(t)+1, pointer.name)
        IN
            /\  Assignment(t, {Var(pointerVar.scope, pointerVar.name, value.value)})
    /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
    /\  UNCHANGED <<terminated, barrier>>

(* result and pointer are variable, value is literal *)
OpAtomicExchange(t, result, pointer, value) == 
    /\  
        \/  IsLocal(result)
        \/  IsShared(result)
    /\  VarExists(WorkGroupId(t)+1, result.name)
    /\  
        \/  IsLocal(pointer)
        \/  IsShared(pointer)
    /\  VarExists(WorkGroupId(t)+1, pointer.name)
    /\  IsLiteral(value)
    /\  LET resultVar == GetVar(WorkGroupId(t)+1, result.name)
            pointerVar == GetVar(WorkGroupId(t)+1, pointer.name)
        IN
            /\  Assignment(t, {Var(resultVar.scope, resultVar.name, pointerVar.value), Var(pointerVar.scope, pointerVar.name, value.value)})
    /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
    /\  UNCHANGED <<terminated, barrier>>

(* result and pointer are variable, compare and value are literal *)
OpAtomicCompareExchange(t, result, pointer, compare, value) ==
    /\  
        \/  IsLocal(result)
        \/  IsShared(result)
    /\  VarExists(WorkGroupId(t)+1, result.name)
    /\  
        \/  IsLocal(pointer)
        \/  IsShared(pointer)
    /\  VarExists(WorkGroupId(t)+1, pointer.name)
    /\  IsLiteral(compare)
    /\  IsLiteral(value)
    /\  LET resultVar == GetVar(WorkGroupId(t)+1, result.name)
            pointerVar == GetVar(WorkGroupId(t)+1, pointer.name)
        IN 
            IF pointerVar.value = compare.value THEN
                /\  Assignment(t, {Var(resultVar.scope, resultVar.name, pointerVar.value), Var(pointerVar.scope, pointerVar.name, value.value)})
            ELSE
                /\  Assignment(t, {Var(resultVar.scope, resultVar.name, pointerVar.value)})
    /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
    /\  UNCHANGED <<terminated, barrier>>

(* condition is an expression, trueLabel and falseLabel are integer representing pc *)
OpBranchConditional(t, condition, trueLabel, falseLabel) ==
    /\  IsLiteral(trueLabel)
    /\  IsLiteral(falseLabel)
    /\  IF EvalExpr(WorkGroupId(t)+1, condition) THEN
            /\  pc' = [pc EXCEPT ![t] = trueLabel.value]
        ELSE
            /\  pc' = [pc EXCEPT ![t] = falseLabel.value]
    /\  UNCHANGED <<terminated, barrier, liveVars>>


Terminate(t) ==
    /\  terminated' = [terminated EXCEPT ![t] = TRUE]
    /\  UNCHANGED <<pc, barrier, liveVars>>

Step(t) ==
    LET workgroupId == WorkGroupId(t)+1
    IN
        IF terminated[t] = FALSE THEN
            IF  ThreadInstructions[t][pc[t]] = "Terminate" THEN
                Terminate(t)
            ELSE IF ThreadInstructions[t][pc[t]] = "Assignment" THEN
                Assignment(t, {ThreadArguments[t][pc[t]][1]})
            ELSE IF ThreadInstructions[t][pc[t]] = "OpAtomicExchange" THEN
                OpAtomicExchange(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpAtomicCompareExchange" THEN
                OpAtomicCompareExchange(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3], ThreadArguments[t][pc[t]][4])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpAtomicLoad" THEN
                OpAtomicLoad(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpAtomicStore" THEN
                OpAtomicStore(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpBranchConditional" THEN
                OpBranchConditional(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE
                /\ UNCHANGED <<threadVars, liveVars>>
        ELSE 
            /\ UNCHANGED << threadVars, liveVars>>


(* This property ensures all the instructions in all threads are bounded to the instruction set *)
AllInstructionsWithinSet ==
    \A t \in Threads:
        \A ins \in DOMAIN ThreadInstructions[t]:
            ThreadInstructions[t][ins] \in InstructionSet

====
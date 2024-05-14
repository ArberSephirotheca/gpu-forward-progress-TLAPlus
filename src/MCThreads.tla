---- MODULE MCThreads ----
LOCAL INSTANCE Integers
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
\* LOCAL INSTANCE MCLayout
LOCAL INSTANCE TLC
VARIABLES pc, terminated, barrier, threadLocals, globalVars

(* Thread Configuration *)
INSTANCE  MCProgram


(* Thread variables and functions start here *)
threadVars == <<pc, terminated, barrier>>

InitThreadVars ==
    /\  pc = [t \in Threads |-> 1]
    /\  terminated = [t \in Threads |-> FALSE]
    /\  barrier = [t \in Threads |-> "NULL"]
    /\  threadLocals = [t \in Threads |-> {}]
    
InitThreads == 
    /\  InitThreadVars

ThreadsWithinWorkGroup(wgid) ==  {tid \in Threads : WorkGroupId(tid) = wgid}

ThreadsWithinSubgroup(sid, wgid) == {tid \in Threads : SubgroupId(tid) = sid} \intersect ThreadsWithinWorkGroup(wgid)

LowestPcWithinSubgroup(sid, wgid) == Min({pc[tid]: tid \in ThreadsWithinSubgroup(sid, wgid)})

MinThreadWithinWorkGroup(workgroupId) ==
    Min(ThreadsWithinWorkGroup(workgroupId))

cleanIntermediateVar(t) == 
    /\  LET workgroupId == WorkGroupId(t)+1
            currthreadLocals == threadLocals[WorkGroupId(t)+1]
        IN
            LET eliminatedVars == {currVar \in currthreadLocals : currVar.scope = "intermediate"}
            IN
                /\  threadLocals' =  [threadLocals EXCEPT ![workgroupId] = threadLocals[workgroupId] \ eliminatedVars]


 UpdateBarrier(tid, barrierState) ==
     /\  barrierState \in ScopeOperand
     /\  barrier' = [barrier EXCEPT ![tid] = barrierState]
    
 SubgroupBarrier(t) ==
     /\ IF barrier[t] = "subgroup" THEN \* already waiting at a subgroup barrier
            \* find all threads and their corresponding barrier state within the same subgroup
            LET affectedThreadsBarrier == {barrier[affectedThreads]: affectedThreads \in ThreadsWithinSubgroup(SubgroupId(t), WorkGroupId(t))}
                affectedThreads == ThreadsWithinSubgroup(SubgroupId(t), WorkGroupId(t))
            IN
                \* if all threads in the subgroup are waiting at the barrier, release them
                IF \A affected \in affectedThreadsBarrier : affected = "subgroup" THEN
                    \* release all barrier in the subgroup, marking barrier as null
                    /\  barrier' = [
                            tid \in Threads |->
                                IF tid \in affectedThreads THEN 
                                    "NULL" 
                                ELSE 
                                    barrier[tid]
                        ]
                    \* increment the program counter for all threads in the subgroup
                    /\  pc' = [
                            tid \in Threads |->
                                IF tid \in affectedThreads THEN 
                                    pc[tid] + 1
                                ELSE 
                                    pc[tid]
                        ]
                ELSE
                    \* else, do nothing as some threads are still not at the barrier
                    /\  UNCHANGED <<barrier, pc>> 
        ELSE
            \* set the barrier for the thread
            /\  UpdateBarrier(t, "subgroup") 
            /\  UNCHANGED <<pc>>
    /\  UNCHANGED <<threadLocals, globalVars, terminated>>


WorkgroupBarrier(t) ==
    /\  IF barrier[t] = "workgroup" THEN \* already waiting at a workgroup barrier
            LET affectedThreadsBarrier == {barrier[affectedThreads]: affectedThreads \in ThreadsWithinWorkGroup(WorkGroupId(t))}
                affectedThreads == ThreadsWithinWorkGroup(WorkGroupId(t))
            IN 
                IF \A affected \in affectedThreadsBarrier : affected = "workgroup" THEN \* if all threads in the workgroup are waiting at the barrier, release them
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
                    /\  UNCHANGED <<barrier, pc>> \* else, do nothing as some threads are still not at the barrier
        ELSE
            /\  UpdateBarrier(t, "workgroup") \* set the barrier for the thread
            /\  UNCHANGED <<pc>>
    /\  UNCHANGED <<threadLocals, globalVars, terminated>>

Assignment(t, vars) == 
    /\  LET workgroupId == WorkGroupId(t)+1
            AssGlobalVars == {var \in vars : var.scope = "global"}
            AssthreadLocals == {var \in vars : var.scope # "global"}
            currthreadLocals == threadLocals[WorkGroupId(t)+1]
        IN
            \* try to eliminated var with old value and intermediate var
            LET eliminatedthreadLocals == {currVar \in currthreadLocals : \E var \in vars: (currVar.name = var.name /\ currVar.scope = var.scope)}
                eliminatedGlobalVars == {currVar \in globalVars : \E var \in vars: (currVar.name = var.name /\ currVar.scope = var.scope)}
            IN
                /\  threadLocals' =  [threadLocals EXCEPT ![workgroupId] = (threadLocals[workgroupId] \ eliminatedthreadLocals) \union AssthreadLocals]
                /\  globalVars' = (globalVars \ eliminatedGlobalVars) \union AssGlobalVars

GetGlobalId(t, result) ==
    LET mangledResult == Mangle(t, result)
    IN
        /\
            \/  
                /\  IsVariable(mangledResult)
                /\  VarExists(WorkGroupId(t)+1, mangledResult)
            \/  IsIntermediate(mangledResult)
        /\  Assignment(t, {Var(mangledResult.scope, mangledResult.name, GlobalInvocationId(t))})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<terminated, barrier>>


OpAtomicLoad(t, result, pointer) ==
    LET mangledResult == Mangle(t, result)
        mangledPointer == Mangle(t, pointer)
    IN
        /\
            \/  
                /\  IsVariable(mangledResult)
                /\  VarExists(WorkGroupId(t)+1, mangledResult)
            \/  IsIntermediate(mangledResult)
        /\  IsVariable(mangledPointer)
        /\  VarExists(WorkGroupId(t)+1, mangledPointer)
        /\  IF IsIntermediate(mangledResult) THEN 
                LET pointerVar == GetVar(WorkGroupId(t)+1, mangledPointer)
                IN 
                    /\  Assignment(t, {Var("intermediate", mangledResult.name, pointerVar.value)})
            ELSE
                LET pointerVar == GetVar(WorkGroupId(t)+1, mangledPointer)
                    resultVar == GetVar(WorkGroupId(t)+1, mangledResult)
                IN
                    /\  Assignment(t, {Var(resultVar.scope, resultVar.name, pointerVar.value)})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<terminated, barrier>>

OpAtomicStore(t, pointer, value) == 
    LET mangledPointer == Mangle(t, pointer)
    IN
        /\  IsVariable(mangledPointer)
        /\  VarExists(WorkGroupId(t)+1, mangledPointer)
        /\  
            \/  IsLiteral(value)
            \/  IsExpression(value)
        /\  LET pointerVar == GetVar(WorkGroupId(t)+1, mangledPointer)
            IN
                /\  Assignment(t, {Var(pointerVar.scope, pointerVar.name, EvalExpr(t, WorkGroupId(t)+1, value))})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<terminated, barrier>>


OpGroupAll(t, result, predicate, scope) ==
    LET mangledResult == Mangle(t, result)
    IN
        /\  
            \/  /\  IsVariable(mangledResult)
                /\  VarExists(WorkGroupId(t)+1, mangledResult)
            \/  IsIntermediate(mangledResult)
        /\  scope \in ScopeOperand
        /\  IF scope = "subgroup" THEN
                /\  LET sthreads == ThreadsWithinSubgroup(SubgroupId(t), WorkGroupId(t))
                    IN
                        \* if there exists thread in the subgroup that has not reached the opgroupAll, set the barrier to current thread
                        /\  IF \E sthread \in sthreads: pc[sthread] # pc[t] THEN
                                /\  barrier' = [barrier EXCEPT ![t] = "subgroup"]
                                /\  UNCHANGED <<pc, threadLocals, globalVars>>
                            ELSE IF \A sthread \in sthreads: EvalExpr(sthread, WorkGroupId(t)+1, predicate) = TRUE THEN 
                                /\  Assignment(t, {Var(mangledResult.scope, Mangle(sthread, result).name, TRUE): sthread \in sthreads})
                                /\  barrier' = [\* release all barrier in the subgroup, marking barrier as null
                                        tid \in Threads |->
                                            IF tid \in sthreads THEN 
                                                "NULL" 
                                            ELSE 
                                                barrier[tid]
                                    ]
                                /\  pc' = [
                                        tid \in Threads |->
                                            IF tid \in sthreads THEN 
                                                pc[tid] + 1
                                            ELSE 
                                                pc[tid]
                                    ]
                            ELSE 
                                /\  Assignment(t, {Var(mangledResult.scope, Mangle(sthread, result).name, FALSE): sthread \in sthreads })
                                /\  barrier' = [\* release all barrier in the subgroup, marking barrier as null
                                        tid \in Threads |->
                                            IF tid \in sthreads THEN 
                                                "NULL" 
                                            ELSE 
                                                barrier[tid]
                                    ]
                                /\  pc' = [
                                        tid \in Threads |->
                                            IF tid \in sthreads THEN 
                                                pc[tid] + 1
                                            ELSE 
                                                pc[tid]
                                    ]
            ELSE IF scope = "workgroup" THEN 
                /\  LET wthreads == ThreadsWithinWorkGroup(WorkGroupId(t))
                    IN      \* if there is a thread that has not reached the opgroupAll, return false
                        /\  IF \E wthread \in wthreads: pc[wthread] # pc[t] THEN
                                /\  barrier' = [barrier EXCEPT ![t] = "workgroup"]
                                /\  UNCHANGED <<pc, threadLocals, globalVars>>
                            ELSE IF \A wthread \in wthreads: EvalExpr(wthread, WorkGroupId(t)+1, predicate) = TRUE THEN 
                                /\  Assignment(t, {Var(mangledResult.scope, Mangle(wthread, result).name, TRUE): wthread \in wthreads})
                                /\  barrier' = [\* release all barrier in the subgroup, marking barrier as null
                                        tid \in Threads |->
                                            IF tid \in wthreads THEN 
                                                "NULL" 
                                            ELSE 
                                                barrier[tid]
                                    ]
                                /\  pc' = [
                                        tid \in Threads |->
                                            IF tid \in wthreads THEN 
                                                pc[tid] + 1
                                            ELSE 
                                                pc[tid]
                                    ]
                            ELSE 
                                /\  Assignment(t, {Var(mangledResult.scope, Mangle(wthread, result).name, FALSE): wthread \in wthreads })
                                /\  barrier' = [\* release all barrier in the subgroup, marking barrier as null
                                        tid \in Threads |->
                                            IF tid \in wthreads THEN 
                                                "NULL" 
                                            ELSE 
                                                barrier[tid]
                                    ]
                                /\  pc' = [
                                        tid \in Threads |->
                                            IF tid \in wthreads THEN 
                                                pc[tid] + 1
                                            ELSE 
                                                pc[tid]
                                    ]
            ELSE
                /\  FALSE
        /\  UNCHANGED <<terminated>>


(* result and pointer are variable, value is literal *)

OpAtomicExchange(t, result, pointer, value) ==
    LET mangledResult == Mangle(t, result)
        mangledPointer == Mangle(t, pointer)
    IN
        /\  IsVariable(mangledResult)
        /\  VarExists(WorkGroupId(t)+1, mangledResult)
        /\  IsVariable(mangledPointer)
        /\  VarExists(WorkGroupId(t)+1, mangledPointer)
        /\  IsLiteral(value)
        /\  LET resultVar == GetVar(WorkGroupId(t)+1, mangledResult.name)
                pointerVar == GetVar(WorkGroupId(t)+1, mangledPointer.name)
            IN
                /\  Assignment(t, {Var(resultVar.scope, resultVar.name, pointerVar.value), Var(pointerVar.scope, pointerVar.name, value.value)})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<terminated, barrier>>

(* result and pointer are variable, compare and value are literal *)
OpAtomicCompareExchange(t, result, pointer, compare, value) ==
    LET mangledResult == Mangle(t, result)
        mangledPointer == Mangle(t, pointer)
    IN
        /\  IsVariable(mangledResult)
        /\  IsVariable(mangledPointer)
        /\  VarExists(WorkGroupId(t)+1, mangledPointer)
        /\  IsLiteral(compare)
        /\  IsLiteral(value)
        /\  LET pointerVar == GetVar(WorkGroupId(t)+1, mangledPointer)
            IN 
                IF pointerVar.value = compare.value THEN
                    /\  Assignment(t, {Var(mangledResult.scope, mangledResult.name, pointerVar.value), 
                            Var(pointerVar.scope, pointerVar.name, value.value)})
                ELSE
                    /\  Assignment(t, {Var(mangledResult.scope, mangledResult.name, pointerVar.value)})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<terminated, barrier>>

(* condition is an expression, trueLabel and falseLabel are integer representing pc *)
OpBranchConditional(t, condition, trueLabel, falseLabel) ==
    /\  IsLiteral(trueLabel)
    /\  IsLiteral(falseLabel)
    /\  IF EvalExpr(t, WorkGroupId(t)+1, condition) = TRUE THEN
            /\  pc' = [pc EXCEPT ![t] = trueLabel.value]
        ELSE
            /\  pc' = [pc EXCEPT ![t] = falseLabel.value]
    /\  UNCHANGED <<terminated, barrier, threadLocals, globalVars>>


Terminate(t) ==
    /\  terminated' = [terminated EXCEPT ![t] = TRUE]
    /\  UNCHANGED <<pc, barrier, threadLocals, globalVars>>

Step(t) ==
    LET workgroupId == WorkGroupId(t)+1
    IN
        IF terminated[t] = FALSE THEN
            IF  ThreadInstructions[t][pc[t]] = "Terminate" THEN
                Terminate(t)
            ELSE IF ThreadInstructions[t][pc[t]] = "Assignment" THEN
                /\  Assignment(t, {Mangle(t, ThreadArguments[t][pc[t]][1])})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<terminated, barrier>>
            ELSE IF ThreadInstructions[t][pc[t]] = "GetGlobalId" THEN
                GetGlobalId(t, ThreadArguments[t][pc[t]][1])
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
            ELSE IF ThreadInstructions[t][pc[t]] = "OpGroupAll" THEN
                OpGroupAll(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE
                /\ UNCHANGED <<threadVars, threadLocals, globalVars>>
        ELSE 
            /\ UNCHANGED << threadVars, threadLocals, globalVars>>


(* This property ensures all the instructions in all threads are bounded to the instruction set *)
AllInstructionsWithinSet ==
    \A t \in Threads:
        \A ins \in DOMAIN ThreadInstructions[t]:
            ThreadInstructions[t][ins] \in InstructionSet

====
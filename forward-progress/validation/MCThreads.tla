---- MODULE MCThreads ----
LOCAL INSTANCE Integers
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
\* LOCAL INSTANCE MCLayout
LOCAL INSTANCE TLC
VARIABLES pc, state, threadLocals, globalVars, CFG, MaxPathLength

(* Thread Configuration *)
INSTANCE  MCProgram

ThreadState == {"ready", "workgroup", "subgroup", "terminated"}

(* Thread variables and functions start here *)
threadVars == <<pc, state>>

InitThreadVars ==
    /\  pc = [t \in Threads |-> 1]
    /\  state = [t \in Threads |-> "ready"]
    /\  threadLocals = [t \in Threads |-> {}]
    
InitThreads == 
    /\  InitThreadVars

\* ThreadsWithinWorkGroup(wgid) ==  {tid \in Threads : WorkGroupId(tid) = wgid}

\* ThreadsWithinSubgroup(sid, wgid) == {tid \in Threads : SubgroupId(tid) = sid} \intersect ThreadsWithinWorkGroup(wgid)

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


 UpdateState(tid, State) ==
     /\  state' = [state EXCEPT ![tid] = State]
    

Assignment(t, vars) == 
    /\  LET workgroupId == WorkGroupId(t)+1
            AssGlobalVars == {var \in vars : var.scope = "global" \/ var.scope = "shared"} 
            AssthreadLocals == {var \in vars : var.scope # "global" /\ var.scope # "shared"}
            currthreadLocals == threadLocals[WorkGroupId(t)+1]
        IN
            \* try to eliminated var with old value and intermediate var
            LET eliminatedthreadLocals == {currVar \in currthreadLocals : \E var \in vars: (currVar.name = var.name /\ currVar.scope = var.scope)}
                eliminatedGlobalVars == {currVar \in globalVars : \E var \in vars: (currVar.name = var.name /\ currVar.scope = var.scope)}
            IN
                /\  threadLocals' =  [threadLocals EXCEPT ![workgroupId] = (threadLocals[workgroupId] \ eliminatedthreadLocals) \union AssthreadLocals]
                /\  globalVars' = (globalVars \ eliminatedGlobalVars) \union AssGlobalVars

\* This is the inner helper function to return the array with updated element. It does not change the next state of the variable
ChangeElementAt(var, index, value) ==
        Var(var.scope, var.name, [currentIndex \in DOMAIN var.value |-> IF currentIndex = index THEN value ELSE var.value[currentIndex] ], var.index)


OpEqual(t, var, operand1, operand2) ==
    LET workgroupId == WorkGroupId(t)+1
        \* mangledOperand1 == Mangle(t, operand1)
        \* mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workgroupId, operand1)
                operand2Val == GetVal(workgroupId, operand2)
            IN
                /\  IF operand1Val = operand2Val THEN
                        Assignment(t, {Var(var.scope, var.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(var.scope, var.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars, CFG, MaxPathLength>>


OpNotEqual(t, var, operand1, operand2) ==
    LET workgroupId == WorkGroupId(t)+1
        \* mangledOperand1 == Mangle(t, operand1)
        \* mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workgroupId, operand1)
                operand2Val == GetVal(workgroupId, operand2)
            IN
                /\  IF operand1Val # operand2Val THEN
                        Assignment(t, {Var(var.scope, var.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(var.scope, var.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars, CFG, MaxPathLength>>


OpLess(t, var, operand1, operand2) ==
    LET workgroupId == WorkGroupId(t)+1
        \* mangledOperand1 == Mangle(t, operand1)
        \* mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workgroupId, operand1)
                operand2Val == GetVal(workgroupId, operand2)
            IN
                /\  IF operand1Val < operand2Val THEN
                        Assignment(t, {Var(var.scope, var.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(var.scope, var.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars, CFG, MaxPathLength>>

OpLessOrEqual(t, var, operand1, operand2) ==
    LET workgroupId == WorkGroupId(t)+1
        \* mangledOperand1 == Mangle(t, operand1)
        \* mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workgroupId, operand1)
                operand2Val == GetVal(workgroupId, operand2)
            IN
                /\  IF operand1Val <= operand2Val THEN
                        Assignment(t, {Var(var.scope, var.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(var.scope, var.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars, CFG, MaxPathLength>>

OpGreater(t, var, operand1, operand2) ==
    LET workgroupId == WorkGroupId(t)+1
        \* mangledOperand1 == Mangle(t, operand1)
        \* mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workgroupId, operand1)
                operand2Val == GetVal(workgroupId, operand2)
            IN
                /\  IF operand1Val > operand2Val THEN
                        Assignment(t, {Var(var.scope, var.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(var.scope, var.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars, CFG, MaxPathLength>>

OpGreaterOrEqual(t, var, operand1, operand2) ==
    LET workgroupId == WorkGroupId(t)+1
        \* mangledOperand1 == Mangle(t, operand1)
        \* mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workgroupId, operand1)
                operand2Val == GetVal(workgroupId, operand2)
            IN
                /\  IF operand1Val >= operand2Val THEN
                        Assignment(t, {Var(var.scope, var.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(var.scope, var.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars, CFG, MaxPathLength>>

OpAdd(t, var, operand1, operand2) ==
    LET workgroupId == WorkGroupId(t)+1
        \* mangledOperand1 == Mangle(t, operand1)
        \* mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workgroupId, operand1)
                operand2Val == GetVal(workgroupId, operand2)
            IN
                Assignment(t, {Var(var.scope, var.name, operand1Val + operand2Val, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars, CFG, MaxPathLength>>

OpSub(t, var, operand1, operand2) ==
    LET workgroupId == WorkGroupId(t)+1
        \* mangledOperand1 == Mangle(t, operand1)
        \* mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workgroupId, operand1)
                operand2Val == GetVal(workgroupId, operand2)
            IN
                Assignment(t, {Var(var.scope, var.name, operand1Val - operand2Val, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars, CFG, MaxPathLength>>

OpMul(t, var, operand1, operand2) ==
    LET workgroupId == WorkGroupId(t)+1
        \* mangledOperand1 == Mangle(t, operand1)
        \* mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workgroupId, operand1)
                operand2Val == GetVal(workgroupId, operand2)
            IN
                Assignment(t, {Var(var.scope, var.name, operand1Val * operand2Val, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars, CFG, MaxPathLength>>


GetGlobalId(t, result) ==
    LET mangledResult == Mangle(t, result)
    IN
        /\
            \/  
                /\  IsVariable(result)
                /\  VarExists(WorkGroupId(t)+1, result)
            \/  IsIntermediate(result)
        /\  Assignment(t, {Var(result.scope, result.name, GlobalInvocationId(t), Index(-1))})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<state, MaxPathLength>>


\* It does not handle the situation where result is an index to array
OpAtomicLoad(t, result, pointer) ==
    LET mangledResult == Mangle(t, result)
        mangledPointer == Mangle(t, pointer)
    IN
        /\
            \/  
                /\  IsVariable(result)
                \* /\  VarExists(WorkGroupId(t)+1, mangledResult)
            \/  IsIntermediate(result)
        /\  IsVariable(pointer)
        /\  VarExists(WorkGroupId(t)+1, pointer)
        /\  IF IsIntermediate(mangledResult) THEN 
                LET pointerVar == GetVar(WorkGroupId(t)+1, pointer)
                    evaluatedIndex == EvalExpr(t, WorkGroupId(t)+1, pointer.index)
                IN 
                    /\
                        IF evaluatedIndex > 0 THEN 
                            Assignment(t, {Var("intermediate", result.name, pointerVar.value[evaluatedIndex], Index(-1))})
                        ELSE
                            Assignment(t, {Var("intermediate", result.name, pointerVar.value, Index(-1))})
            ELSE
                LET pointerVar == GetVar(WorkGroupId(t)+1, pointer)
                    \* resultVar == GetVar(WorkGroupId(t)+1, mangledResult)
                    evaluatedPointerIndex == EvalExpr(t, WorkGroupId(t)+1, pointer.index)
                    evaluatedResultIndex == EvalExpr(t, WorkGroupId(t)+1, result.index)
                IN
                    /\
                        IF evaluatedPointerIndex > 0 /\ evaluatedResultIndex > 0 THEN
                            \* Assignment(t, {ChangeElementAt(resultVar, evaluatedResultIndex, pointerVar.value[evaluatedPointerIndex])})
                            Assignment(t, {ChangeElementAt(result, evaluatedResultIndex, pointerVar.value[evaluatedPointerIndex])})
                        ELSE IF evaluatedPointerIndex > 0 THEN
                            \* Assignment(t, {Var(resultVar.scope, resultVar.name, pointerVar.value[evaluatedPointerIndex], Index(-1))})
                            Assignment(t, {Var(result.scope, result.name, pointerVar.value[evaluatedPointerIndex], Index(-1))})
                        ELSE IF evaluatedResultIndex > 0 THEN
                            \* Assignment(t, {ChangeElementAt(resultVar, evaluatedResultIndex, pointerVar.value)})
                            Assignment(t, {ChangeElementAt(result, evaluatedResultIndex, pointerVar.value)})
                        ELSE
                            \* Assignment(t, {Var(resultVar.scope, resultVar.name, pointerVar.value, Index(-1))})  
                            Assignment(t, {Var(result.scope, result.name, pointerVar.value, Index(-1))})  
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<state, CFG, MaxPathLength>>

OpAtomicStore(t, pointer, value) == 
    LET mangledPointer == Mangle(t, pointer)
    IN
        /\  IsVariable(pointer)
        /\  VarExists(WorkGroupId(t)+1, pointer)
        /\  LET pointerVar == GetVar(WorkGroupId(t)+1, pointer)
                evaluatedPointerIndex == EvalExpr(t, WorkGroupId(t)+1, pointer.index)
            IN
                /\
                    IF evaluatedPointerIndex > 0 THEN 
                        Assignment(t, {ChangeElementAt(pointerVar, evaluatedPointerIndex, EvalExpr(t, WorkGroupId(t)+1, value))})
                    ELSE
                        Assignment(t, {Var(pointerVar.scope, pointerVar.name, EvalExpr(t, WorkGroupId(t)+1, value), pointerVar.index)})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<state, CFG, MaxPathLength>>

OpAtomicAdd(t, pointer) == 
    LET mangledPointer == Mangle(t, pointer)
    IN
        /\  IsVariable(pointer)
        /\  VarExists(WorkGroupId(t)+1, pointer)
        /\  IsArray(pointer) = FALSE
        /\  LET pointerVar == GetVar(WorkGroupId(t)+1, pointer)
                evaluatedPointerIndex == EvalExpr(t, WorkGroupId(t)+1, pointer.index)
            IN
                /\
                    IF evaluatedPointerIndex > 0 THEN 
                        Assignment(t, {ChangeElementAt(pointerVar, evaluatedPointerIndex, pointerVar.value[evaluatedPointerIndex] + 1)})
                    ELSE  
                        Assignment(t, {Var(pointerVar.scope, pointerVar.name, pointerVar.value + 1, pointerVar.index)})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<state, CFG, MaxPathLength>>


OpAtomicSub(t, pointer) == 
    LET mangledPointer == Mangle(t, pointer)
    IN
        /\  IsVariable(pointer)
        /\  VarExists(WorkGroupId(t)+1, pointer)
        /\  LET pointerVar == GetVar(WorkGroupId(t)+1, pointer)
                evaluatedPointerIndex == EvalExpr(t, WorkGroupId(t)+1, pointer.index)
            IN
                /\
                    IF evaluatedPointerIndex > 0 THEN 
                        Assignment(t, {ChangeElementAt(pointerVar, evaluatedPointerIndex, pointerVar.value[evaluatedPointerIndex] - 1)})
                    ELSE  
                        Assignment(t, {Var(pointerVar.scope, pointerVar.name, pointerVar.value - 1, pointerVar.index)})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<state, CFG, MaxPathLength>>

 OpControlBarrier(t, scope) ==
    IF scope = "subgroup" THEN \* already waiting at a subgroup barrier
        \* find all threads and their corresponding barrier state within the same subgroup
        LET sthreads == ThreadsWithinSubgroup(SubgroupId(t), WorkGroupId(t))
            currentTangle == FindCurrentBlock(CFG.node, pc[t]).tangle[WorkGroupId(t) + 1]
        IN
            IF \E sthread \in sthreads: sthread  \notin currentTangle THEN 
                Print("UB: All threads within subgroup must converge at current block", FALSE)
            \* if there exists thread in the subgroup that has not reached the subgroup barrier, set the barrier to current thread
            ELSE IF \E sthread \in sthreads: pc[sthread] # pc[t] THEN
                /\  state' = [state EXCEPT ![t] = "subgroup"]
                /\  UNCHANGED <<pc, threadLocals, globalVars, CFG, MaxPathLength>>
            \* if all threads in the subgroup are waiting at the barrier, release them
            ELSE 
                \* release all barrier in the subgroup, marking state as ready
                /\  state' = [
                        tid \in Threads |->
                            IF tid \in sthreads THEN 
                                "ready" 
                            ELSE 
                                state[tid]
                    ]
                \* increment the program counter for all threads in the subgroup
                /\  pc' = [
                        tid \in Threads |->
                            IF tid \in sthreads THEN 
                                pc[tid] + 1
                            ELSE 
                                pc[tid]
                    ]
                /\  UNCHANGED <<threadLocals, globalVars, CFG, MaxPathLength>>

    ELSE IF scope = "workgroup" THEN \* already waiting at a workgroup barrier
        LET sthreads == ThreadsWithinSubgroup(SubgroupId(t), WorkGroupId(t))
        IN
            \* if there exists thread in the subgroup that has not reached the subgroup barrier, set the barrier to current thread
            IF \E sthread \in sthreads: pc[sthread] # pc[t] THEN
                /\  state' = [state EXCEPT ![t] = "workgroup"]
                /\  UNCHANGED <<pc, threadLocals, globalVars, CFG, MaxPathLength>>
            \* if all threads in the subgroup are waiting at the barrier, release them
            ELSE 
                \* release all barrier in the subgroup, marking state as ready
                /\  state' = [
                        tid \in Threads |->
                            IF tid \in sthreads THEN 
                                "ready" 
                            ELSE 
                                state[tid]
                    ]
                \* increment the program counter for all threads in the subgroup
                /\  pc' = [
                        tid \in Threads |->
                            IF tid \in sthreads THEN 
                                pc[tid] + 1
                            ELSE 
                                pc[tid]
                    ]
                /\  UNCHANGED <<threadLocals, globalVars, CFG, MaxPathLength>>
    ELSE    
        FALSE


\* zheyuan: add assertion to check if the all threads within subgroup converge at current block because it is UB if not
OpGroupAll(t, result, predicate, scope) ==
    LET mangledResult == Mangle(t, result)
    IN
        /\  
            \/  /\  IsVariable(result)
                /\  VarExists(WorkGroupId(t)+1, result)
            \/  IsIntermediate(result)
        /\  scope \in ScopeOperand
        /\  IF scope = "subgroup" THEN
                /\  LET sthreads == ThreadsWithinSubgroup(SubgroupId(t), WorkGroupId(t))
                        currentTangle == FindCurrentBlock(CFG.node, pc[t]).tangle[WorkGroupId(t) + 1]
                    IN
                        IF \E sthread \in sthreads: sthread  \notin currentTangle THEN 
                                Print("UB: All threads within subgroup must converge at current block", FALSE)
                        \* if there exists thread in the subgroup that has not reached the opgroupAll, set the barrier to current thread
                        ELSE IF \E sthread \in sthreads: pc[sthread] # pc[t] THEN
                            /\  state' = [state EXCEPT ![t] = "subgroup"]
                            /\  UNCHANGED <<pc, threadLocals, globalVars, CFG, MaxPathLength>>
                        ELSE IF \A sthread \in sthreads: EvalExpr(sthread, WorkGroupId(t)+1, predicate) = TRUE THEN 
                            /\  Assignment(t, {Var(result.scope, Mangle(sthread, result).name, TRUE, Index(-1)): sthread \in sthreads})
                            /\  state' = [\* release all barrier in the subgroup, marking barrier as ready
                                    tid \in Threads |->
                                        IF tid \in sthreads THEN 
                                            "ready" 
                                        ELSE 
                                            state[tid]
                                ]
                            /\  pc' = [
                                    tid \in Threads |->
                                        IF tid \in sthreads THEN 
                                            pc[tid] + 1
                                        ELSE 
                                            pc[tid]
                                ]
                        ELSE 
                            /\  Assignment(t, {Var(result.scope, Mangle(sthread, result).name, FALSE, Index(-1)): sthread \in sthreads })
                            /\  state' = [\* release all barrier in the subgroup, marking barrier as ready
                                    tid \in Threads |->
                                        IF tid \in sthreads THEN 
                                            "ready" 
                                        ELSE 
                                            state[tid]
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
                                /\  state' = [state EXCEPT ![t] = "workgroup"]
                                /\  UNCHANGED <<pc, threadLocals, globalVars, CFG, MaxPathLength>>
                            ELSE IF \A wthread \in wthreads: EvalExpr(wthread, WorkGroupId(t)+1, predicate) = TRUE THEN 
                                /\  Assignment(t, {Var(result.scope, Mangle(wthread, result).name, TRUE, Index(-1)): wthread \in wthreads})
                                /\  state' = [\* release all barrier in the subgroup, marking barrier as ready
                                        tid \in Threads |->
                                            IF tid \in wthreads THEN 
                                                "ready" 
                                            ELSE 
                                                state[tid]
                                    ]
                                /\  pc' = [
                                        tid \in Threads |->
                                            IF tid \in wthreads THEN 
                                                pc[tid] + 1
                                            ELSE 
                                                pc[tid]
                                    ]
                            ELSE 
                                /\  Assignment(t, {Var(result.scope, Mangle(wthread, result).name, FALSE, Index(-1)): wthread \in wthreads })
                                /\  state' = [\* release all barrier in the subgroup, marking barrier as ready
                                        tid \in Threads |->
                                            IF tid \in wthreads THEN 
                                                "ready" 
                                            ELSE 
                                                state[tid]
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


(* result and pointer are variable, value is literal *)

OpAtomicExchange(t, result, pointer, value) ==
    LET mangledResult == Mangle(t, result)
        mangledPointer == Mangle(t, pointer)
    IN
        /\  IsVariable(result)
        \* /\  VarExists(WorkGroupId(t)+1, mangledResult)
        /\  IsVariable(pointer)
        /\  VarExists(WorkGroupId(t)+1, pointer)
        /\  
            \/  IsLiteral(value) 
            \/  IsExpression(value)
        /\  LET pointerVar == GetVar(WorkGroupId(t)+1, pointer)
                \* resultVar == GetVar(WorkGroupId(t)+1, mangledResult)
                evaluatedResultIndex == EvalExpr(t, WorkGroupId(t)+1, result.index)
                evaluatedPointerIndex == EvalExpr(t, WorkGroupId(t)+1, pointer.index)
                evaluatedValue == EvalExpr(t, WorkGroupId(t)+1, value)
            IN
                IF evaluatedResultIndex > 0 /\ evaluatedPointerIndex > 0 THEN
                    \* Assignment(t, {ChangeElementAt(resultVar, evaluatedResultIndex, pointerVar.value[evaluatedPointerIndex]), ChangeElementAt(pointerVar, evaluatedPointerIndex, evaluatedValue)})
                    Assignment(t, {ChangeElementAt(result, evaluatedResultIndex, pointerVar.value[evaluatedPointerIndex]), ChangeElementAt(pointerVar, evaluatedPointerIndex, evaluatedValue)})
                ELSE IF evaluatedResultIndex > 0 THEN
                    \* Assignment(t, {ChangeElementAt(resultVar, evaluatedResultIndex, pointerVar.value), Var(pointerVar.scope, pointerVar.name, evaluatedValue, pointerVar.index)})
                    Assignment(t, {ChangeElementAt(result, evaluatedResultIndex, pointerVar.value), Var(pointerVar.scope, pointerVar.name, evaluatedValue, pointerVar.index)})
                ELSE IF evaluatedPointerIndex > 0 THEN
                    \* Assignment(t, {Var(resultVar.scope, resultVar.name, pointerVar.value[evaluatedPointerIndex], resultVar.index), ChangeElementAt(pointerVar, evaluatedPointerIndex, evaluatedValue)})
                    Assignment(t, {Var(result.scope, result.name, pointerVar.value[evaluatedPointerIndex], result.index), ChangeElementAt(pointerVar, evaluatedPointerIndex, evaluatedValue)})
                ELSE
                    \* Assignment(t, {Var(resultVar.scope, resultVar.name, pointerVar.value, resultVar.index), Var(pointerVar.scope, pointerVar.name, evaluatedValue, pointerVar.index)})
                    Assignment(t, {Var(result.scope, result.name, pointerVar.value, result.index), Var(pointerVar.scope, pointerVar.name, evaluatedValue, pointerVar.index)})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<state, CFG, MaxPathLength>>

(* result and pointer are variable, compare and value are literal *)
OpAtomicCompareExchange(t, result, pointer, compare, value) ==
    LET mangledResult == Mangle(t, result)
        mangledPointer == Mangle(t, pointer)
    IN
        /\  IsVariable(result)
        /\  IsVariable(pointer)
        /\  VarExists(WorkGroupId(t)+1, pointer)
        /\  IsLiteral(compare)
        /\  
            \/  IsLiteral(value)
            \/  IsExpression(value)
        /\  LET pointerVar == GetVar(WorkGroupId(t)+1, pointer)
                resultVar == GetVar(WorkGroupId(t)+1, result)
                evaluatedPointerIndex == EvalExpr(t, WorkGroupId(t)+1, pointer.index)
                evaluatedResultIndex == EvalExpr(t, WorkGroupId(t)+1, result.index)
                evaluatedValue == EvalExpr(t, WorkGroupId(t)+1, value)
            IN 
                IF pointerVar.value = compare.value THEN
                    /\  
                        IF evaluatedResultIndex > 0 /\ evaluatedPointerIndex > 0 THEN
                            Assignment(t, {ChangeElementAt(resultVar, evaluatedResultIndex, pointerVar.value[evaluatedPointerIndex]), ChangeElementAt(pointerVar, evaluatedPointerIndex, evaluatedValue)})
                        ELSE IF evaluatedResultIndex > 0 THEN
                            Assignment(t, {ChangeElementAt(resultVar, evaluatedResultIndex, pointerVar.value), Var(pointerVar.scope, pointerVar.name, evaluatedValue, pointerVar.index)})
                        ELSE IF evaluatedPointerIndex > 0 THEN
                            Assignment(t, {Var(resultVar.scope, resultVar.name, pointerVar.value[evaluatedPointerIndex], resultVar.index), ChangeElementAt(pointerVar, evaluatedPointerIndex, evaluatedValue)})
                        ELSE
                            Assignment(t, {Var(resultVar.scope, resultVar.name, pointerVar.value, resultVar.index), Var(pointerVar.scope, pointerVar.name, evaluatedValue, pointerVar.index)})

                ELSE
                    /\
                        IF evaluatedResultIndex > 0 /\ evaluatedPointerIndex > 0 THEN
                            Assignment(t, {ChangeElementAt(resultVar, evaluatedResultIndex, pointerVar.value[evaluatedPointerIndex])})
                        ELSE IF evaluatedResultIndex > 0 THEN
                            Assignment(t, {ChangeElementAt(resultVar, evaluatedResultIndex, pointerVar.value)})
                        ELSE IF evaluatedPointerIndex > 0 THEN
                            Assignment(t, {Var(resultVar.scope, resultVar.name, pointerVar.value[evaluatedPointerIndex], resultVar.index)})
                        ELSE
                            Assignment(t, {Var(resultVar.scope, resultVar.name, pointerVar.value, resultVar.index)})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<state, CFG, MaxPathLength>>


(* zheyuan chen: invocation is escaped from reconvergence if: 
1. The invocation executes OpTerminateInvocation or OpKill.
2. The last non-demoted, non-terminated invocation in the invocation's quad executes OpDemoteToHelperInvocation, OpTerminateInvocation, or OpKill.
3. The invocation executes OpReturn or OpReturnValue. Escaping in this manner only affects relations in the current function.
4. Executing OpBranch or OpBranchConditional causes an invocation to branch to the Merge Block or Continue Target for a merge instruction instance that strictly dominates I.
*)
OpBranch(t, label) ==
    /\  LET curBlock == FindCurrentBlock(CFG.node, pc[t])
            targetBlock == FindBlockbyOpLabelIdx(CFG.node, GetVal(-1, label))
            labelVal == GetVal(-1, label)
            workGroupId == WorkGroupId(t)+1
        IN
            CFG' = GenerateCFG(BranchUpdate(workGroupId, t, curBlock.tangle[workGroupId], {labelVal}, labelVal), CFG.edge) 
        
    /\ pc' = [pc EXCEPT ![t] = GetVal(-1, label)]
    /\  UNCHANGED <<state, threadLocals, globalVars, MaxPathLength>>

(* condition is an expression, trueLabel and falseLabel are integer representing pc *)
OpBranchConditional(t, condition, trueLabel, falseLabel) ==
    /\  IsLiteral(trueLabel)
    /\  IsLiteral(falseLabel)
    /\  LET curBlock == FindCurrentBlock(CFG.node, pc[t])
            trueLabelVal == GetVal(-1, trueLabel)
            falseLabelVal == GetVal(-1, falseLabel)
            workGroupId == WorkGroupId(t)+1
        IN
            IF EvalExpr(t, WorkGroupId(t)+1, condition) = TRUE THEN
                /\  CFG' = GenerateCFG(BranchUpdate(workGroupId, t, FindCurrentBlock(CFG.node, pc[t]).tangle[workGroupId], {trueLabelVal, falseLabelVal}, trueLabelVal), CFG.edge)
                /\  pc' = [pc EXCEPT ![t] = GetVal(-1, trueLabel)]
            ELSE
                /\  CFG' = GenerateCFG(BranchUpdate(workGroupId, t, FindCurrentBlock(CFG.node, pc[t]).tangle[workGroupId], {trueLabelVal, falseLabelVal}, falseLabelVal), CFG.edge)
                /\  pc' = [pc EXCEPT ![t] = GetVal(-1, falseLabel)]
    /\  UNCHANGED <<state, threadLocals, globalVars, MaxPathLength>>

OpLabel(t, label) ==
    /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
    /\  UNCHANGED <<state, threadLocals, globalVars, CFG, MaxPathLength>>

(* structured loop, must immediately precede block termination instruction, which means it must be second-to-last instruction in its block *)
OpLoopMerge(t, mergeLabel, continueTarget) ==
    \* because the merge instruction must be the second to last instruction in the block, we can find the currren block by looking at the termination instruction
    LET currBlock == FindBlockByTerminationIns(CFG.node, pc[t]+1)
        workGroupId == WorkGroupId(t)+1
    IN 
        /\  CFG' = GenerateCFG(MergeUpdate(workGroupId, currBlock.opLabelIdx, currBlock.tangle[workGroupId], {GetVal(-1, mergeLabel), GetVal(-1, continueTarget)}), CFG.edge)
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<state, threadLocals, globalVars, MaxPathLength>>

(* structured switch/if, must immediately precede block termination instruction, which means it must be second-to-last instruction in its block  *)
OpSelectionMerge(t, mergeLabel) ==
    \* because the merge instruction must be the second to last instruction in the block, we can find the currren block by looking at the termination instruction
    LET currBlock == FindBlockByTerminationIns(CFG.node, pc[t]+1)
        workGroupId == WorkGroupId(t)+1
    IN
        /\  CFG' = GenerateCFG(MergeUpdate(workGroupId, currBlock.opLabelIdx, currBlock.tangle[workGroupId], {GetVal(-1, mergeLabel)}), CFG.edge)
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<state, threadLocals, globalVars, MaxPathLength>>

\* zheyuan chen: update tangle
Terminate(t) ==
    LET workgroupId == WorkGroupId(t)+1
    IN
        /\  CFG' = GenerateCFG(TerminateUpdate(workgroupId, t, FindBlockByTerminationIns(CFG.node, pc[t]).opLabelIdx), CFG.edge)
        /\  state' = [state EXCEPT ![t] = "terminated"]
        /\  UNCHANGED <<pc, threadLocals, globalVars, MaxPathLength>>

ExecuteInstruction(t) ==
    LET workgroupId == WorkGroupId(t)+1
    IN
        IF state[t] # "terminated" THEN
            IF  ThreadInstructions[t][pc[t]] = "Terminate" THEN
                Terminate(t)
            ELSE IF ThreadInstructions[t][pc[t]] = "Assignment" THEN
                /\  Assignment(t, {ThreadArguments[t][pc[t]][1]})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, CFG, MaxPathLength>>
            ELSE IF ThreadInstructions[t][pc[t]] = "GetGlobalId" THEN
                GetGlobalId(t, ThreadArguments[t][pc[t]][1])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpAtomicAdd" THEN
                OpAtomicAdd(t, ThreadArguments[t][pc[t]][1])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpAtomicSub" THEN
                OpAtomicSub(t, ThreadArguments[t][pc[t]][1])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpEqual" THEN
                OpEqual(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpNotEqual" THEN
                OpNotEqual(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpLess" THEN
                OpLess(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpLessOrEqual" THEN
                OpLessOrEqual(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpGreater" THEN
                OpGreater(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpGreaterOrEqual" THEN
                OpGreaterOrEqual(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpAdd" THEN
                OpAdd(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpSub" THEN
                OpSub(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpAtomicExchange" THEN
                OpAtomicExchange(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpAtomicCompareExchange" THEN
                OpAtomicCompareExchange(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3], ThreadArguments[t][pc[t]][4])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpAtomicLoad" THEN
                OpAtomicLoad(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpAtomicStore" THEN
                OpAtomicStore(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpBranch" THEN
                OpBranch(t, ThreadArguments[t][pc[t]][1])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpBranchConditional" THEN
                OpBranchConditional(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            \* ELSE IF ThreadInstructions[t][pc[t]] = "OpSwitch" THEN
            \*     OpSwitch(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpControlBarrier" THEN
                OpControlBarrier(t, ThreadArguments[t][pc[t]][1])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpGroupAll" THEN
                OpGroupAll(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpLoopMerge" THEN
                OpLoopMerge(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpSelectionMerge" THEN
                OpSelectionMerge(t, ThreadArguments[t][pc[t]][1])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpLabel" THEN
                OpLabel(t, ThreadArguments[t][pc[t]][1])
            ELSE
                FALSE
        ELSE 
            /\ UNCHANGED << threadVars, threadLocals, globalVars, CFG, MaxPathLength>>


(* This property ensures all the instructions in all threads are bounded to the instruction set *)
AllInstructionsWithinSet ==
    \A t \in Threads:
        \A ins \in DOMAIN ThreadInstructions[t]:
            ThreadInstructions[t][ins] \in InstructionSet

AllThreadStatesAreBounded ==
    \A t \in Threads:
        state[t] \in ThreadState

(* This property ensures that the program counter of all threads are bounded *)

====
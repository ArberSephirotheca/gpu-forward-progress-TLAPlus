---- MODULE MCThreads ----
LOCAL INSTANCE Integers
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
\* LOCAL INSTANCE MCLayout
LOCAL INSTANCE TLC
VARIABLES pc, state, threadLocals, globalVars, DynamicNodeSet, globalCounter, snapShotMap

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

newSnapShot(localPc, localState, localThreadLocals, localGlobalVars, dynamicNode, dynamicNodeSet) ==
    [
        pc |-> localPc,
        state |-> localState,
        threadLocals |-> localThreadLocals,
        globalVars |-> localGlobalVars,
        dynamicNode |-> dynamicNode,
        dynamicNodeSet |-> dynamicNodeSet
    ]

RemoveId(dynamicNode) == [dynamicNode EXCEPT !.iterationVec = <<>>]

\* default that has no meaningful value
\* InitSnapShotMap ==
\*     LET newDBIds == {db.labelIdx : db \in DynamicNodeSet} IN
\*         snapShotMap = [ id \in newDBIds |-> newSnapShot(<<>>, <<>>, <<>>, {})]

InitSnapShotMap ==
     LET newDBIds == {db.labelIdx : db \in DynamicNodeSet} IN
         snapShotMap = { newSnapShot(<<>>, <<>>, <<>>, {}, RemoveId(db), DynamicNodeSet) : db \in DynamicNodeSet}

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
    
\* Update the state of the thread when there is an update in the tangle, especially if a thread is removed from the tangle
\* This function tries to update the state of the thread to "ready" if it is waiting at tangled instruction and all threads within the subgroup have reached the same block
\* within the tangle are having the same pc number. Otherwise, it keeps the state as it is.
\* StateUpdate(wgid, t, newBlocks) ==
\*     [thread \in Threads |-> 
\*         IF \E i \in 1..Len(newBlocks) : 
\*             /\ state[thread] # "terminated"
\*             /\ state[thread] # "ready"
\*             /\ thread \in newBlocks[i].tangle[wgid] 
\*             /\ \A tid \in newBlocks[i].tangle[wgid] : pc[tid] = pc[thread] /\ ThreadInstructions[1][pc[tid]] \in TangledInstructionSet /\ state[tid] = state[thread]
\*         THEN 
\*             "ready"
\*         ELSE
\*             state[thread]
\*     ]

\* Update the state of the thread when there is an update in the tangle, especially if a thread is removed from the tangle
\* This function tries to update the state of the thread to "ready" if it is waiting at tangled instruction and all threads within the subgroup have reached the same block
\* within the tangle are having the same pc number. Otherwise, it keeps the state as it is.
StateUpdate(wgid, t, newDBSet) ==
    [thread \in Threads |-> 
        IF \E DB \in newDBSet :
            /\ state[thread] # "terminated"
            /\ state[thread] # "ready"
            /\ thread \in DB.currentThreadSet[wgid]
            /\ \A tid \in DB.currentThreadSet[wgid] : pc[tid] = pc[thread] /\ ThreadInstructions[1][pc[tid]] \in TangledInstructionSet /\ state[tid] = state[thread]
            /\ DB.unknownSet[wgid] = {}
        THEN 
            "ready"
        ELSE
            state[thread]
    ]

\* InsertMultipleSnapShots(map, snapshots) ==
\*     [blockIdx \in DOMAIN map \cup DOMAIN snapshots |-> 
\*         IF blockIdx \in DOMAIN snapshots 
\*         THEN snapshots[blockIdx] 
\*         ELSE map[blockIdx]]

InsertMultipleSnapShots(map, snapshots) ==
    map \cup snapshots

\* InsertSnapShot(map, snapshot, blockIdx) ==
\*     [map EXCEPT ![blockIdx] = snapshot]


\* SnapShotUpdate(newDBSet, newState, t, localPc) ==
\*         \* get set of newly created DBs
\*         LET newDBs == newDBSet \ DynamicNodeSet
\*             newDBIds == {db.labelIdx : db \in newDBs}
\*             snapShots == [id \in newDBIds |-> newSnapShot(localPc, newState, threadLocals, globalVars)]
\*         IN
\*             InsertMultipleSnapShots(snapShotMap, snapShots)

SnapShotUpdate(newDBSet, newState, t, localPc) ==
        \* get set of newly created DBs
        LET newDBs == newDBSet \ DynamicNodeSet
            newDBIds == {db.labelIdx : db \in newDBs}
            snapShots == {newSnapShot(localPc, newState, threadLocals, globalVars, RemoveId(db), newDBSet) : db \in newDBs}
        IN
            InsertMultipleSnapShots(snapShotMap, snapShots)

\* MeaningfulUpdate(newSnapShotMap, oldSnapShotMap) ==
\*     /\ \E blockIdx \in DOMAIN newSnapShotMap : oldSnapShotMap[blockIdx] /= newSnapShotMap[blockIdx]

Normalize(snapshot) ==
    [
        pc |-> snapshot["pc"],
        state |-> snapshot["state"],
        threadLocals |-> snapshot["threadLocals"],
        globalVars |-> snapshot["globalVars"],
        dynamicNode |-> snapshot["dynamicNode"]
    ]

MeaningfulUpdate(localPc, newState, oldSnapShotMap, newDBSet) ==
    \A db \in newDBSet \ DynamicNodeSet:
        IF \E snapshot \in oldSnapShotMap : 
            /\ snapshot["pc"] = localPc
            /\ snapshot["state"] = newState
            /\ snapshot["threadLocals"] = threadLocals
            /\ snapshot["globalVars"] = globalVars
            /\ snapshot["dynamicNode"] = RemoveId(db)
            \* /\ snapshot["dynamicNodeSet"] = DynamicNodeSet
        THEN 
            FALSE
        ELSE
            TRUE
    \* LET normMap == {Normalize(snapshot) : snapshot \in newSnapShotMap}
    \*     normOldMap == {Normalize(snapshot) : snapshot \in oldSnapShotMap}
    \* IN
    \*     normMap # normOldMap
    
GetBackState(localPc, newState, oldSnapShotMap, newDBSet) ==
    CHOOSE snapshot \in oldSnapShotMap:
        /\ snapshot["pc"] = localPc
        /\ snapshot["state"] = newState
        /\ snapshot["threadLocals"] = threadLocals
        /\ snapshot["globalVars"] = globalVars
        /\ snapshot["dynamicNode"] = RemoveId(CHOOSE db \in (newDBSet \ DynamicNodeSet): TRUE)
\* StateUpdate(wgid, t, newBlocks) ==
\*     {thread \in Threads:
\*         IF \E i \in 1..Len(newBlocks.node) : 
\*             /\ thread \in newBlocks.node[i].tangle[wgid] 
\*             /\ \A tid \in newBlocks.node[i].tangle[wgid] : pc[tid] = pc[thread] /\ ThreadInstructions[1][pc[tid]] \in TangledInstructionSet /\ state[tid] = state[thread]
\*             /\ state[thread] # "terminated" 
\*             /\ state[thread] # "ready"
\*         THEN 
\*             TRUE
\*         ELSE
\*             FALSE
\*     }


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

\* This is the inner helper function to return the array with updated element. It does not change the next state of the variable
ChangeElementAt(var, index, value) ==
        Var(var.scope, var.name, [currentIndex \in DOMAIN var.value |-> IF currentIndex = index THEN value ELSE var.value[currentIndex] ], var.index)


OpLogicalOr(t, var, operand1, operand2) ==
    LET workgroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workgroupId, mangledOperand1)
                operand2Val == GetVal(workgroupId, mangledOperand2)
            IN
                /\  IF operand1Val = TRUE \/ operand2Val = TRUE THEN
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars, DynamicNodeSet, globalCounter, snapShotMap>>

OpLogicalAnd(t, var, operand1, operand2) ==
    LET workgroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workgroupId, mangledOperand1)
                operand2Val == GetVal(workgroupId, mangledOperand2)
            IN
                /\  IF operand1Val = TRUE /\ operand2Val = TRUE THEN
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>

OpLogicalEqual(t, var, operand1, operand2) ==
    LET workgroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workgroupId, mangledOperand1)
                operand2Val == GetVal(workgroupId, mangledOperand2)
            IN
                /\  IF operand1Val = operand2Val THEN
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>

OpLogicalNotEqual(t, var, operand1, operand2) ==
    LET workgroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workgroupId, mangledOperand1)
                operand2Val == GetVal(workgroupId, mangledOperand2)
            IN
                /\  IF operand1Val # operand2Val THEN
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
OpLogicalNot(t, var, operand) ==
    LET workgroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand == Mangle(t, operand)
    IN
        /\  LET operandVal == GetVal(workgroupId, mangledOperand)
            IN
                /\  IF operandVal = FALSE THEN
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>


OpEqual(t, var, operand1, operand2) ==
    LET workgroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workgroupId, mangledOperand1)
                operand2Val == GetVal(workgroupId, mangledOperand2)
            IN
                /\  IF operand1Val = operand2Val THEN
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>


OpNotEqual(t, var, operand1, operand2) ==
    LET workgroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workgroupId, mangledOperand1)
                operand2Val == GetVal(workgroupId, mangledOperand2)
            IN
                /\  IF operand1Val # operand2Val THEN
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>


OpLess(t, var, operand1, operand2) ==
    LET workgroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workgroupId, mangledOperand1)
                operand2Val == GetVal(workgroupId, mangledOperand2)
            IN
                /\  IF operand1Val < operand2Val THEN
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>

OpLessOrEqual(t, var, operand1, operand2) ==
    LET workgroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workgroupId, mangledOperand1)
                operand2Val == GetVal(workgroupId, mangledOperand2)
            IN
                /\  IF operand1Val <= operand2Val THEN
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>

OpGreater(t, var, operand1, operand2) ==
    LET workgroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workgroupId, mangledOperand1)
                operand2Val == GetVal(workgroupId, mangledOperand2)
            IN
                /\  IF operand1Val > operand2Val THEN
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>

OpGreaterOrEqual(t, var, operand1, operand2) ==
    LET workgroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workgroupId, mangledOperand1)
                operand2Val == GetVal(workgroupId, mangledOperand2)
            IN
                /\  IF operand1Val >= operand2Val THEN
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>


OpAdd(t, var, operand1, operand2) ==
    LET workgroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workgroupId, mangledOperand1)
                operand2Val == GetVal(workgroupId, mangledOperand2)
            IN
                Assignment(t, {Var(MangleVar.scope, MangleVar.name, operand1Val + operand2Val, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>


OpAtomicAdd(t, var, operand1, operand2) ==
    LET workgroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workgroupId, mangledOperand1)
                operand2Val == GetVal(workgroupId, mangledOperand2)
            IN
                Assignment(t, {Var(MangleVar.scope, MangleVar.name, operand1Val + operand2Val, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>

OpSub(t, var, operand1, operand2) ==
    LET workgroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workgroupId, mangledOperand1)
                operand2Val == GetVal(workgroupId, mangledOperand2)
            IN
                Assignment(t, {Var(MangleVar.scope, MangleVar.name, operand1Val - operand2Val, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>

OpAtomicSub(t, var, operand1, operand2) ==
    LET workgroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workgroupId, mangledOperand1)
                operand2Val == GetVal(workgroupId, mangledOperand2)
            IN
                Assignment(t, {Var(MangleVar.scope, MangleVar.name, operand1Val - operand2Val, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>

OpMul(t, var, operand1, operand2) ==
    LET workgroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workgroupId, mangledOperand1)
                operand2Val == GetVal(workgroupId, mangledOperand2)
            IN
                Assignment(t, {Var(MangleVar.scope, MangleVar.name, operand1Val * operand2Val, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>


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
        /\  UNCHANGED <<state>>


\* It does not handle the situation where result is an index to array
OpAtomicLoad(t, result, pointer) ==
    LET mangledResult == Mangle(t, result)
        mangledPointer == Mangle(t, pointer)
    IN
        /\
            \/  
                /\  IsVariable(mangledResult)
                \* /\  VarExists(WorkGroupId(t)+1, mangledResult)
            \/  IsIntermediate(mangledResult)
        /\  IsVariable(mangledPointer)
        /\  VarExists(WorkGroupId(t)+1, mangledPointer)
        /\  IF IsIntermediate(mangledResult) THEN 
                LET pointerVar == GetVar(WorkGroupId(t)+1, mangledPointer)
                    evaluatedIndex == EvalExpr(t, WorkGroupId(t)+1, pointer.index)
                IN 
                    /\
                        IF evaluatedIndex > 0 THEN 
                            Assignment(t, {Var(mangledResult.scope, mangledResult.name, pointerVar.value[evaluatedIndex], Index(-1))})
                        ELSE
                            Assignment(t, {Var(mangledResult.scope, mangledResult.name, pointerVar.value, Index(-1))})
            ELSE
                LET pointerVar == GetVar(WorkGroupId(t)+1, mangledPointer)
                    \* resultVar == GetVar(WorkGroupId(t)+1, mangledResult)
                    resultVar == mangledResult
                    evaluatedPointerIndex == EvalExpr(t, WorkGroupId(t)+1, pointer.index)
                    evaluatedResultIndex == EvalExpr(t, WorkGroupId(t)+1, result.index)
                IN
                    /\
                        IF evaluatedPointerIndex > 0 /\ evaluatedResultIndex > 0 THEN
                            Assignment(t, {ChangeElementAt(resultVar, evaluatedResultIndex, pointerVar.value[evaluatedPointerIndex])})
                        ELSE IF evaluatedPointerIndex > 0 THEN
                            Assignment(t, {Var(resultVar.scope, resultVar.name, pointerVar.value[evaluatedPointerIndex], Index(-1))})
                        ELSE IF evaluatedResultIndex > 0 THEN
                            Assignment(t, {ChangeElementAt(resultVar, evaluatedResultIndex, pointerVar.value)})
                        ELSE
                            Assignment(t, {Var(resultVar.scope, resultVar.name, pointerVar.value, Index(-1))})  
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<state,  DynamicNodeSet, globalCounter, snapShotMap>>

OpAtomicStore(t, pointer, value) == 
    LET mangledPointer == Mangle(t, pointer)
    IN
        /\  IsVariable(mangledPointer)
        /\  VarExists(WorkGroupId(t)+1, mangledPointer)
        /\  LET pointerVar == GetVar(WorkGroupId(t)+1, mangledPointer)
                evaluatedPointerIndex == EvalExpr(t, WorkGroupId(t)+1, pointer.index)
            IN
                /\
                    IF evaluatedPointerIndex > 0 THEN 
                        Assignment(t, {ChangeElementAt(pointerVar, evaluatedPointerIndex, EvalExpr(t, WorkGroupId(t)+1, value))})
                    ELSE
                        Assignment(t, {Var(pointerVar.scope, pointerVar.name, EvalExpr(t, WorkGroupId(t)+1, value), pointerVar.index)})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<state,  DynamicNodeSet, globalCounter, snapShotMap>>

OpAtomicIncrement(t, pointer) == 
    LET mangledPointer == Mangle(t, pointer)
    IN
        /\  IsVariable(mangledPointer)
        /\  VarExists(WorkGroupId(t)+1, mangledPointer)
        /\  IsArray(pointer) = FALSE
        /\  LET pointerVar == GetVar(WorkGroupId(t)+1, mangledPointer)
                evaluatedPointerIndex == EvalExpr(t, WorkGroupId(t)+1, pointer.index)
            IN
                /\
                    IF evaluatedPointerIndex > 0 THEN 
                        Assignment(t, {ChangeElementAt(pointerVar, evaluatedPointerIndex, pointerVar.value[evaluatedPointerIndex] + 1)})
                    ELSE  
                        Assignment(t, {Var(pointerVar.scope, pointerVar.name, pointerVar.value + 1, pointerVar.index)})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<state,  DynamicNodeSet, globalCounter, snapShotMap>>


OpAtomicDecrement(t, pointer) == 
    LET mangledPointer == Mangle(t, pointer)
    IN
        /\  IsVariable(mangledPointer)
        /\  VarExists(WorkGroupId(t)+1, mangledPointer)
        /\  LET pointerVar == GetVar(WorkGroupId(t)+1, mangledPointer)
                evaluatedPointerIndex == EvalExpr(t, WorkGroupId(t)+1, pointer.index)
            IN
                /\
                    IF evaluatedPointerIndex > 0 THEN 
                        Assignment(t, {ChangeElementAt(pointerVar, evaluatedPointerIndex, pointerVar.value[evaluatedPointerIndex] - 1)})
                    ELSE  
                        Assignment(t, {Var(pointerVar.scope, pointerVar.name, pointerVar.value - 1, pointerVar.index)})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<state,  DynamicNodeSet, globalCounter, snapShotMap>>

\*  OpControlBarrier(t, scope) ==
\*     IF GetVal(-1, scope) = "subgroup" THEN \* already waiting at a subgroup barrier
\*         \* find all threads and their corresponding barrier state within the same subgroup
\*         LET sthreads == ThreadsWithinSubgroup(SubgroupId(t), WorkGroupId(t))
\*             currentTangle == FindCurrentBlock( pc[t]).tangle[WorkGroupId(t) + 1]
\*         IN
\*             IF \E sthread \in sthreads: sthread  \notin currentTangle THEN 
\*                 Print("UB: All threads within subgroup must converge at current block", FALSE)
\*             \* if there exists thread in the subgroup that has not reached the subgroup barrier, set the barrier to current thread
\*             ELSE IF \E sthread \in sthreads: pc[sthread] # pc[t] THEN
\*                 /\  state' = [state EXCEPT ![t] = "subgroup"]
\*                 /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
\*             \* if all threads in the subgroup are waiting at the barrier, release them
\*             ELSE 
\*                 \* release all barrier in the subgroup, marking state as ready
\*                 /\  state' = [
\*                         tid \in Threads |->
\*                             IF tid \in sthreads THEN 
\*                                 "ready" 
\*                             ELSE 
\*                                 state[tid]
\*                     ]
\*                 \* increment the program counter for all threads in the subgroup
\*                 /\  pc' = [
\*                         tid \in Threads |->
\*                             IF tid \in sthreads THEN 
\*                                 pc[tid] + 1
\*                             ELSE 
\*                                 pc[tid]
\*                     ]
\*                 /\  UNCHANGED <<threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>

\*     ELSE IF GetVal(-1, scope) = "workgroup" THEN \* already waiting at a workgroup barrier
\*         LET sthreads == ThreadsWithinSubgroup(SubgroupId(t), WorkGroupId(t))
\*         IN
\*             \* if there exists thread in the subgroup that has not reached the subgroup barrier, set the barrier to current thread
\*             IF \E sthread \in sthreads: pc[sthread] # pc[t] THEN
\*                 /\  state' = [state EXCEPT ![t] = "workgroup"]
\*                 /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
\*             \* if all threads in the subgroup are waiting at the barrier, release them
\*             ELSE 
\*                 \* release all barrier in the subgroup, marking state as ready
\*                 /\  state' = [
\*                         tid \in Threads |->
\*                             IF tid \in sthreads THEN 
\*                                 "ready" 
\*                             ELSE 
\*                                 state[tid]
\*                     ]
\*                 \* increment the program counter for all threads in the subgroup
\*                 /\  pc' = [
\*                         tid \in Threads |->
\*                             IF tid \in sthreads THEN 
\*                                 pc[tid] + 1
\*                             ELSE 
\*                                 pc[tid]
\*                     ]
\*                 /\  UNCHANGED <<threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
\*     ELSE    
\*         FALSE

 OpControlBarrier(t, scope) ==
    IF GetVal(-1, scope) = "subgroup" THEN \* already waiting at a subgroup barrier
        \* find all threads and their corresponding barrier state within the same subgroup
        LET sthreads == ThreadsWithinSubgroup(SubgroupId(t), WorkGroupId(t))
            workgroupId == WorkGroupId(t)+1
            currentTangle == CurrentDynamicNode(workgroupId, t).executeSet[workgroupId]
        IN
            IF \E sthread \in sthreads: sthread  \notin currentTangle THEN 
                Print("UB: All threads within subgroup must converge at current block", FALSE)
            \* if there exists thread in the subgroup that has not reached the subgroup barrier, set the barrier to current thread
            ELSE IF \E sthread \in sthreads: pc[sthread] # pc[t] THEN
                /\  state' = [state EXCEPT ![t] = "subgroup"]
                /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
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
                /\  UNCHANGED <<threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>

    ELSE IF GetVal(-1, scope) = "workgroup" THEN \* already waiting at a workgroup barrier
        LET sthreads == ThreadsWithinSubgroup(SubgroupId(t), WorkGroupId(t))
        IN
            \* if there exists thread in the subgroup that has not reached the subgroup barrier, set the barrier to current thread
            IF \E sthread \in sthreads: pc[sthread] # pc[t] THEN
                /\  state' = [state EXCEPT ![t] = "workgroup"]
                /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
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
                /\  UNCHANGED <<threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
    ELSE    
        FALSE


\* zheyuan: add assertion to check if the all threads within subgroup converge at current block because it is UB if not
\* OpGroupAll(t, result, scope, predicate) ==
\*     LET mangledResult == Mangle(t, result)
\*     IN
\*         /\  
\*             \/  /\  IsVariable(mangledResult)
\*                 \* /\  VarExists(WorkGroupId(t)+1, mangledResult)
\*             \/  IsIntermediate(mangledResult)
\*         /\  scope.value \in ScopeOperand
\*         /\  IF scope.value = "subgroup" THEN
\*                 /\  LET sthreads == ThreadsWithinSubgroup(SubgroupId(t), WorkGroupId(t))
\*                         currentTangle == FindCurrentBlock( pc[t]).tangle[WorkGroupId(t) + 1]
\*                     IN
\*                         IF \E sthread \in sthreads: sthread  \notin currentTangle THEN 
\*                                 Print("UB: All threads within subgroup must converge at current block for OpGroupAll", FALSE)
\*                         \* if there exists thread in the subgroup that has not reached the opgroupAll, set the barrier to current thread
\*                         ELSE IF \E sthread \in sthreads: pc[sthread] # pc[t] THEN
\*                             /\  state' = [state EXCEPT ![t] = "subgroup"]
\*                             /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
\*                         ELSE IF \A sthread \in sthreads: EvalExpr(sthread, WorkGroupId(t)+1, predicate) = TRUE THEN 
\*                             /\  Assignment(t, {Var(mangledResult.scope, Mangle(sthread, result).name, TRUE, Index(-1)): sthread \in sthreads})
\*                             /\  state' = [\* release all barrier in the subgroup, marking barrier as ready
\*                                     tid \in Threads |->
\*                                         IF tid \in sthreads THEN 
\*                                             "ready" 
\*                                         ELSE 
\*                                             state[tid]
\*                                 ]
\*                             /\  pc' = [
\*                                     tid \in Threads |->
\*                                         IF tid \in sthreads THEN 
\*                                             pc[tid] + 1
\*                                         ELSE 
\*                                             pc[tid]
\*                                 ]
\*                             /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
\*                         ELSE 
\*                             /\  Assignment(t, {Var(mangledResult.scope, Mangle(sthread, result).name, FALSE, Index(-1)): sthread \in sthreads })
\*                             /\  state' = [\* release all barrier in the subgroup, marking barrier as ready
\*                                     tid \in Threads |->
\*                                         IF tid \in sthreads THEN 
\*                                             "ready" 
\*                                         ELSE 
\*                                             state[tid]
\*                                 ]
\*                             /\  pc' = [
\*                                     tid \in Threads |->
\*                                         IF tid \in sthreads THEN 
\*                                             pc[tid] + 1
\*                                         ELSE 
\*                                             pc[tid]
\*                                 ]
\*                             /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
\*             ELSE IF scope.value = "workgroup" THEN 
\*                 /\  LET wthreads == ThreadsWithinWorkGroup(WorkGroupId(t))
\*                     IN      \* if there is a thread that has not reached the opgroupAll, return false
\*                         /\  IF \E wthread \in wthreads: pc[wthread] # pc[t] THEN
\*                                 /\  state' = [state EXCEPT ![t] = "workgroup"]
\*                                 /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
\*                             ELSE IF \A wthread \in wthreads: EvalExpr(wthread, WorkGroupId(t)+1, predicate) = TRUE THEN 
\*                                 /\  Assignment(t, {Var(mangledResult.scope, Mangle(wthread, result).name, TRUE, Index(-1)): wthread \in wthreads})
\*                                 /\  state' = [\* release all barrier in the subgroup, marking barrier as ready
\*                                         tid \in Threads |->
\*                                             IF tid \in wthreads THEN 
\*                                                 "ready" 
\*                                             ELSE 
\*                                                 state[tid]
\*                                     ]
\*                                 /\  pc' = [
\*                                         tid \in Threads |->
\*                                             IF tid \in wthreads THEN 
\*                                                 pc[tid] + 1
\*                                             ELSE 
\*                                                 pc[tid]
\*                                     ]
\*                                 /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
\*                             ELSE 
\*                                 /\  Assignment(t, {Var(mangledResult.scope, Mangle(wthread, result).name, FALSE, Index(-1)): wthread \in wthreads })
\*                                 /\  state' = [\* release all barrier in the subgroup, marking barrier as ready
\*                                         tid \in Threads |->
\*                                             IF tid \in wthreads THEN 
\*                                                 "ready" 
\*                                             ELSE 
\*                                                 state[tid]
\*                                     ]
\*                                 /\  pc' = [
\*                                         tid \in Threads |->
\*                                             IF tid \in wthreads THEN 
\*                                                 pc[tid] + 1
\*                                             ELSE 
\*                                                 pc[tid]
\*                                     ]
\*                                 /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
\*             ELSE
\*                 /\  FALSE


\* zheyuan: add assertion to check if the all threads within subgroup converge at current block because it is UB if not
OpGroupAll(t, result, scope, predicate) ==
    LET mangledResult == Mangle(t, result)
    IN
        /\  
            \/  /\  IsVariable(mangledResult)
            \/  IsIntermediate(mangledResult)
        /\  scope.value \in ScopeOperand
        /\  IF scope.value = "subgroup" THEN
                /\  LET sthreads == ThreadsWithinSubgroup(SubgroupId(t), WorkGroupId(t))
                        workgroupId == WorkGroupId(t)+1
                        currentTangle == CurrentDynamicNode(workgroupId, t).executeSet[workgroupId]
                    IN
                        IF \E sthread \in sthreads: sthread  \notin currentTangle THEN 
                                Print("UB: All threads within subgroup must converge at current block for OpGroupAll", FALSE)
                        \* if there exists thread in the subgroup that has not reached the opgroupAll, set the barrier to current thread
                        ELSE IF \E sthread \in sthreads: pc[sthread] # pc[t] THEN
                            /\  state' = [state EXCEPT ![t] = "subgroup"]
                            /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
                        ELSE IF \A sthread \in sthreads: EvalExpr(sthread, workgroupId, predicate) = TRUE THEN 
                            /\  Assignment(t, {Var(mangledResult.scope, Mangle(sthread, result).name, TRUE, Index(-1)): sthread \in sthreads})
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
                            /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
                        ELSE 
                            /\  Assignment(t, {Var(mangledResult.scope, Mangle(sthread, result).name, FALSE, Index(-1)): sthread \in sthreads })
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
                            /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
            ELSE IF scope.value = "workgroup" THEN 
                /\  LET wthreads == ThreadsWithinWorkGroup(WorkGroupId(t))
                        workgroupId == WorkGroupId(t)+1
                    IN      \* if there is a thread that has not reached the opgroupAll, return false
                        /\  IF \E wthread \in wthreads: pc[wthread] # pc[t] THEN
                                /\  state' = [state EXCEPT ![t] = "workgroup"]
                                /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
                            ELSE IF \A wthread \in wthreads: EvalExpr(wthread, workgroupId, predicate) = TRUE THEN 
                                /\  Assignment(t, {Var(mangledResult.scope, Mangle(wthread, result).name, TRUE, Index(-1)): wthread \in wthreads})
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
                                /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
                            ELSE 
                                /\  Assignment(t, {Var(mangledResult.scope, Mangle(wthread, result).name, FALSE, Index(-1)): wthread \in wthreads })
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
                                /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
            ELSE
                /\  FALSE



\* OpGroupAny(t, result, scope, predicate) ==
\*     LET mangledResult == Mangle(t, result)
\*     IN
\*         /\  
\*             \/  /\  IsVariable(mangledResult)
\*                 \* /\  VarExists(WorkGroupId(t)+1, mangledResult)
\*             \/  IsIntermediate(mangledResult)
\*         /\  scope.value \in ScopeOperand
\*         /\  IF scope.value = "subgroup" THEN
\*                 /\  LET sthreads == ThreadsWithinSubgroup(SubgroupId(t), WorkGroupId(t))
\*                         currentTangle == FindCurrentBlock( pc[t]).tangle[WorkGroupId(t) + 1]
\*                     IN
\*                         IF \E sthread \in sthreads: sthread  \notin currentTangle THEN 
\*                                 Print("UB: All threads within subgroup must converge at current block for OpGroupAny", FALSE)
\*                         \* if there exists thread in the subgroup that has not reached the subgroup barrier, set the barrier to current thread
\*                         ELSE IF \E sthread \in sthreads: pc[sthread] # pc[t] THEN
\*                             /\  state' = [state EXCEPT ![t] = "subgroup"]
\*                             /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
\*                         ELSE IF \E sthread \in sthreads: EvalExpr(sthread, WorkGroupId(t)+1, predicate) = TRUE THEN 
\*                             /\  Assignment(t, {Var(mangledResult.scope, Mangle(sthread, result).name, TRUE, Index(-1)): sthread \in sthreads})
\*                             /\  state' = [\* release all barrier in the subgroup, marking barrier as ready
\*                                     tid \in Threads |->
\*                                         IF tid \in sthreads THEN 
\*                                             "ready" 
\*                                         ELSE 
\*                                             state[tid]
\*                                 ]
\*                             /\  pc' = [
\*                                     tid \in Threads |->
\*                                         IF tid \in sthreads THEN 
\*                                             pc[tid] + 1
\*                                         ELSE 
\*                                             pc[tid]
\*                                 ]
\*                             /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
\*                         ELSE 
\*                             /\  Assignment(t, {Var(mangledResult.scope, Mangle(sthread, result).name, FALSE, Index(-1)): sthread \in sthreads })
\*                             /\  state' = [\* release all barrier in the subgroup, marking barrier as
\*                                     tid \in Threads |->
\*                                         IF tid \in sthreads THEN 
\*                                             "ready" 
\*                                         ELSE 
\*                                             state[tid]
\*                                 ]
\*                             /\  pc' = [
\*                                     tid \in Threads |->
\*                                         IF tid \in sthreads THEN 
\*                                             pc[tid] + 1
\*                                         ELSE 
\*                                             pc[tid]
\*                                 ]
\*                             /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
\*             ELSE IF scope.value = "workgroup" THEN
\*                 /\  LET wthreads == ThreadsWithinWorkGroup(WorkGroupId(t))
\*                     IN      \* if there is a thread that has not reached the opgroupAny, return false
\*                         /\  IF \E wthread \in wthreads: pc[wthread] # pc[t] THEN
\*                                 /\  state' = [state EXCEPT ![t] = "workgroup"]
\*                                 /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
\*                             ELSE IF \E wthread \in wthreads: EvalExpr(wthread, WorkGroupId(t)+1, predicate) = TRUE THEN 
\*                                 /\  Assignment(t, {Var(mangledResult.scope, Mangle(wthread, result).name, TRUE, Index(-1)): wthread \in wthreads})
\*                                 /\  state' = [\* release all barrier in the subgroup, marking barrier as ready
\*                                         tid \in Threads |->
\*                                             IF tid \in wthreads THEN 
\*                                                 "ready" 
\*                                             ELSE 
\*                                                 state[tid]
\*                                     ]
\*                                 /\  pc' = [
\*                                         tid \in Threads |->
\*                                             IF tid \in wthreads THEN 
\*                                                 pc[tid] + 1
\*                                             ELSE 
\*                                                 pc[tid]
\*                                     ]
\*                                 /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
\*                             ELSE 
\*                                 /\  Assignment(t, {Var(mangledResult.scope, Mangle(wthread, result).name, FALSE, Index(-1)): wthread \in wthreads })
\*                                 /\  state' = [\* release all barrier in the subgroup, marking barrier as ready
\*                                         tid \in Threads |->
\*                                             IF tid \in wthreads THEN 
\*                                                 "ready" 
\*                                             ELSE 
\*                                                 state[tid]
\*                                     ]
\*                                 /\  pc' = [
\*                                         tid \in Threads |->
\*                                             IF tid \in wthreads THEN 
\*                                                 pc[tid] + 1
\*                                             ELSE 
\*                                                 pc[tid]
\*                                     ]
\*                                 /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
\*             ELSE
\*                 /\  FALSE

OpGroupAny(t, result, scope, predicate) ==
    LET mangledResult == Mangle(t, result)
    IN
        /\  
            \/  /\  IsVariable(mangledResult)
                \* /\  VarExists(WorkGroupId(t)+1, mangledResult)
            \/  IsIntermediate(mangledResult)
        /\  scope.value \in ScopeOperand
        /\  IF scope.value = "subgroup" THEN
                /\  LET sthreads == ThreadsWithinSubgroup(SubgroupId(t), WorkGroupId(t))
                        workgroupId == WorkGroupId(t)+1
                        currentTangle == CurrentDynamicNode(workgroupId, t).executeSet[workgroupId]
                    IN
                        IF \E sthread \in sthreads: sthread  \notin currentTangle THEN 
                                Print("UB: All threads within subgroup must converge at current block for OpGroupAny", FALSE)
                        \* if there exists thread in the subgroup that has not reached the subgroup barrier, set the barrier to current thread
                        ELSE IF \E sthread \in sthreads: pc[sthread] # pc[t] THEN
                            /\  state' = [state EXCEPT ![t] = "subgroup"]
                            /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
                        ELSE IF \E sthread \in sthreads: EvalExpr(sthread, workgroupId, predicate) = TRUE THEN 
                            /\  Assignment(t, {Var(mangledResult.scope, Mangle(sthread, result).name, TRUE, Index(-1)): sthread \in sthreads})
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
                            /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
                        ELSE 
                            /\  Assignment(t, {Var(mangledResult.scope, Mangle(sthread, result).name, FALSE, Index(-1)): sthread \in sthreads })
                            /\  state' = [\* release all barrier in the subgroup, marking barrier as
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
                            /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
            ELSE IF scope.value = "workgroup" THEN
                /\  LET wthreads == ThreadsWithinWorkGroup(WorkGroupId(t))
                        workgroupId == WorkGroupId(t)+1
                    IN      \* if there is a thread that has not reached the opgroupAny, return false
                        /\  IF \E wthread \in wthreads: pc[wthread] # pc[t] THEN
                                /\  state' = [state EXCEPT ![t] = "workgroup"]
                                /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
                            ELSE IF \E wthread \in wthreads: EvalExpr(wthread, workgroupId, predicate) = TRUE THEN 
                                /\  Assignment(t, {Var(mangledResult.scope, Mangle(wthread, result).name, TRUE, Index(-1)): wthread \in wthreads})
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
                                /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
                            ELSE 
                                /\  Assignment(t, {Var(mangledResult.scope, Mangle(wthread, result).name, FALSE, Index(-1)): wthread \in wthreads })
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
                                /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
            ELSE
                /\  FALSE


\* OpGroupNonUniformAll(t, result, scope, predicate) ==
\*     LET mangledResult == Mangle(t, result)
\*     IN
\*         /\  
\*             \/  /\  IsVariable(result)
\*                 \* /\  VarExists(WorkGroupId(t)+1, result)
\*             \/  IsIntermediate(result)
\*         /\  scope.value \in ScopeOperand
\*         /\  IF scope.value = "subgroup" THEN
\*                 /\  LET active_subgroup_threads == ThreadsWithinSubgroup(SubgroupId(t), WorkGroupId(t)) \cap FindCurrentBlock( pc[t]).tangle[WorkGroupId(t) + 1]
\*                     IN
\*                         IF \E sthread \in active_subgroup_threads: pc[sthread] # pc[t] THEN
\*                             /\  state' = [state EXCEPT ![t] = "subgroup"]
\*                             /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
\*                         ELSE IF \A sthread \in active_subgroup_threads: EvalExpr(sthread, WorkGroupId(t)+1, predicate) = TRUE THEN 
\*                             /\  Assignment(t, {Var(result.scope, Mangle(sthread, result).name, TRUE, Index(-1)): sthread \in active_subgroup_threads})
\*                             /\  state' = [\* release all barrier in the subgroup, marking barrier as ready
\*                                     tid \in Threads |->
\*                                         IF tid \in active_subgroup_threads THEN 
\*                                             "ready" 
\*                                         ELSE 
\*                                             state[tid]
\*                                 ]
\*                             /\  pc' = [
\*                                     tid \in Threads |->
\*                                         IF tid \in active_subgroup_threads THEN 
\*                                             pc[tid] + 1
\*                                         ELSE 
\*                                             pc[tid]
\*                                 ]
\*                             /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
\*                         ELSE 
\*                             /\  Assignment(t, {Var(result.scope, Mangle(sthread, result).name, FALSE, Index(-1)): sthread \in active_subgroup_threads })
\*                             /\  state' = [\* release all barrier in the subgroup, marking barrier as ready
\*                                     tid \in Threads |->
\*                                         IF tid \in active_subgroup_threads THEN 
\*                                             "ready" 
\*                                         ELSE 
\*                                             state[tid]
\*                                 ]
\*                             /\  pc' = [
\*                                     tid \in Threads |->
\*                                         IF tid \in active_subgroup_threads THEN 
\*                                             pc[tid] + 1
\*                                         ELSE 
\*                                             pc[tid]
\*                                 ]
\*                             /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
\*             ELSE
\*                 /\  FALSE


OpGroupNonUniformAll(t, result, scope, predicate) ==
    LET mangledResult == Mangle(t, result)
    IN
        /\  
            \/  /\  IsVariable(result)
            \/  IsIntermediate(result)
        /\  scope.value \in ScopeOperand
        /\  IF scope.value = "subgroup" THEN
                /\  LET workGroupId == WorkGroupId(t) + 1
                        currentDB == CurrentDynamicNode(workGroupId, t)
                        active_subgroup_threads == currentDB.currentThreadSet[workGroupId]
                        unknown_subgroup_threads == currentDB.unknownSet[workGroupId]
                    IN
                        \* if there are threads in tangle not reaching the instruction point,
                        \* or there are threads in unknown set, make current thread waiting
                        IF unknown_subgroup_threads # {} \/ \E sthread \in active_subgroup_threads: pc[sthread] # pc[t] THEN
                            /\  state' = [state EXCEPT ![t] = "subgroup"]
                            /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
                        ELSE IF \A sthread \in active_subgroup_threads: EvalExpr(sthread, workGroupId, predicate) = TRUE THEN 
                            /\  Assignment(t, {Var(result.scope, Mangle(sthread, result).name, TRUE, Index(-1)): sthread \in active_subgroup_threads})
                            /\  state' = [\* release all barrier in the subgroup, marking barrier as ready
                                    tid \in Threads |->
                                        IF tid \in active_subgroup_threads THEN 
                                            "ready" 
                                        ELSE 
                                            state[tid]
                                ]
                            /\  pc' = [
                                    tid \in Threads |->
                                        IF tid \in active_subgroup_threads THEN 
                                            pc[tid] + 1
                                        ELSE 
                                            pc[tid]
                                ]
                            /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
                        ELSE 
                            /\  Assignment(t, {Var(result.scope, Mangle(sthread, result).name, FALSE, Index(-1)): sthread \in active_subgroup_threads })
                            /\  state' = [\* release all barrier in the subgroup, marking barrier as ready
                                    tid \in Threads |->
                                        IF tid \in active_subgroup_threads THEN 
                                            "ready" 
                                        ELSE 
                                            state[tid]
                                ]
                            /\  pc' = [
                                    tid \in Threads |->
                                        IF tid \in active_subgroup_threads THEN 
                                            pc[tid] + 1
                                        ELSE 
                                            pc[tid]
                                ]
                            /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
            ELSE
                /\  FALSE

\* OpGroupNonUniformAny(t, result, scope, predicate) ==
\*     LET mangledResult == Mangle(t, result)
\*     IN
\*         /\  
\*             \/  /\  IsVariable(result)
\*             \/  IsIntermediate(result)
\*         /\  scope.value \in ScopeOperand
\*         /\  IF scope.value = "subgroup" THEN
\*                 /\  LET active_subgroup_threads == ThreadsWithinSubgroup(SubgroupId(t), WorkGroupId(t)) \cap FindCurrentBlock( pc[t]).tangle[WorkGroupId(t) + 1]
\*                     IN
\*                         IF \E sthread \in active_subgroup_threads: pc[sthread] # pc[t] THEN
\*                             /\  state' = [state EXCEPT ![t] = "subgroup"]
\*                             /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
\*                         ELSE IF \E sthread \in active_subgroup_threads: EvalExpr(sthread, WorkGroupId(t)+1, predicate) = TRUE THEN 
\*                             /\  Assignment(t, {Var(result.scope, Mangle(sthread, result).name, TRUE, Index(-1)): sthread \in active_subgroup_threads})
\*                             /\  state' = [\* release all barrier in the subgroup, marking barrier as ready
\*                                     tid \in Threads |->
\*                                         IF tid \in active_subgroup_threads THEN 
\*                                             "ready" 
\*                                         ELSE 
\*                                             state[tid]
\*                                 ]
\*                             /\  pc' = [
\*                                     tid \in Threads |->
\*                                         IF tid \in active_subgroup_threads THEN 
\*                                             pc[tid] + 1
\*                                         ELSE 
\*                                             pc[tid]
\*                                 ]
\*                             /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
\*                         ELSE 
\*                             /\  Assignment(t, {Var(result.scope, Mangle(sthread, result).name, FALSE, Index(-1)): sthread \in active_subgroup_threads })
\*                             /\  state' = [\* release all barrier in the subgroup, marking barrier as ready
\*                                     tid \in Threads |->
\*                                         IF tid \in active_subgroup_threads THEN 
\*                                             "ready" 
\*                                         ELSE 
\*                                             state[tid]
\*                                 ]
\*                             /\  pc' = [
\*                                     tid \in Threads |->
\*                                         IF tid \in active_subgroup_threads THEN 
\*                                             pc[tid] + 1
\*                                         ELSE 
\*                                             pc[tid]
\*                                 ]
\*                             /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
\*             ELSE
\*                 /\  FALSE


OpGroupNonUniformAny(t, result, scope, predicate) ==
    LET mangledResult == Mangle(t, result)
    IN
        /\  
            \/  /\  IsVariable(result)
            \/  IsIntermediate(result)
        /\  scope.value \in ScopeOperand
        /\  IF scope.value = "subgroup" THEN
                /\  LET workGroupId == WorkGroupId(t) + 1
                        currentDB == CurrentDynamicNode(workGroupId, t)
                        active_subgroup_threads == currentDB.currentThreadSet[workGroupId]
                        unknown_subgroup_threads == currentDB.unknownSet[workGroupId]
                    IN
                        IF unknown_subgroup_threads # {} \/ \E sthread \in active_subgroup_threads: pc[sthread] # pc[t] THEN
                            /\  state' = [state EXCEPT ![t] = "subgroup"]
                            /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
                        ELSE IF \E sthread \in active_subgroup_threads: EvalExpr(sthread, workGroupId+1, predicate) = TRUE THEN 
                            /\  Assignment(t, {Var(result.scope, Mangle(sthread, result).name, TRUE, Index(-1)): sthread \in active_subgroup_threads})
                            /\  state' = [\* release all barrier in the subgroup, marking barrier as ready
                                    tid \in Threads |->
                                        IF tid \in active_subgroup_threads THEN 
                                            "ready" 
                                        ELSE 
                                            state[tid]
                                ]
                            /\  pc' = [
                                    tid \in Threads |->
                                        IF tid \in active_subgroup_threads THEN 
                                            pc[tid] + 1
                                        ELSE 
                                            pc[tid]
                                ]
                            /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
                        ELSE 
                            /\  Assignment(t, {Var(result.scope, Mangle(sthread, result).name, FALSE, Index(-1)): sthread \in active_subgroup_threads })
                            /\  state' = [\* release all barrier in the subgroup, marking barrier as ready
                                    tid \in Threads |->
                                        IF tid \in active_subgroup_threads THEN 
                                            "ready" 
                                        ELSE 
                                            state[tid]
                                ]
                            /\  pc' = [
                                    tid \in Threads |->
                                        IF tid \in active_subgroup_threads THEN 
                                            pc[tid] + 1
                                        ELSE 
                                            pc[tid]
                                ]
                            /\ UNCHANGED <<globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>
            ELSE
                /\  FALSE

(* result and pointer are variable *)
OpAtomicExchange(t, result, pointer, value) ==
    LET mangledResult == Mangle(t, result)
        mangledPointer == Mangle(t, pointer)
    IN
        /\  IsVariable(mangledResult)
        \* /\  VarExists(WorkGroupId(t)+1, mangledResult)
        /\  IsVariable(mangledPointer)
        /\  VarExists(WorkGroupId(t)+1, mangledPointer)

        /\  LET pointerVar == GetVar(WorkGroupId(t)+1, mangledPointer)
                \* resultVar == GetVar(WorkGroupId(t)+1, mangledResult)
                resultVar == mangledResult
                evaluatedResultIndex == EvalExpr(t, WorkGroupId(t)+1, result.index)
                evaluatedPointerIndex == EvalExpr(t, WorkGroupId(t)+1, pointer.index)
                evaluatedValue == EvalExpr(t, WorkGroupId(t)+1, value)
            IN
                IF evaluatedResultIndex > 0 /\ evaluatedPointerIndex > 0 THEN
                    Assignment(t, {ChangeElementAt(resultVar, evaluatedResultIndex, pointerVar.value[evaluatedPointerIndex]), ChangeElementAt(pointerVar, evaluatedPointerIndex, evaluatedValue)})
                ELSE IF evaluatedResultIndex > 0 THEN
                    Assignment(t, {ChangeElementAt(resultVar, evaluatedResultIndex, pointerVar.value), Var(pointerVar.scope, pointerVar.name, evaluatedValue, pointerVar.index)})
                ELSE IF evaluatedPointerIndex > 0 THEN
                    Assignment(t, {Var(resultVar.scope, resultVar.name, pointerVar.value[evaluatedPointerIndex], resultVar.index), ChangeElementAt(pointerVar, evaluatedPointerIndex, evaluatedValue)})
                ELSE
                    Assignment(t, {Var(resultVar.scope, resultVar.name, pointerVar.value, resultVar.index), Var(pointerVar.scope, pointerVar.name, evaluatedValue, pointerVar.index)})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<state,  DynamicNodeSet, globalCounter, snapShotMap>>

(* result and pointer are variable, compare and value are literal *)
OpAtomicCompareExchange(t, result, pointer, value, comparator) ==
    LET mangledResult == Mangle(t, result)
        mangledPointer == Mangle(t, pointer)
    IN
        /\  IsVariable(mangledResult)
        /\  VarExists(WorkGroupId(t)+1, mangledPointer)

        /\  LET pointerVar == GetVar(WorkGroupId(t)+1, mangledPointer)
                \* resultVar == GetVar(WorkGroupId(t)+1, result)
                resultVar == mangledResult
                evaluatedPointerIndex == EvalExpr(t, WorkGroupId(t)+1, pointer.index)
                evaluatedResultIndex == EvalExpr(t, WorkGroupId(t)+1, result.index)
                evaluatedValue == EvalExpr(t, WorkGroupId(t)+1, value)
                evaluatedComparator == EvalExpr(t, WorkGroupId(t)+1, comparator)
            IN 
                IF pointerVar.value = evaluatedComparator THEN
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
        /\  UNCHANGED <<state,  DynamicNodeSet, globalCounter, snapShotMap>>


(* zheyuan chen: invocation is escaped from reconvergence if: 
1. The invocation executes OpTerminateInvocation or OpKill.
2. The last non-demoted, non-terminated invocation in the invocation's quad executes OpDemoteToHelperInvocation, OpTerminateInvocation, or OpKill.
3. The invocation executes OpReturn or OpReturnValue. Escaping in this manner only affects relations in the current function.
4. Executing OpBranch or OpBranchConditional causes an invocation to branch to the Merge Block or Continue Target for a merge instruction instance that strictly dominates I.
*)
\* Block with OpBranch as termination instruction is not part of construct
\* Hence, we do not need to update the Blocks and state
\* OpBranch(t, label) ==
\*     /\  LET curBlock == FindCurrentBlock( pc[t])
\*             targetBlock == FindBlockbyOpLabelIdx( GetVal(-1, label))
\*             labelVal == GetVal(-1, label)
\*             workGroupId == WorkGroupId(t)+1
\*         IN
\*             LET newBlocks == BranchUpdate(workGroupId, t, curBlock, curBlock.tangle[workGroupId], {labelVal}, labelVal)
\*                 newState == StateUpdate(workGroupId, t, newBlocks)
\*                 newDBSet == BranchUpdateDynamicExecutionGraph(workGroupId, t, {labelVal}, labelVal)
\*             IN 
\*                 /\  Blocks' = newBlocks
\*                 /\  state' = newState  
\*                 /\  DynamicNodeSet' = newDBSet 
\*     /\ pc' = [pc EXCEPT ![t] = GetVal(-1, label)]
\*     /\  UNCHANGED <<threadLocals, globalVars>>


OpBranch(t, label) ==
    /\  LET labelVal == GetVal(-1, label)
            workGroupId == WorkGroupId(t)+1
            newPc == [pc EXCEPT ![t] = GetVal(-1, label)]
        IN
            LET newDBSet == BranchUpdate(workGroupId, t, pc[t], <<labelVal>>, labelVal)
                newState == StateUpdate(workGroupId, t, newDBSet)
                newSnapShotMap == SnapShotUpdate(newDBSet, newState, t, newPc)
            IN 
                IF MeaningfulUpdate(newPc, newState, snapShotMap, newDBSet) THEN
                    /\  snapShotMap' = newSnapShotMap
                    /\  state' = newState  
                    /\  DynamicNodeSet' = newDBSet 
                    /\  pc' = newPc
                ELSE
                    \* /\ snapShotMap' = newSnapShotMap
                    /\ state' = newState
                    /\ DynamicNodeSet' = GetBackState(newPc, newState, snapShotMap, newDBSet).dynamicNodeSet
                    /\ pc' = newPc
                    /\ UNCHANGED  <<threadLocals, globalVars, snapShotMap>>
    /\  UNCHANGED <<threadLocals, globalVars, globalCounter>>


(* condition is an expression, trueLabel and falseLabel are integer representing pc *)
OpBranchConditional(t, condition, trueLabel, falseLabel) ==
    /\  IsLiteral(trueLabel)
    /\  IsLiteral(falseLabel)
    /\  LET trueLabelVal == GetVal(-1, trueLabel)
            falseLabelVal == GetVal(-1, falseLabel)
            workGroupId == WorkGroupId(t)+1

        IN
            IF EvalExpr(t, WorkGroupId(t)+1, condition) = TRUE THEN
                /\  LET newDBSet == BranchUpdate(workGroupId, t, pc[t], <<trueLabelVal, falseLabelVal>>, trueLabelVal)
                        newState == StateUpdate(workGroupId, t, newDBSet)
                        newPc == [pc EXCEPT ![t] = trueLabelVal]
                        newSnapShotMap == SnapShotUpdate(newDBSet, newState, t, newPc)
                    IN
                        IF MeaningfulUpdate(newPc, newState, snapShotMap, newDBSet) THEN
                            /\  snapShotMap' = newSnapShotMap
                            /\  state' = newState   
                            /\  DynamicNodeSet' = newDBSet
                            /\  pc' = newPc
                        ELSE 
                            \* /\ snapShotMap' = newSnapShotMap
                            /\ state' = newState
                            /\ DynamicNodeSet' = GetBackState(newPc, newState, snapShotMap, newDBSet).dynamicNodeSet
                            /\ pc' = newPc
                            /\ UNCHANGED <<threadLocals, globalVars, snapShotMap>>
            ELSE
                /\  LET newDBSet == BranchUpdate(workGroupId, t, pc[t], <<trueLabelVal, falseLabelVal>>, falseLabelVal)
                        newState == StateUpdate(workGroupId, t, newDBSet)
                        newPc == [pc EXCEPT ![t] = falseLabelVal]
                        newSnapShotMap == SnapShotUpdate(newDBSet, newState, t, newPc)

                    IN
                        IF MeaningfulUpdate(newPc, newState, snapShotMap, newDBSet) THEN
                            /\  snapShotMap' = newSnapShotMap
                            /\  state' = newState
                            /\  DynamicNodeSet' = newDBSet
                            /\  pc' = newPc
                        ELSE 
                            \* /\ snapShotMap' = newSnapShotMap
                            /\ state' = newState
                            /\ DynamicNodeSet' = GetBackState(newPc, newState, snapShotMap, newDBSet).dynamicNodeSet
                            /\ pc' = newPc
                            /\ UNCHANGED <<threadLocals, globalVars, snapShotMap>>
    /\  UNCHANGED <<threadLocals, globalVars, globalCounter>>

    
\* zheyuan: need more tests
\* need to update it
OpSwitch(t, selector, default, literals, ids) ==
    /\  LET defaultVal == GetVal(-1, default)
            literalsVal == [idx \in 1..Len(literals) |-> GetVal(-1, literals[idx])]
            idsVal == [idx \in 1..Len(ids) |-> GetVal(-1, ids[idx])]
            workGroupId == WorkGroupId(t)+1
        IN
            IF EvalExpr(t, WorkGroupId(t)+1, selector) \in SeqToSet(literalsVal) THEN
                LET val == EvalExpr(t, WorkGroupId(t)+1, selector)
                    index == CHOOSE i \in 1..Len(literalsVal): literalsVal[i] = val 
                IN
                    /\  LET newDBSet == BranchUpdate(workGroupId, t, pc[t], idsVal, idsVal[index])
                            newState == StateUpdate(workGroupId, t, newDBSet)
                            newPc == [pc EXCEPT ![t] = idsVal[index]]
                            newSnapShotMap == SnapShotUpdate(newDBSet, newState, t, newPc)
                        IN
                            IF MeaningfulUpdate(newPc, newState, snapShotMap, newDBSet) THEN
                                /\  snapShotMap' = newSnapShotMap
                                /\  state' = newState
                                /\  DynamicNodeSet' = newDBSet
                                /\  pc' = newPc
                            ELSE 
                                /\  UNCHANGED <<pc, state, threadLocals, globalVars, DynamicNodeSet, snapShotMap>>
            ELSE
                /\  LET newDBSet == BranchUpdate(workGroupId, t, pc[t], idsVal, defaultVal)
                        newState == StateUpdate(workGroupId, t, newDBSet)
                        newPc == [pc EXCEPT ![t] = defaultVal]
                        newSnapShotMap == SnapShotUpdate(newDBSet, newState, t, newPc)
                    IN
                        IF MeaningfulUpdate(newPc, newState, snapShotMap, newDBSet) THEN
                            /\  snapShotMap' = newSnapShotMap
                            /\  state' = newState
                            /\  DynamicNodeSet' = newDBSet
                            /\  pc' = newPc
                        ELSE
                            /\  UNCHANGED <<pc, state, threadLocals, globalVars, DynamicNodeSet, snapShotMap>>
    /\  UNCHANGED <<threadLocals, globalVars, globalCounter>>

(* structured loop, must immediately precede block termination instruction, which means it must be second-to-last instruction in its block *)
OpLabel(t, label) ==
    /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
    /\  UNCHANGED <<state, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>

(* structured loop, must immediately precede block termination instruction, which means it must be second-to-last instruction in its block *)
OpLoopMerge(t, mergeLabel, continueTarget) ==
    \* because the merge instruction must be the second to last instruction in the block, we can find the currren block by looking at the termination instruction
    \* /\  LET workGroupId == WorkGroupId(t) + 1
    \*         newDBSet == LoopMergeUpdate(workGroupId, t, FindCurrentBlock(Blocks, pc[t]).opLabelIdx, mergeLabel)
    \*     IN
    \*         /\  DynamicNodeSet' = newDBSet
    /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
    /\  UNCHANGED <<state, threadLocals, globalVars, DynamicNodeSet, globalCounter, snapShotMap>>

(* structured switch/if, must immediately precede block termination instruction, which means it must be second-to-last instruction in its block  *)
OpSelectionMerge(t, mergeLabel) ==
    \* because the merge instruction must be the second to last instruction in the block, we can find the currren block by looking at the termination instruction
    /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
    /\  UNCHANGED <<state, threadLocals, globalVars, DynamicNodeSet, globalCounter, snapShotMap>>

\* zheyuan chen: update tangle
Terminate(t) ==
    LET workGroupId == WorkGroupId(t)+1
    IN
        LET newDBSet == TerminateUpdate(workGroupId, t)
            newState == StateUpdate(workGroupId, t, newDBSet)
        IN 
            /\  DynamicNodeSet' = newDBSet
            /\  state' = [newState EXCEPT ![t] = "terminated"]
            /\  UNCHANGED <<pc, threadLocals, globalVars, globalCounter, snapShotMap>>

ExecuteInstruction(t) ==
    LET workgroupId == WorkGroupId(t)+1
    IN
        IF state[t] # "terminated" THEN
            IF  ThreadInstructions[t][pc[t]] = "Terminate" THEN
                Terminate(t)
            ELSE IF ThreadInstructions[t][pc[t]] = "Assignment" THEN
                /\  Assignment(t, {Mangle(t,ThreadArguments[t][pc[t]][1])})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state,  DynamicNodeSet, globalCounter, snapShotMap>>
            ELSE IF ThreadInstructions[t][pc[t]] = "GetGlobalId" THEN
                GetGlobalId(t, ThreadArguments[t][pc[t]][1])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpAtomicIncrement" THEN
                OpAtomicIncrement(t, ThreadArguments[t][pc[t]][1])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpAtomicDecrement" THEN
                OpAtomicDecrement(t, ThreadArguments[t][pc[t]][1])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpLogicalOr" THEN 
                OpLogicalOr(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpLogicalAnd" THEN
                OpLogicalAnd(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpLogicalEqual" THEN
                OpLogicalEqual(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpLogicalNotEqual" THEN
                OpLogicalNotEqual(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpLogicalNot" THEN
                OpLogicalNot(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2])
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
            ELSE IF ThreadInstructions[t][pc[t]] = "OpAtomicAdd" THEN
                OpAtomicAdd(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpSub" THEN
                OpSub(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpAtomicSub" THEN
                OpAtomicSub(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
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
            ELSE IF ThreadInstructions[t][pc[t]] = "OpSwitch" THEN
                OpSwitch(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3], ThreadArguments[t][pc[t]][4])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpControlBarrier" THEN
                OpControlBarrier(t, ThreadArguments[t][pc[t]][1])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpGroupAll" THEN
                OpGroupAll(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpGroupAny" THEN
                OpGroupAny(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpGroupNonUniformAll" THEN
                OpGroupNonUniformAll(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpGroupNonUniformAny" THEN
                OpGroupNonUniformAny(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpLoopMerge" THEN
                OpLoopMerge(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpSelectionMerge" THEN
                OpSelectionMerge(t, ThreadArguments[t][pc[t]][1])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpLabel" THEN
                OpLabel(t, ThreadArguments[t][pc[t]][1])
            ELSE
                FALSE
        ELSE 
            /\ UNCHANGED << threadVars, threadLocals, globalVars,  DynamicNodeSet, globalCounter, snapShotMap>>


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
---- MODULE MCThreads ----
LOCAL INSTANCE Integers
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE TLC
VARIABLES pc, state, threadLocals, globalVars, DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView

(* Thread Configuration *)
INSTANCE  MCProgram

ThreadState == {"ready", "workgroup", "subgroup", "terminated"}
threadVars == <<pc, state>>

InitThreadVars ==
    /\  pc = [t \in Threads |-> 1]
    /\  state = [t \in Threads |-> "ready"]
    /\  threadLocals = [t \in Threads |-> {}]
    
InitThreads == 
    /\  InitThreadVars

RAVars == <<modOrder, threadView>>

RAEnabled == MemoryModel = "RA"

RAAtomicInstructionSet == {"OpAtomicLoad", "OpAtomicStore", "OpAtomicOr", "OpAtomicAnd"}

RAPointerArgument(t, insIdx) ==
    IF ThreadInstructions[t][insIdx] = "OpAtomicLoad" THEN
        Mangle(t, ThreadArguments[t][insIdx][2])
    ELSE
        Mangle(t, ThreadArguments[t][insIdx][1])

RAPointerIndexArgument(t, insIdx) ==
    IF ThreadInstructions[t][insIdx] = "OpAtomicLoad" THEN
        ThreadArguments[t][insIdx][2].index
    ELSE
        ThreadArguments[t][insIdx][1].index

IsScalarRAInstruction(t, insIdx) ==
    /\ ThreadInstructions[t][insIdx] \in RAAtomicInstructionSet
    /\ LET ptr == RAPointerArgument(t, insIdx)
           ptrIdx == RAPointerIndexArgument(t, insIdx)
       IN
           /\ (IsGlobal(ptr) \/ IsShared(ptr))
           /\ IsIndex(ptrIdx)
           /\ ptrIdx.realIndex = -1

RAAddress(ptr) ==
    [scope |-> ptr.scope, name |-> ptr.name]

RAAddressesForThread(t) ==
    {RAAddress(RAPointerArgument(t, insIdx)) :
        insIdx \in {i \in DOMAIN ThreadInstructions[t] : IsScalarRAInstruction(t, i)}}

RAAddressDomain ==
    UNION {RAAddressesForThread(t) : t \in Threads}

RAInitialPointerVar(addr) ==
    Var(addr.scope, addr.name, 0, Index(-1))

RAInitialValue(addr) ==
    IF addr.scope = "global" /\ \E variable \in globalVars : variable.name = addr.name THEN
        GetVar(1, RAInitialPointerVar(addr)).value
    ELSE IF addr.scope = "shared" /\ \E wg \in 1..NumWorkGroups : VarExists(wg, RAInitialPointerVar(addr)) THEN
        LET wg == CHOOSE w \in 1..NumWorkGroups : VarExists(w, RAInitialPointerVar(addr))
        IN
            GetVar(wg, RAInitialPointerVar(addr)).value
    ELSE
        0

RAInitialView ==
    [a \in RAAddressDomain |-> 1]

RAWrite(value, tid, snapView) ==
    [value |-> value, tid |-> tid, snapView |-> snapView]

InitRA ==
    /\ modOrder = [a \in RAAddressDomain |-> <<RAWrite(RAInitialValue(a), 0, RAInitialView)>>]
    /\ threadView = [t \in Threads |-> RAInitialView]

InitPlainMemory ==
    /\ modOrder = [a \in RAAddressDomain |-> <<>>]
    /\ threadView = [t \in Threads |-> [a \in RAAddressDomain |-> 0]]

InitMemoryModel ==
    CASE MemoryModel = "RA" -> InitRA
         [] MemoryModel = "Plain" -> InitPlainMemory
         [] OTHER -> FALSE

MaxNat(x, y) ==
    IF x >= y THEN x ELSE y

HasConcreteIndex(idx) ==
    idx >= 0

IsScalarIndex(idx) ==
    idx < 0

JoinRAViews(left, right) ==
    [a \in RAAddressDomain |-> MaxNat(left[a], right[a])]

IsRAEligiblePointer(mangledPointer, evaluatedPointerIndex) ==
    /\ RAEnabled
    /\ (IsGlobal(mangledPointer) \/ IsShared(mangledPointer))
    /\ IsScalarIndex(evaluatedPointerIndex)
    /\ RAAddress(mangledPointer) \in RAAddressDomain

RAReadChoices(t, addr) ==
    {idx \in 1..Len(modOrder[addr]) : idx >= threadView[t][addr]}

RAJoinedThreadView(t, addr, readIdx) ==
    LET localView == [threadView[t] EXCEPT ![addr] = MaxNat(threadView[t][addr], readIdx)]
    IN
        JoinRAViews(localView, modOrder[addr][readIdx].snapView)

RALoadStateUpdate(t, addr, readIdx) ==
    /\ UNCHANGED modOrder
    /\ threadView' = [threadView EXCEPT ![t] = RAJoinedThreadView(t, addr, readIdx)]

RAStoreStateUpdate(t, addr, valueToStore) ==
    LET newWrite == RAWrite(valueToStore, t, threadView[t])
        newPos == Len(modOrder[addr]) + 1
    IN
        /\ modOrder' = [modOrder EXCEPT ![addr] = Append(@, newWrite)]
        /\ threadView' = [threadView EXCEPT ![t][addr] = newPos]

RARMWReadIndex(addr) ==
    Len(modOrder[addr])

RARMWStateUpdate(t, addr, readIdx, valueToStore) ==
    LET joinedView == RAJoinedThreadView(t, addr, readIdx)
        newWrite == RAWrite(valueToStore, t, joinedView)
        newPos == Len(modOrder[addr]) + 1
    IN
        /\ modOrder' = [modOrder EXCEPT ![addr] = Append(@, newWrite)]
        /\ threadView' =
            [threadView EXCEPT ![t] = [a \in RAAddressDomain |-> IF a = addr THEN newPos ELSE joinedView[a]]]

newSnapShot(localPc, localState, localThreadLocals, localGlobalVars, dynamicBlockSet, localCounter, localModOrder, localThreadView) ==
    [
        pc |-> localPc,
        state |-> localState,
        threadLocals |-> localThreadLocals,
        globalVars |-> localGlobalVars,
        dynamicBlockSet |-> dynamicBlockSet,
        globalCounter |-> localCounter,
        modOrder |-> localModOrder,
        threadView |-> localThreadView
    ]

RemoveId(dynamicBlock) == [dynamicBlock EXCEPT !.id = 0, !.mergeStack = <<>>, !.children = {}, !.sis = EmptySIS]



InitSnapShotMap ==
    LET newDBIds == {db.labelIdx : db \in DynamicBlockSet} IN
         snapShotMap = { newSnapShot(<<>>, <<>>, <<>>, {}, DynamicBlockSet, 1, modOrder, threadView) : db \in DynamicBlockSet}


LowestPcWithinSubgroup(sid, wgid) == Min({pc[tid]: tid \in ThreadsWithinSubgroup(sid, wgid)})

MinThreadWithinWorkGroup(workGroupId) ==
    Min(ThreadsWithinWorkGroup(workGroupId))

cleanIntermediateVar(t) == 
    /\  LET workGroupId == WorkGroupId(t)+1
            currthreadLocals == threadLocals[WorkGroupId(t)+1]
        IN
            LET eliminatedVars == {currVar \in currthreadLocals : currVar.scope = "intermediate"}
            IN
                /\  threadLocals' =  [threadLocals EXCEPT ![workGroupId] = threadLocals[workGroupId] \ eliminatedVars]


 UpdateState(tid, State) ==
     /\  state' = [state EXCEPT ![tid] = State]
    
StateUpdate(wgid, t, newDBSet) ==
    [thread \in Threads |-> 
        IF \E DB \in newDBSet :
            /\ state[thread] # "terminated"
            /\ state[thread] # "ready"
            /\ thread \in DB.currentThreadSet[wgid]
            /\ \A tid \in DB.currentThreadSet[wgid] : pc[tid] = pc[thread] (* /\ ThreadInstructions[1][pc[tid]] \in TangledInstructionSet *) /\ state[tid] = state[thread]
            /\ DB.unknownSet[wgid] = {}
        THEN 
            "ready"
        ELSE
            state[thread]
    ]


Basic(s) ==
  [ pc           |-> s.pc,
    state        |-> s.state,
    threadLocals |-> s.threadLocals,
    globalVars   |-> s.globalVars,
    dynamicBlock  |-> s.dynamicBlock]

InsertMultipleSnapShots(map, snapshots) ==
    map \cup snapshots

SnapShotUpdate(newDBSet, newState, t, localPc, newCounter) ==
        LET newDBs == newDBSet \ DynamicBlockSet
            newDBIds == {db.labelIdx : db \in newDBs}
            snapShots == {newSnapShot(localPc, newState, threadLocals, globalVars, newDBSet, newCounter, modOrder, threadView)}
        IN
            InsertMultipleSnapShots(snapShotMap, snapShots)

\* Once the Arrive condition holds we release every waiting thread back to "ready".
StateUpdateSubgroup(wgid, active_subgroup_threads, newDBSet) ==
    [thread \in Threads |->
        IF thread \in active_subgroup_threads THEN
            "ready"
        ELSE
            state[thread]
    ]

SnapShotUpdateSubgroup(newDBSet, newState, active_subgroup_threads, localPc, newCounter) ==
        LET newDBs == newDBSet \ DynamicBlockSet
            newDBIds == {db.labelIdx : db \in newDBs}
            snapShots == {newSnapShot(localPc, newState, threadLocals, globalVars, newDBSet, newCounter, modOrder, threadView)}
        IN
            InsertMultipleSnapShots(snapShotMap, snapShots)

MeaningfulUpdate(localPc, newState, oldSnapShotMap, newDBSet) ==
    LET newDBs == newDBSet \ DynamicBlockSet
    IN
        { snapshot \in oldSnapShotMap :
                /\ snapshot["pc"] = localPc
                /\ snapshot["state"] = newState
                /\ snapshot["threadLocals"] = threadLocals
                /\ snapshot["globalVars"] = globalVars
                /\ snapshot["modOrder"] = modOrder
                /\ snapshot["threadView"] = threadView
        }

GetBackState(localPc, newState, oldSnapShotMap, newDBSet) ==
    CHOOSE snapshot \in oldSnapShotMap:
        /\ snapshot["pc"] = localPc
        /\ snapshot["state"] = newState
        /\ snapshot["threadLocals"] = threadLocals
        /\ snapshot["globalVars"] = globalVars
        /\ snapshot["modOrder"] = modOrder
        /\ snapshot["threadView"] = threadView
        /\ snapshot["dynamicBlock"] = RemoveId(CHOOSE db \in (newDBSet \ DynamicBlockSet): TRUE)

    

\* https://en.wikipedia.org/wiki/Bitwise_operation#Mathematical_equivalents
RECURSIVE And(_,_,_,_)
LOCAL And(x,y,n,m) == 
        LET exp == 2^n
        IN IF m = 0 
           THEN 0
           ELSE exp * ((x \div exp) % 2) * ((y \div exp) % 2) 
                    + And(x,y,n+1,m \div 2)

x & y == 
    (***************************************************************************)
    (* Bitwise AND of (non-negative) x and y (defined for Nat \cup {0}).       *)
    (***************************************************************************)
    IF x >= y THEN And(x, y, 0, x) ELSE And(y, x, 0, y) \* Infix variant of And(x,y)

-------------------------------------------------------------------------------

RECURSIVE Or(_,_,_,_)
LOCAL Or(x,y,n,m) == 
        LET exp == 2^n
            xdm == (x \div exp) % 2
            ydm == (y \div exp) % 2
        IN IF m = 0 
           THEN 0
           ELSE exp * (((xdm + ydm) + (xdm * ydm)) % 2)
                        + Or(x,y,n+1,m \div 2)

x | y == 
    (***************************************************************************)
    (* Bitwise OR of (non-negative) x and y (defined for Nat \cup {0}).        *)
    (***************************************************************************)
    IF x >= y THEN Or(x, y, 0, x) ELSE Or(y, x, 0, y) \* Infix variant of Or(x,y)

-------------------------------------------------------------------------------

RECURSIVE Xor(_,_,_,_)
LOCAL Xor(x,y,n,m) == 
        LET exp == 2^n
        IN IF m = 0 
           THEN 0
           ELSE exp * (((x \div exp) + (y \div exp)) % 2) 
                    + Xor(x,y,n+1,m \div 2)

x ^^ y ==   \* single "^" already taken by Naturals.tla
    (***************************************************************************)
    (* Bitwise XOR of (non-negative) x and y (defined for Nat \cup {0}).       *)
    (***************************************************************************)
    IF x >= y THEN Xor(x, y, 0, x) ELSE Xor(y, x, 0, y) \* Infix variant of Xor(x,y)

-------------------------------------------------------------------------------

RECURSIVE NotR(_,_,_)
LOCAL NotR(x,n,m) == 
    LET exp == 2^n
        xdm == (x \div exp) % 2
    IN IF m = 0 
        THEN 0
        ELSE exp * ((xdm + 1) % 2)
                    + NotR(x,n+1,m \div 2)

-------------------------------------------------------------------------------

RECURSIVE shiftR(_,_)
shiftR(n,pos) == 
    (***************************************************************************)
    (* Logical bit-shifting the (non-negative) n by pos positions to the right *)
    (* shifting zeros in from the left/MSB (defined for Nat \cup {0}).         *)
    (***************************************************************************)
    IF pos = 0 
    THEN n
    ELSE LET odd(z) == z % 2 = 1
             m == IF odd(n) THEN (n-1) \div 2 ELSE n \div 2
         IN shiftR(m, pos - 1)

RECURSIVE shiftL(_,_)
shiftL(n, pos) ==
    (***************************************************************************)
    (* Logical bit-shifting the (non-negative) n by pos positions to the left   *)
    (* shifting zeros in from the right/LSB.                                  *)
    (***************************************************************************)
    IF pos = 0 
    THEN n
    ELSE shiftL(2 * n, pos - 1)

Assignment(t, vars) == 
    /\  LET workGroupId == WorkGroupId(t)+1
            AssGlobalVars == {var \in vars : var.scope = "global"} 
            AssthreadLocals == {var \in vars : var.scope # "global"}
            currthreadLocals == threadLocals[WorkGroupId(t)+1]
        IN
            \* try to eliminated var with old value and intermediate var
            LET eliminatedthreadLocals == {currVar \in currthreadLocals : \E var \in vars: (currVar.name = var.name /\ currVar.scope = var.scope)}
                eliminatedGlobalVars == {currVar \in globalVars : \E var \in vars: (currVar.name = var.name /\ currVar.scope = var.scope)}
            IN
                /\  threadLocals' =  [threadLocals EXCEPT ![workGroupId] = (threadLocals[workGroupId] \ eliminatedthreadLocals) \union AssthreadLocals]
                /\  globalVars' = (globalVars \ eliminatedGlobalVars) \union AssGlobalVars
                \* /\  Print(AssthreadLocals, TRUE)

\* This is the inner helper function to return the array with updated element. It does not change the next state of the variable
ChangeElementAt(var, index, value) ==
        Var(var.scope, var.name, [currentIndex \in DOMAIN var.value |-> IF currentIndex = index THEN value ELSE var.value[currentIndex] ], var.index)

RAResultAssignments(t, result, valueRead) ==
    LET workGroupId == WorkGroupId(t) + 1
        mangledResult == Mangle(t, result)
    IN
        IF IsIntermediate(mangledResult) THEN
            {Var(mangledResult.scope, mangledResult.name, valueRead, Index(-1))}
        ELSE
            LET resultVar == mangledResult
                evaluatedResultIndex == EvalExpr(t, workGroupId, result.index)
            IN
                IF HasConcreteIndex(evaluatedResultIndex) THEN
                    {ChangeElementAt(resultVar, evaluatedResultIndex, valueRead)}
                ELSE
                    {Var(resultVar.scope, resultVar.name, valueRead, Index(-1))}


OpLogicalOr(t, var, operand1, operand2) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workGroupId, mangledOperand1)
                operand2Val == GetVal(workGroupId, mangledOperand2)
            IN
                /\  IF operand1Val = TRUE \/ operand2Val = TRUE THEN
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars, DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>

OpLogicalAnd(t, var, operand1, operand2) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workGroupId, mangledOperand1)
                operand2Val == GetVal(workGroupId, mangledOperand2)
            IN
                /\  IF operand1Val = TRUE /\ operand2Val = TRUE THEN
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>

OpLogicalEqual(t, var, operand1, operand2) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workGroupId, mangledOperand1)
                operand2Val == GetVal(workGroupId, mangledOperand2)
            IN
                /\  IF operand1Val = operand2Val THEN
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>

OpLogicalNotEqual(t, var, operand1, operand2) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workGroupId, mangledOperand1)
                operand2Val == GetVal(workGroupId, mangledOperand2)
            IN
                /\  IF operand1Val # operand2Val THEN
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
OpLogicalNot(t, var, operand) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand == Mangle(t, operand)
    IN
        /\  LET operandVal == GetVal(workGroupId, mangledOperand)
            IN
                /\  IF operandVal = FALSE THEN
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>

OpAtomicOr(t, var, pointer, value) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledPointer == Mangle(t, pointer)
        mangledValue == Mangle(t, value)

    IN
        /\  LET pointerVar == GetVar(workGroupId, mangledPointer)
                evaluatedPointerIndex == EvalExpr(t, workGroupId, pointer.index)
                pointerVal == GetVal(workGroupId, mangledPointer)
                valueVal == GetVal(workGroupId, mangledValue)
                raEligible == IsRAEligiblePointer(mangledPointer, evaluatedPointerIndex)
                raAddr == RAAddress(mangledPointer)
            IN
                IF raEligible THEN
                    LET readIdx == RARMWReadIndex(raAddr)
                        oldValue == modOrder[raAddr][readIdx].value
                        newValue == oldValue | valueVal
                    IN
                        /\ Assignment(t, RAResultAssignments(t, var, oldValue) \cup {Var(mangledPointer.scope, mangledPointer.name, newValue, pointerVar.index)})
                        /\ RARMWStateUpdate(t, raAddr, readIdx, newValue)
                        /\ pc' = [pc EXCEPT ![t] = pc[t] + 1]
                        /\ UNCHANGED <<state, DynamicBlockSet, globalCounter, snapShotMap>>
                ELSE
                    /\ Assignment(t, {Var(MangleVar.scope, MangleVar.name, pointerVal, Index(-1)), Var(mangledPointer.scope, mangledPointer.name, pointerVal | valueVal, Index(-1))})
                    /\ pc' = [pc EXCEPT ![t] = pc[t] + 1]
                    /\ UNCHANGED <<state, DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>

\* Atomics that emulate a slot update also use the synchronous Arrive/Execute flow.
OpAtomicOrSync(t, var, pointer, value) ==
    LET mangledVar == Mangle(t, var)
        mangledPointer == Mangle(t, pointer)
        mangledValue == Mangle(t, value)
        workGroupId == WorkGroupId(t) + 1
        sgIdx == SubgroupIndex(t)
        currentPc == pc[t]
        sthreads == ThreadsWithinSubgroupNonTerminated(SubgroupId(t), WorkGroupId(t))
        currentDB == CurrentDynamicBlock(workGroupId, t)
        active_subgroup_threads == currentDB.currentThreadSet[workGroupId] \intersect sthreads
        unknown_subgroup_threads == currentDB.unknownSet[workGroupId] \intersect sthreads
        aligned == unknown_subgroup_threads = {} /\ \A sthread \in active_subgroup_threads: pc[sthread] = currentPc
        pointerVar == GetVar(workGroupId, mangledPointer)
        evaluatedPointerIndex == EvalExpr(t, workGroupId, pointer.index)
        pointerVal == GetVal(workGroupId, mangledPointer)
        valueVal == GetVal(workGroupId, mangledValue)
        raEligible == IsRAEligiblePointer(mangledPointer, evaluatedPointerIndex)
        raAddr == RAAddress(mangledPointer)
        assignmentSet == {Var(mangledVar.scope, mangledVar.name, pointerVal, Index(-1)),
                          Var(mangledPointer.scope, mangledPointer.name, pointerVal | valueVal, Index(-1))}
        remaining == {sthread \in active_subgroup_threads : sthread # t /\ pc[sthread] = currentPc}
    IN
        /\ (IsVariable(mangledVar) \/ IsIntermediate(mangledVar))
        /\ IsVariable(mangledPointer)
        /\ VarExists(workGroupId, mangledPointer)
        /\ IF currentDB.sis[workGroupId][sgIdx][currentPc] = FALSE THEN
                IF ~aligned THEN
                    /\ state' = [state EXCEPT ![t] = "subgroup"]
                    /\ UNCHANGED <<pc, threadLocals, globalVars, DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
                ELSE
                    LET newDBSet == SetSISInDB(DynamicBlockSet, currentDB, workGroupId, sgIdx, currentPc, TRUE)
                    IN
                        /\ DynamicBlockSet' = newDBSet
                        /\ state' = StateUpdateSubgroup(workGroupId, active_subgroup_threads, newDBSet)
                        /\ UNCHANGED <<pc, threadLocals, globalVars, globalCounter, snapShotMap, modOrder, threadView>>
           ELSE
                LET newDBSet == IF remaining = {}
                                 THEN SetSISInDB(DynamicBlockSet, currentDB, workGroupId, sgIdx, currentPc, FALSE)
                                 ELSE DynamicBlockSet
                IN
                    IF raEligible THEN
                        LET readIdx == RARMWReadIndex(raAddr)
                            oldValue == modOrder[raAddr][readIdx].value
                            newValue == oldValue | valueVal
                        IN
                            /\ Assignment(t, RAResultAssignments(t, var, oldValue) \cup {Var(mangledPointer.scope, mangledPointer.name, newValue, pointerVar.index)})
                            /\ RARMWStateUpdate(t, raAddr, readIdx, newValue)
                            /\ pc' = [pc EXCEPT ![t] = pc[t] + 1]
                            /\ DynamicBlockSet' = newDBSet
                            /\ state' = [state EXCEPT ![t] = "ready"]
                            /\ UNCHANGED <<globalCounter, snapShotMap>>
                    ELSE
                        /\ Assignment(t, assignmentSet)
                        /\ pc' = [pc EXCEPT ![t] = pc[t] + 1]
                        /\ DynamicBlockSet' = newDBSet
                        /\ state' = [state EXCEPT ![t] = "ready"]
                        /\ UNCHANGED <<globalCounter, snapShotMap, modOrder, threadView>>


OpAtomicAnd(t, var, pointer, value) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledPointer == Mangle(t, pointer)
        mangledValue == Mangle(t, value)

    IN
        /\  LET pointerVar == GetVar(workGroupId, mangledPointer)
                evaluatedPointerIndex == EvalExpr(t, workGroupId, pointer.index)
                pointerVal == GetVal(workGroupId, mangledPointer)
                valueVal == GetVal(workGroupId, mangledValue)
                raEligible == IsRAEligiblePointer(mangledPointer, evaluatedPointerIndex)
                raAddr == RAAddress(mangledPointer)
            IN
                IF raEligible THEN
                    LET readIdx == RARMWReadIndex(raAddr)
                        oldValue == modOrder[raAddr][readIdx].value
                        newValue == oldValue & valueVal
                    IN
                        /\ Assignment(t, RAResultAssignments(t, var, oldValue) \cup {Var(mangledPointer.scope, mangledPointer.name, newValue, pointerVar.index)})
                        /\ RARMWStateUpdate(t, raAddr, readIdx, newValue)
                        /\ pc' = [pc EXCEPT ![t] = pc[t] + 1]
                        /\ UNCHANGED <<state, DynamicBlockSet, globalCounter, snapShotMap>>
                ELSE
                    /\ Assignment(t, {Var(MangleVar.scope, MangleVar.name, pointerVal, Index(-1)), Var(mangledPointer.scope, mangledPointer.name, pointerVal & valueVal, Index(-1))})
                    /\ pc' = [pc EXCEPT ![t] = pc[t] + 1]
                    /\ UNCHANGED <<state, DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>

OpAtomicAndSync(t, var, pointer, value) ==
    LET mangledVar == Mangle(t, var)
        mangledPointer == Mangle(t, pointer)
        mangledValue == Mangle(t, value)
        workGroupId == WorkGroupId(t) + 1
        sgIdx == SubgroupIndex(t)
        currentPc == pc[t]
        sthreads == ThreadsWithinSubgroupNonTerminated(SubgroupId(t), WorkGroupId(t))
        currentDB == CurrentDynamicBlock(workGroupId, t)
        active_subgroup_threads == currentDB.currentThreadSet[workGroupId] \intersect sthreads
        unknown_subgroup_threads == currentDB.unknownSet[workGroupId] \intersect sthreads
        aligned == unknown_subgroup_threads = {} /\ \A sthread \in active_subgroup_threads: pc[sthread] = currentPc
        pointerVar == GetVar(workGroupId, mangledPointer)
        evaluatedPointerIndex == EvalExpr(t, workGroupId, pointer.index)
        pointerVal == GetVal(workGroupId, mangledPointer)
        valueVal == GetVal(workGroupId, mangledValue)
        raEligible == IsRAEligiblePointer(mangledPointer, evaluatedPointerIndex)
        raAddr == RAAddress(mangledPointer)
        assignmentSet == {Var(mangledVar.scope, mangledVar.name, pointerVal, Index(-1)),
                          Var(mangledPointer.scope, mangledPointer.name, pointerVal & valueVal, Index(-1))}
        remaining == {sthread \in active_subgroup_threads : sthread # t /\ pc[sthread] = currentPc}
    IN
        /\ (IsVariable(mangledVar) \/ IsIntermediate(mangledVar))
        /\ IsVariable(mangledPointer)
        /\ VarExists(workGroupId, mangledPointer)
        /\ IF currentDB.sis[workGroupId][sgIdx][currentPc] = FALSE THEN
                IF ~aligned THEN
                    /\ state' = [state EXCEPT ![t] = "subgroup"]
                    /\ UNCHANGED <<pc, threadLocals, globalVars, DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
                ELSE
                    LET newDBSet == SetSISInDB(DynamicBlockSet, currentDB, workGroupId, sgIdx, currentPc, TRUE)
                    IN
                        /\ DynamicBlockSet' = newDBSet
                        /\ state' = StateUpdateSubgroup(workGroupId, active_subgroup_threads, newDBSet)
                        /\ UNCHANGED <<pc, threadLocals, globalVars, globalCounter, snapShotMap, modOrder, threadView>>
           ELSE
                LET newDBSet == IF remaining = {}
                                 THEN SetSISInDB(DynamicBlockSet, currentDB, workGroupId, sgIdx, currentPc, FALSE)
                                 ELSE DynamicBlockSet
                IN
                    IF raEligible THEN
                        LET readIdx == RARMWReadIndex(raAddr)
                            oldValue == modOrder[raAddr][readIdx].value
                            newValue == oldValue & valueVal
                        IN
                            /\ Assignment(t, RAResultAssignments(t, var, oldValue) \cup {Var(mangledPointer.scope, mangledPointer.name, newValue, pointerVar.index)})
                            /\ RARMWStateUpdate(t, raAddr, readIdx, newValue)
                            /\ pc' = [pc EXCEPT ![t] = pc[t] + 1]
                            /\ DynamicBlockSet' = newDBSet
                            /\ state' = [state EXCEPT ![t] = "ready"]
                            /\ UNCHANGED <<globalCounter, snapShotMap>>
                    ELSE
                        /\ Assignment(t, assignmentSet)
                        /\ pc' = [pc EXCEPT ![t] = pc[t] + 1]
                        /\ DynamicBlockSet' = newDBSet
                        /\ state' = [state EXCEPT ![t] = "ready"]
                        /\ UNCHANGED <<globalCounter, snapShotMap, modOrder, threadView>>
OpBitcast(t, var, operand) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand == Mangle(t, operand)

    IN
        /\  LET operandVal == GetVal(workGroupId, mangledOperand)
            IN
                Assignment(t, {Var(MangleVar.scope, MangleVar.name, operandVal, Index(-1))})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<state, DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>

OpShiftLeftLogical(t, var, base, shift) == 
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledBase == Mangle(t, base)
        mangledShift == Mangle(t, shift)

    IN
        /\  LET baseVal == GetVal(workGroupId, mangledBase)
                shiftVal == GetVal(workGroupId, mangledShift)
            IN
                Assignment(t, {Var(MangleVar.scope, MangleVar.name, shiftL(baseVal, shiftVal), Index(-1))})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]   
        /\  UNCHANGED <<state, DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>

OpShiftRightLogical(t, var, base, shift) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledBase == Mangle(t, base)
        mangledShift == Mangle(t, shift)

    IN
        /\  LET baseVal == GetVal(workGroupId, mangledBase)
                shiftVal == GetVal(workGroupId, mangledShift)
            IN
                Assignment(t, {Var(MangleVar.scope, MangleVar.name, shiftR(baseVal, shiftVal), Index(-1))})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<state, DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>

OpEqual(t, var, operand1, operand2) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workGroupId, mangledOperand1)
                operand2Val == GetVal(workGroupId, mangledOperand2)
            IN
                /\  IF operand1Val = operand2Val THEN
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>


OpNotEqual(t, var, operand1, operand2) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workGroupId, mangledOperand1)
                operand2Val == GetVal(workGroupId, mangledOperand2)
            IN
                /\  IF operand1Val # operand2Val THEN
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>


OpLess(t, var, operand1, operand2) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workGroupId, mangledOperand1)
                operand2Val == GetVal(workGroupId, mangledOperand2)
            IN
                /\  IF operand1Val < operand2Val THEN
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>

OpLessOrEqual(t, var, operand1, operand2) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workGroupId, mangledOperand1)
                operand2Val == GetVal(workGroupId, mangledOperand2)
            IN
                /\  IF operand1Val <= operand2Val THEN
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>

OpGreater(t, var, operand1, operand2) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workGroupId, mangledOperand1)
                operand2Val == GetVal(workGroupId, mangledOperand2)
            IN
                /\  IF operand1Val > operand2Val THEN
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>

OpGreaterOrEqual(t, var, operand1, operand2) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workGroupId, mangledOperand1)
                operand2Val == GetVal(workGroupId, mangledOperand2)
            IN
                /\  IF operand1Val >= operand2Val THEN
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, TRUE, Index(-1))})
                    ELSE
                        Assignment(t, {Var(MangleVar.scope, MangleVar.name, FALSE, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>

OpBitwiseOr(t, var, operand1, operand2) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workGroupId, mangledOperand1)
                operand2Val == GetVal(workGroupId, mangledOperand2)
            IN
                Assignment(t, {Var(MangleVar.scope, MangleVar.name, operand1Val | operand2Val, Index(-1))})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]   
        /\  UNCHANGED <<state, DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>     

OpBitwiseAnd(t, var, operand1, operand2) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workGroupId, mangledOperand1)
                operand2Val == GetVal(workGroupId, mangledOperand2)
            IN
                Assignment(t, {Var(MangleVar.scope, MangleVar.name, operand1Val & operand2Val, Index(-1))})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<state, DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>

OpAdd(t, var, operand1, operand2) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workGroupId, mangledOperand1)
                operand2Val == GetVal(workGroupId, mangledOperand2)
            IN
                Assignment(t, {Var(MangleVar.scope, MangleVar.name, operand1Val + operand2Val, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>


OpAtomicAdd(t, var, pointer, value) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledPointer == Mangle(t, pointer)
        mangledValue == Mangle(t, value)

    IN
        /\  LET pointerVal == GetVal(workGroupId, mangledPointer)
                valueVal == GetVal(workGroupId, mangledValue)
            IN
                Assignment(t, {Var(MangleVar.scope, MangleVar.name, pointerVal, Index(-1)), Var(mangledPointer.scope, mangledPointer.name, pointerVal + valueVal, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>

OpSub(t, var, operand1, operand2) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workGroupId, mangledOperand1)
                operand2Val == GetVal(workGroupId, mangledOperand2)
            IN
                Assignment(t, {Var(MangleVar.scope, MangleVar.name, operand1Val - operand2Val, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>

OpAtomicSub(t, var, pointer, value) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledPointer == Mangle(t, pointer)
        mangledValue == Mangle(t, value)

    IN
        /\  LET pointerVal == GetVal(workGroupId, mangledPointer)
                valueVal == GetVal(workGroupId, mangledValue)
            IN
                Assignment(t, {Var(MangleVar.scope, MangleVar.name, pointerVal, Index(-1)), Var(mangledPointer.scope, mangledPointer.name, pointerVal - valueVal, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>

OpMul(t, var, operand1, operand2) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workGroupId, mangledOperand1)
                operand2Val == GetVal(workGroupId, mangledOperand2)
            IN
                Assignment(t, {Var(MangleVar.scope, MangleVar.name, operand1Val * operand2Val, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>

OpMod(t, var, operand1, operand2) ==
    LET workGroupId == WorkGroupId(t)+1
        MangleVar == Mangle(t, var)
        mangledOperand1 == Mangle(t, operand1)
        mangledOperand2 == Mangle(t, operand2)

    IN
        /\  LET operand1Val == GetVal(workGroupId, mangledOperand1)
                operand2Val == GetVal(workGroupId, mangledOperand2)
            IN
                Assignment(t, {Var(MangleVar.scope, MangleVar.name, operand1Val % operand2Val, Index(-1))})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state, DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>

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
        /\  UNCHANGED <<state, modOrder, threadView>>

\* Arrive/Execute semantics for atomic loads (SIMT-Step §4.2).
OpAtomicLoadSync(t, result, pointer) ==
    LET mangledResult == Mangle(t, result)
        mangledPointer == Mangle(t, pointer)
        workGroupId == WorkGroupId(t) + 1
        sgIdx == SubgroupIndex(t)
        currentPc == pc[t]
        sthreads == ThreadsWithinSubgroupNonTerminated(SubgroupId(t), WorkGroupId(t))
        currentDB == CurrentDynamicBlock(workGroupId, t)
        active_subgroup_threads == currentDB.currentThreadSet[workGroupId] \intersect sthreads
        unknown_subgroup_threads == currentDB.unknownSet[workGroupId] \intersect sthreads
        aligned == unknown_subgroup_threads = {} /\ \A sthread \in active_subgroup_threads: pc[sthread] = currentPc
        pointerVar == GetVar(workGroupId, mangledPointer)
        evaluatedPointerIndex == EvalExpr(t, workGroupId, pointer.index)
        raEligible == IsRAEligiblePointer(mangledPointer, evaluatedPointerIndex)
        raAddr == RAAddress(mangledPointer)
        assignmentSet ==
            IF IsIntermediate(mangledResult) THEN
                LET value == IF HasConcreteIndex(evaluatedPointerIndex) THEN pointerVar.value[evaluatedPointerIndex] ELSE pointerVar.value
                IN {Var(result.scope, Mangle(t, result).name, value, Index(-1))}
            ELSE
                LET resultVar == mangledResult
                    evaluatedResultIndex == EvalExpr(t, workGroupId, result.index)
                IN
                    IF HasConcreteIndex(evaluatedPointerIndex) /\ HasConcreteIndex(evaluatedResultIndex) THEN
                        {ChangeElementAt(resultVar, evaluatedResultIndex, pointerVar.value[evaluatedPointerIndex])}
                    ELSE IF HasConcreteIndex(evaluatedPointerIndex) THEN
                        {Var(resultVar.scope, resultVar.name, pointerVar.value[evaluatedPointerIndex], resultVar.index)}
                    ELSE IF HasConcreteIndex(evaluatedResultIndex) THEN
                        {ChangeElementAt(resultVar, evaluatedResultIndex, pointerVar.value)}
                    ELSE
                        {Var(resultVar.scope, resultVar.name, pointerVar.value, resultVar.index)}
        remaining == {sthread \in active_subgroup_threads : sthread # t /\ pc[sthread] = currentPc}
    IN
        /\ (IsVariable(mangledResult) \/ IsIntermediate(mangledResult))
        /\ IsVariable(mangledPointer)
        /\ VarExists(workGroupId, mangledPointer)
        /\ IF currentDB.sis[workGroupId][sgIdx][currentPc] = FALSE THEN
                IF ~aligned THEN
                    /\ state' = [state EXCEPT ![t] = "subgroup"]
                    /\ UNCHANGED <<pc, threadLocals, globalVars, DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
                ELSE
                    LET newDBSet == SetSISInDB(DynamicBlockSet, currentDB, workGroupId, sgIdx, currentPc, TRUE)
                    IN
                        /\ DynamicBlockSet' = newDBSet
                        /\ state' = StateUpdateSubgroup(workGroupId, active_subgroup_threads, newDBSet)
                        /\ UNCHANGED <<pc, threadLocals, globalVars, globalCounter, snapShotMap, modOrder, threadView>>
           ELSE
                LET newDBSet == IF remaining = {}
                                 THEN SetSISInDB(DynamicBlockSet, currentDB, workGroupId, sgIdx, currentPc, FALSE)
                                 ELSE DynamicBlockSet
                IN
                    IF raEligible THEN
                        \E readIdx \in RAReadChoices(t, raAddr):
                            /\ Assignment(t, RAResultAssignments(t, result, modOrder[raAddr][readIdx].value))
                            /\ RALoadStateUpdate(t, raAddr, readIdx)
                            /\ pc' = [pc EXCEPT ![t] = pc[t] + 1]
                            /\ DynamicBlockSet' = newDBSet
                            /\ state' = [state EXCEPT ![t] = "ready"]
                            /\ UNCHANGED <<globalCounter, snapShotMap>>
                    ELSE
                        /\ Assignment(t, assignmentSet)
                        /\ pc' = [pc EXCEPT ![t] = pc[t] + 1]
                        /\ DynamicBlockSet' = newDBSet
                        /\ state' = [state EXCEPT ![t] = "ready"]
                        /\ UNCHANGED <<globalCounter, snapShotMap, modOrder, threadView>>


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
        /\  LET workGroupId == WorkGroupId(t) + 1
                pointerVar == GetVar(workGroupId, mangledPointer)
                evaluatedPointerIndex == EvalExpr(t, workGroupId, pointer.index)
                raEligible == IsRAEligiblePointer(mangledPointer, evaluatedPointerIndex)
                raAddr == RAAddress(mangledPointer)
            IN
                IF raEligible THEN
                    \E readIdx \in RAReadChoices(t, raAddr):
                        /\ Assignment(t, RAResultAssignments(t, result, modOrder[raAddr][readIdx].value))
                        /\ RALoadStateUpdate(t, raAddr, readIdx)
                        /\ pc' = [pc EXCEPT ![t] = pc[t] + 1]
                        /\ UNCHANGED <<state, DynamicBlockSet, globalCounter, snapShotMap>>
                ELSE IF IsIntermediate(mangledResult) THEN 
                    /\  IF HasConcreteIndex(evaluatedPointerIndex) THEN 
                            Assignment(t, {Var(mangledResult.scope, mangledResult.name, pointerVar.value[evaluatedPointerIndex], Index(-1))})
                        ELSE
                            Assignment(t, {Var(mangledResult.scope, mangledResult.name, pointerVar.value, Index(-1))})
                    /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                    /\  UNCHANGED <<state, DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
                ELSE
                    LET resultVar == mangledResult
                        evaluatedResultIndex == EvalExpr(t, workGroupId, result.index)
                    IN
                        /\  IF HasConcreteIndex(evaluatedPointerIndex) /\ HasConcreteIndex(evaluatedResultIndex) THEN
                                Assignment(t, {ChangeElementAt(resultVar, evaluatedResultIndex, pointerVar.value[evaluatedPointerIndex])})
                            ELSE IF HasConcreteIndex(evaluatedPointerIndex) THEN
                                Assignment(t, {Var(resultVar.scope, resultVar.name, pointerVar.value[evaluatedPointerIndex], Index(-1))})
                            ELSE IF HasConcreteIndex(evaluatedResultIndex) THEN
                                Assignment(t, {ChangeElementAt(resultVar, evaluatedResultIndex, pointerVar.value)})
                            ELSE
                                Assignment(t, {Var(resultVar.scope, resultVar.name, pointerVar.value, Index(-1))})
                        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                        /\  UNCHANGED <<state, DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>

OpAtomicLoadCollective(t, result, pointer) ==
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
                LET workGroupId == WorkGroupId(t) + 1
                    sthreads == ThreadsWithinSubgroupNonTerminated(SubgroupId(t), WorkGroupId(t))
                    currentDB == CurrentDynamicBlock(workGroupId, t)
                    active_subgroup_threads == currentDB.currentThreadSet[workGroupId] \intersect sthreads
                    unknown_subgroup_threads == currentDB.unknownSet[workGroupId] \intersect sthreads
                    pointerVar == GetVar(WorkGroupId(t)+1, mangledPointer)
                    evaluatedIndex == EvalExpr(t, WorkGroupId(t)+1, pointer.index)
                IN 
                    /\
                        IF unknown_subgroup_threads # {} \/ \E sthread \in active_subgroup_threads: pc[sthread] # pc[t] THEN
                            /\  state' = [state EXCEPT ![t] = "subgroup"]
                            /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
                        ELSE
                            /\  LET loadVars == {
                                    IF HasConcreteIndex(evaluatedIndex) THEN 
                                        Var(result.scope, Mangle(sthread, result).name, pointerVar.value[evaluatedIndex], Index(-1))
                                    ELSE
                                        Var(result.scope, Mangle(sthread, result).name, pointerVar.value, Index(-1))
                                    : sthread \in active_subgroup_threads
                                }
                                IN Assignment(t, loadVars)
                            /\  state' = [
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
                            /\ UNCHANGED <<globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
            ELSE
                LET workGroupId == WorkGroupId(t) + 1
                    sthreads == ThreadsWithinSubgroupNonTerminated(SubgroupId(t), WorkGroupId(t))
                    currentDB == CurrentDynamicBlock(workGroupId, t)
                    active_subgroup_threads == currentDB.currentThreadSet[workGroupId] \intersect sthreads
                    unknown_subgroup_threads == currentDB.unknownSet[workGroupId] \intersect sthreads
                    pointerVar == GetVar(WorkGroupId(t)+1, mangledPointer)
                IN
                    /\
                        IF unknown_subgroup_threads # {} \/ \E sthread \in active_subgroup_threads: pc[sthread] # pc[t] THEN
                            /\  state' = [state EXCEPT ![t] = "subgroup"]
                            /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
                        ELSE
                            /\  LET loadVars == {
                                    LET resultVar == Mangle(sthread, result)
                                        evaluatedPointerIndex == EvalExpr(sthread, WorkGroupId(sthread)+1, pointer.index)
                                        evaluatedResultIndex == EvalExpr(sthread, WorkGroupId(sthread)+1, result.index)
                                    IN
                                        IF HasConcreteIndex(evaluatedPointerIndex) /\ HasConcreteIndex(evaluatedResultIndex) THEN
                                            ChangeElementAt(resultVar, evaluatedResultIndex, pointerVar.value[evaluatedPointerIndex])
                                        ELSE IF HasConcreteIndex(evaluatedPointerIndex) THEN
                                            Var(resultVar.scope, resultVar.name, pointerVar.value[evaluatedPointerIndex], Index(-1))
                                        ELSE IF HasConcreteIndex(evaluatedResultIndex) THEN
                                            ChangeElementAt(resultVar, evaluatedResultIndex, pointerVar.value)
                                        ELSE
                                            Var(resultVar.scope, resultVar.name, pointerVar.value, Index(-1))
                                    : sthread \in active_subgroup_threads
                                }
                                IN Assignment(t, loadVars)
                            /\  state' = [
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
                            /\ UNCHANGED <<globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>

\* Arrive/Execute semantics for atomic stores (SIMT-Step §4.2).
OpAtomicStoreSync(t, pointer, value) == 
    LET mangledPointer == Mangle(t, pointer)
        workGroupId == WorkGroupId(t) + 1
        sgIdx == SubgroupIndex(t)
        currentPc == pc[t]
        sthreads == ThreadsWithinSubgroupNonTerminated(SubgroupId(t), WorkGroupId(t))
        currentDB == CurrentDynamicBlock(workGroupId, t)
        active_subgroup_threads == currentDB.currentThreadSet[workGroupId] \intersect sthreads
        unknown_subgroup_threads == currentDB.unknownSet[workGroupId] \intersect sthreads
        aligned == unknown_subgroup_threads = {} /\ \A sthread \in active_subgroup_threads: pc[sthread] = currentPc
        pointerVar == GetVar(workGroupId, mangledPointer)
        evaluatedPointerIndex == EvalExpr(t, workGroupId, pointer.index)
        valueToStore == EvalExpr(t, workGroupId, value)
        raEligible == IsRAEligiblePointer(mangledPointer, evaluatedPointerIndex)
        raAddr == RAAddress(mangledPointer)
        assignmentSet ==
            IF HasConcreteIndex(evaluatedPointerIndex) THEN
                {ChangeElementAt(pointerVar, evaluatedPointerIndex, valueToStore)}
            ELSE
                {Var(pointerVar.scope, pointerVar.name, valueToStore, pointerVar.index)}
        remaining == {sthread \in active_subgroup_threads : sthread # t /\ pc[sthread] = currentPc}
    IN
        /\ IsVariable(mangledPointer)
        /\ VarExists(workGroupId, mangledPointer)
        /\ IF currentDB.sis[workGroupId][sgIdx][currentPc] = FALSE THEN
                IF ~aligned THEN
                    /\ state' = [state EXCEPT ![t] = "subgroup"]
                    /\ UNCHANGED <<pc, threadLocals, globalVars, DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
                ELSE
                    LET newDBSet == SetSISInDB(DynamicBlockSet, currentDB, workGroupId, sgIdx, currentPc, TRUE)
                    IN
                        /\ DynamicBlockSet' = newDBSet
                        /\ state' = StateUpdateSubgroup(workGroupId, active_subgroup_threads, newDBSet)
                        /\ UNCHANGED <<pc, threadLocals, globalVars, globalCounter, snapShotMap, modOrder, threadView>>
           ELSE
                LET newDBSet == IF remaining = {}
                                 THEN SetSISInDB(DynamicBlockSet, currentDB, workGroupId, sgIdx, currentPc, FALSE)
                                 ELSE DynamicBlockSet
                IN
                    IF raEligible THEN
                        /\ Assignment(t, {Var(pointerVar.scope, pointerVar.name, valueToStore, pointerVar.index)})
                        /\ RAStoreStateUpdate(t, raAddr, valueToStore)
                        /\ pc' = [pc EXCEPT ![t] = pc[t] + 1]
                        /\ DynamicBlockSet' = newDBSet
                        /\ state' = [state EXCEPT ![t] = "ready"]
                        /\ UNCHANGED <<globalCounter, snapShotMap>>
                    ELSE
                        /\ Assignment(t, assignmentSet)
                        /\ pc' = [pc EXCEPT ![t] = pc[t] + 1]
                        /\ DynamicBlockSet' = newDBSet
                        /\ state' = [state EXCEPT ![t] = "ready"]
                        /\ UNCHANGED <<globalCounter, snapShotMap, modOrder, threadView>>


OpAtomicStore(t, pointer, value) == 
    LET mangledPointer == Mangle(t, pointer)
    IN
        /\  IsVariable(mangledPointer)
        /\  VarExists(WorkGroupId(t)+1, mangledPointer)
        /\  LET workGroupId == WorkGroupId(t) + 1
                pointerVar == GetVar(workGroupId, mangledPointer)
                evaluatedPointerIndex == EvalExpr(t, workGroupId, pointer.index)
                valueToStore == EvalExpr(t, workGroupId, value)
                raEligible == IsRAEligiblePointer(mangledPointer, evaluatedPointerIndex)
                raAddr == RAAddress(mangledPointer)
            IN
                IF raEligible THEN
                    /\ Assignment(t, {Var(pointerVar.scope, pointerVar.name, valueToStore, pointerVar.index)})
                    /\ RAStoreStateUpdate(t, raAddr, valueToStore)
                    /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                    /\  UNCHANGED <<state,  DynamicBlockSet, globalCounter, snapShotMap>>
                ELSE
                    /\  IF HasConcreteIndex(evaluatedPointerIndex) THEN 
                            Assignment(t, {ChangeElementAt(pointerVar, evaluatedPointerIndex, valueToStore)})
                        ELSE
                            Assignment(t, {Var(pointerVar.scope, pointerVar.name, valueToStore, pointerVar.index)})
                    /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                    /\  UNCHANGED <<state,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>

OpAtomicStoreCollective(t, pointer, value) == 
    LET mangledPointer == Mangle(t, pointer)
    IN
        /\  IsVariable(mangledPointer)
        /\  VarExists(WorkGroupId(t)+1, mangledPointer)
        /\  LET pointerVar == GetVar(WorkGroupId(t)+1, mangledPointer)
                evaluatedPointerIndex == EvalExpr(t, WorkGroupId(t)+1, pointer.index)
                workGroupId == WorkGroupId(t) + 1
                sthreads == ThreadsWithinSubgroupNonTerminated(SubgroupId(t), WorkGroupId(t))
                currentDB == CurrentDynamicBlock(workGroupId, t)
                active_subgroup_threads == currentDB.currentThreadSet[workGroupId] \intersect sthreads
                unknown_subgroup_threads == currentDB.unknownSet[workGroupId] \intersect sthreads
            IN 
                IF unknown_subgroup_threads # {} \/ \E sthread \in active_subgroup_threads: pc[sthread] # pc[t] THEN
                    /\  state' = [state EXCEPT ![t] = "subgroup"]
                    /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
                ELSE
                    /\  LET storeVars == {
                            IF HasConcreteIndex(evaluatedPointerIndex) THEN 
                                ChangeElementAt(GetVar(WorkGroupId(sthread)+1, Mangle(sthread, pointer)), evaluatedPointerIndex, EvalExpr(sthread, WorkGroupId(sthread)+1, value))
                            ELSE
                                Var(pointerVar.scope, Mangle(sthread, pointer).name, EvalExpr(sthread, WorkGroupId(sthread)+1, value), pointerVar.index)
                            : sthread \in active_subgroup_threads
                        }
                        IN Assignment(t, storeVars)
                    /\  state' = [
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
        /\  UNCHANGED <<DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>

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
                    IF HasConcreteIndex(evaluatedPointerIndex) THEN 
                        Assignment(t, {ChangeElementAt(pointerVar, evaluatedPointerIndex, pointerVar.value[evaluatedPointerIndex] + 1)})
                    ELSE  
                        Assignment(t, {Var(pointerVar.scope, pointerVar.name, pointerVar.value + 1, pointerVar.index)})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<state,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>


OpAtomicDecrement(t, pointer) == 
    LET mangledPointer == Mangle(t, pointer)
    IN
        /\  IsVariable(mangledPointer)
        /\  VarExists(WorkGroupId(t)+1, mangledPointer)
        /\  LET pointerVar == GetVar(WorkGroupId(t)+1, mangledPointer)
                evaluatedPointerIndex == EvalExpr(t, WorkGroupId(t)+1, pointer.index)
            IN
                /\
                    IF HasConcreteIndex(evaluatedPointerIndex) THEN 
                        Assignment(t, {ChangeElementAt(pointerVar, evaluatedPointerIndex, pointerVar.value[evaluatedPointerIndex] - 1)})
                    ELSE  
                        Assignment(t, {Var(pointerVar.scope, pointerVar.name, pointerVar.value - 1, pointerVar.index)})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<state,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>


OpControlBarrier(t, scope) ==
    IF GetVal(-1, scope) = "subgroup" THEN \* already waiting at a subgroup barrier
        \* find all threads and their corresponding barrier state within the same subgroup
        LET sthreads == ThreadsWithinSubgroup(SubgroupId(t), WorkGroupId(t))
            workGroupId == WorkGroupId(t)+1
            currentDB == CurrentDynamicBlock(workGroupId, t)
            active_subgroup_threads == currentDB.currentThreadSet[workGroupId] \intersect sthreads
            unknown_subgroup_threads == currentDB.unknownSet[workGroupId] \intersect sthreads
            not_executing_subgroup_threads == currentDB.notExecuteSet[workGroupId] \intersect sthreads
        IN
            IF not_executing_subgroup_threads # {} THEN 
                Print("UB: All threads within subgroup must converge at current block", FALSE)
            \* if there exists thread in the subgroup that has not reached the subgroup barrier, set the barrier to current thread
            ELSE IF unknown_subgroup_threads # {} \/ \E sthread \in active_subgroup_threads: pc[sthread] # pc[t] THEN
                /\  state' = [state EXCEPT ![t] = "subgroup"]
                /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
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
                /\  UNCHANGED <<threadLocals, globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>

    ELSE IF GetVal(-1, scope) = "workgroup" THEN \* already waiting at a workgroup barrier
        LET workGroupId == WorkGroupId(t)+1
            currentDB == CurrentDynamicBlock(workGroupId, t)
            wthreads == ThreadsWithinWorkGroup(WorkGroupId(t))
            active_workgroup_threads == currentDB.currentThreadSet[workGroupId]
            unknown_workgroup_threads == currentDB.unknownSet[workGroupId]
            not_executing_workgroup_threads == currentDB.notExecuteSet[workGroupId]
        IN
            IF not_executing_workgroup_threads # {} THEN 
                Print("UB: All threads within workgroup must converge at current block", FALSE)
            \* if there exists thread in the subgroup that has not reached the workgroup barrier, set the barrier to current thread
            ELSE IF unknown_workgroup_threads # {}  \/ \E wthread \in wthreads: pc[wthread] # pc[t] THEN
                /\  state' = [state EXCEPT ![t] = "workgroup"]
                /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
            \* if all threads in the subgroup are waiting at the barrier, release them
            ELSE 
                \* release all barrier in the subgroup, marking state as ready
                /\  state' = [
                        tid \in Threads |->
                            IF tid \in wthreads THEN 
                                "ready" 
                            ELSE 
                                state[tid]
                    ]
                \* increment the program counter for all threads in the subgroup
                /\  pc' = [
                        tid \in Threads |->
                            IF tid \in wthreads THEN 
                                pc[tid] + 1
                            ELSE 
                                pc[tid]
                    ]
                /\  UNCHANGED <<threadLocals, globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
    ELSE    
        FALSE



OpGroupAll(t, result, scope, predicate) ==
    LET mangledResult == Mangle(t, result)
    IN
        /\  
            \/  /\  IsVariable(mangledResult)
            \/  IsIntermediate(mangledResult)
        /\  scope.value \in ScopeOperand
        /\  IF scope.value = "subgroup" THEN
                /\  LET sthreads == ThreadsWithinSubgroup(SubgroupId(t), WorkGroupId(t))
                        workGroupId == WorkGroupId(t)+1
                        currentDB == CurrentDynamicBlock(workGroupId, t)
                        active_subgroup_threads == currentDB.currentThreadSet[workGroupId] \intersect sthreads
                        unknown_subgroup_threads == currentDB.unknownSet[workGroupId] \intersect sthreads
                        not_executing_subgroup_threads == currentDB.notExecuteSet[workGroupId] \intersect sthreads
                    IN
                        IF not_executing_subgroup_threads # {} THEN 
                                Print("UB: All threads within subgroup must converge at current block for OpGroupAll", FALSE)
                        \* if there exists thread in the subgroup that has not reached the opgroupAll, set the barrier to current thread
                        ELSE IF unknown_subgroup_threads # {} \/ \E sthread \in sthreads: pc[sthread] # pc[t] THEN
                            /\  state' = [state EXCEPT ![t] = "subgroup"]
                            /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
                        ELSE IF \A sthread \in sthreads: EvalExpr(sthread, workGroupId, predicate) = TRUE THEN 
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
                            /\ UNCHANGED <<globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
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
                            /\ UNCHANGED <<globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
            ELSE IF scope.value = "workgroup" THEN 
                /\ LET  workGroupId == WorkGroupId(t)+1
                        currentDB == CurrentDynamicBlock(workGroupId, t)
                        wthreads == ThreadsWithinWorkGroup(WorkGroupId(t))
                        active_workgroup_threads == currentDB.currentThreadSet[workGroupId]
                        unknown_workgroup_threads == currentDB.unknownSet[workGroupId]
                        not_executing_workgroup_threads == currentDB.notExecuteSet[workGroupId]
                    IN
                        IF not_executing_workgroup_threads # {} THEN 
                            Print("UB: All threads within workgroup must converge at current block", FALSE)
                        \* if there exists thread in the subgroup that has not reached the workgroup barrier, set the barrier to current thread
                        ELSE IF unknown_workgroup_threads # {}  \/ \E wthread \in wthreads: pc[wthread] # pc[t] THEN
                                /\  state' = [state EXCEPT ![t] = "workgroup"]
                                /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
                        ELSE IF \A wthread \in wthreads: EvalExpr(wthread, workGroupId, predicate) = TRUE THEN 
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
                            /\ UNCHANGED <<globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
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
                            /\ UNCHANGED <<globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
            ELSE
                /\  FALSE

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
                        workGroupId == WorkGroupId(t)+1
                        currentDB == CurrentDynamicBlock(workGroupId, t)
                        active_subgroup_threads == currentDB.currentThreadSet[workGroupId] \intersect sthreads
                        unknown_subgroup_threads == currentDB.unknownSet[workGroupId] \intersect sthreads
                        not_executing_subgroup_threads == currentDB.notExecuteSet[workGroupId] \intersect sthreads
                    IN
                        IF not_executing_subgroup_threads # {} THEN 
                                Print("UB: All threads within subgroup must converge at current block for OpGroupAny", FALSE)
                        \* if there exists thread in the subgroup that has not reached the opgroupAll, set the barrier to current thread
                        ELSE IF unknown_subgroup_threads # {} \/ \E sthread \in sthreads: pc[sthread] # pc[t] THEN
                            /\  state' = [state EXCEPT ![t] = "subgroup"]
                            /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
                        ELSE IF \E sthread \in sthreads: EvalExpr(sthread, workGroupId, predicate) = TRUE THEN 
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
                            /\ UNCHANGED <<globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
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
                            /\ UNCHANGED <<globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
            ELSE IF scope.value = "workgroup" THEN
                /\ LET  workGroupId == WorkGroupId(t)+1
                        currentDB == CurrentDynamicBlock(workGroupId, t)
                        wthreads == ThreadsWithinWorkGroup(WorkGroupId(t))
                        active_workgroup_threads == currentDB.currentThreadSet[workGroupId]
                        unknown_workgroup_threads == currentDB.unknownSet[workGroupId]
                        not_executing_workgroup_threads == currentDB.notExecuteSet[workGroupId]
                    IN
                        IF not_executing_workgroup_threads # {} THEN 
                            Print("UB: All threads within workgroup must converge at current block", FALSE)
                        \* if there exists thread in the subgroup that has not reached the workgroup barrier, set the barrier to current thread
                        ELSE IF unknown_workgroup_threads # {}  \/ \E wthread \in wthreads: pc[wthread] # pc[t] THEN
                                /\  state' = [state EXCEPT ![t] = "workgroup"]
                                /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
                        ELSE IF \E wthread \in wthreads: EvalExpr(wthread, workGroupId, predicate) = TRUE THEN 
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
                            /\ UNCHANGED <<globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
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
                            /\ UNCHANGED <<globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
            ELSE
                /\  FALSE

OpGroupNonUniformAll(t, result, scope, predicate) ==
    LET mangledResult == Mangle(t, result)
    IN
        /\  
            \/  /\  IsVariable(result)
            \/  IsIntermediate(result)
        /\  scope.value \in ScopeOperand
        /\  IF scope.value = "subgroup" THEN
                /\  LET workGroupId == WorkGroupId(t) + 1
                        sthreads == ThreadsWithinSubgroupNonTerminated(SubgroupId(t), WorkGroupId(t))
                        currentDB == CurrentDynamicBlock(workGroupId, t)
                        active_subgroup_threads == currentDB.currentThreadSet[workGroupId] \intersect sthreads
                        unknown_subgroup_threads == currentDB.unknownSet[workGroupId] \intersect sthreads
                    IN
                        \* if there are threads in tangle not reaching the instruction point,
                        \* or there are threads in unknown set, make current thread waiting
                        IF unknown_subgroup_threads # {} \/ \E sthread \in active_subgroup_threads: pc[sthread] # pc[t] THEN
                            /\  state' = [state EXCEPT ![t] = "subgroup"]
                            /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
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
                            /\ UNCHANGED <<globalVars, globalCounter, DynamicBlockSet, snapShotMap, modOrder, threadView>>
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
                            /\ UNCHANGED <<globalVars, globalCounter, DynamicBlockSet, snapShotMap, modOrder, threadView>>
            ELSE
                /\  FALSE

OpGroupNonUniformAllEqual(t, result, scope, value) ==
    LET mangledResult == Mangle(t, result)
    IN
        /\  
            \/  /\  IsVariable(result)
            \/  IsIntermediate(result)
        /\  scope.value \in ScopeOperand
        /\  IF scope.value = "subgroup" THEN
                /\  LET workGroupId == WorkGroupId(t) + 1
                        sthreads == ThreadsWithinSubgroupNonTerminated(SubgroupId(t), WorkGroupId(t))
                        currentDB == CurrentDynamicBlock(workGroupId, t)
                        active_subgroup_threads == currentDB.currentThreadSet[workGroupId] \intersect sthreads
                        unknown_subgroup_threads == currentDB.unknownSet[workGroupId] \intersect sthreads
                        equalVal == EvalExpr(t, workGroupId, value)
                    IN
                        \* if there are threads in tangle not reaching the instruction point,
                        \* or there are threads in unknown set, make current thread waiting
                        IF unknown_subgroup_threads # {} \/ \E sthread \in active_subgroup_threads: pc[sthread] # pc[t] THEN
                            /\  state' = [state EXCEPT ![t] = "subgroup"]
                            /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
                        ELSE IF \A sthread \in active_subgroup_threads: EvalExpr(sthread, workGroupId, value) = equalVal THEN 
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
                            /\ UNCHANGED <<globalVars, globalCounter, DynamicBlockSet, snapShotMap, modOrder, threadView>>
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
                            /\ UNCHANGED <<globalVars, globalCounter, DynamicBlockSet, snapShotMap, modOrder, threadView>>
            ELSE
                /\  FALSE

OpGroupNonUniformAny(t, result, scope, predicate) ==
    LET mangledResult == Mangle(t, result)
    IN
        /\  
            \/  /\  IsVariable(result)
            \/  IsIntermediate(result)
        /\  scope.value \in ScopeOperand
        /\  IF scope.value = "subgroup" THEN
                /\  LET workGroupId == WorkGroupId(t) + 1
                        sthreads == ThreadsWithinSubgroupNonTerminated(SubgroupId(t), WorkGroupId(t))
                        currentDB == CurrentDynamicBlock(workGroupId, t)
                        active_subgroup_threads == currentDB.currentThreadSet[workGroupId] \intersect sthreads
                        unknown_subgroup_threads == currentDB.unknownSet[workGroupId] \intersect sthreads
                    IN
                        IF unknown_subgroup_threads # {} \/ \E sthread \in active_subgroup_threads: pc[sthread] # pc[t] THEN
                            /\  state' = [state EXCEPT ![t] = "subgroup"]
                            /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
                        ELSE IF \E sthread \in active_subgroup_threads: EvalExpr(sthread, workGroupId, predicate) = TRUE THEN 
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
                            /\ UNCHANGED <<globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
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
                            /\ UNCHANGED <<globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
            ELSE
                /\  FALSE

OpGroupNonUniformBroadcast(t, result, scope, value, id) ==
    LET mangledResult == Mangle(t, result)
    IN
        /\  scope.value \in ScopeOperand
        /\  IF scope.value = "subgroup" THEN
                /\  LET workGroupId == WorkGroupId(t) + 1
                        sthreads == ThreadsWithinSubgroupNonTerminated(SubgroupId(t), WorkGroupId(t))
                        currentDB == CurrentDynamicBlock(workGroupId, t)
                        tidVal == EvalExpr(t, workGroupId, id) + 1
                        gtidVal == tidVal + SubgroupId(t) * SubgroupSize + WorkGroupId(t) * WorkGroupSize
                        active_subgroup_threads == currentDB.currentThreadSet[workGroupId] \intersect sthreads
                        not_excecuteing_subgroup_threads == currentDB.notExecuteSet[workGroupId] \intersect sthreads
                        unknown_subgroup_threads == currentDB.unknownSet[workGroupId] \intersect sthreads
                    IN
                        \*  resulting value is undefined if Id is not part of the scope restricted tangle, or is greater than or equal to the size of the scope.
                        IF (tidVal > SubgroupSize) \/ (gtidVal \in not_excecuteing_subgroup_threads) THEN
                            Print("UB: Id is not part of the scope restricted tangle, or is greater than or equal to the size of the scope.", FALSE)
                        ELSE IF unknown_subgroup_threads # {} \/ \E sthread \in active_subgroup_threads: pc[sthread] # pc[t] THEN
                            /\  state' = [state EXCEPT ![t] = "subgroup"]
                            /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
                        \*  behavior is undefined when Id is not dynamically uniform
                        ELSE IF \E sthread \in sthreads: (EvalExpr(sthread, workGroupId, id) + 1) # tidVal THEN 
                            Print("UB: Id is not dynamically uniform", FALSE)
                        ELSE 
                            /\  Assignment(t, {Var(result.scope, Mangle(sthread, result).name, EvalExpr(gtidVal, WorkGroupId(gtidVal) + 1, value), Index(-1)): sthread \in active_subgroup_threads })
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
                            /\ UNCHANGED <<globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
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
                IF HasConcreteIndex(evaluatedResultIndex) /\ HasConcreteIndex(evaluatedPointerIndex) THEN
                    Assignment(t, {ChangeElementAt(resultVar, evaluatedResultIndex, pointerVar.value[evaluatedPointerIndex]), ChangeElementAt(pointerVar, evaluatedPointerIndex, evaluatedValue)})
                ELSE IF HasConcreteIndex(evaluatedResultIndex) THEN
                    Assignment(t, {ChangeElementAt(resultVar, evaluatedResultIndex, pointerVar.value), Var(pointerVar.scope, pointerVar.name, evaluatedValue, pointerVar.index)})
                ELSE IF HasConcreteIndex(evaluatedPointerIndex) THEN
                    Assignment(t, {Var(resultVar.scope, resultVar.name, pointerVar.value[evaluatedPointerIndex], resultVar.index), ChangeElementAt(pointerVar, evaluatedPointerIndex, evaluatedValue)})
                ELSE
                    Assignment(t, {Var(resultVar.scope, resultVar.name, pointerVar.value, resultVar.index), Var(pointerVar.scope, pointerVar.name, evaluatedValue, pointerVar.index)})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<state,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>

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
                        IF HasConcreteIndex(evaluatedResultIndex) /\ HasConcreteIndex(evaluatedPointerIndex) THEN
                            Assignment(t, {ChangeElementAt(resultVar, evaluatedResultIndex, pointerVar.value[evaluatedPointerIndex]), ChangeElementAt(pointerVar, evaluatedPointerIndex, evaluatedValue)})
                        ELSE IF HasConcreteIndex(evaluatedResultIndex) THEN
                            Assignment(t, {ChangeElementAt(resultVar, evaluatedResultIndex, pointerVar.value), Var(pointerVar.scope, pointerVar.name, evaluatedValue, pointerVar.index)})
                        ELSE IF HasConcreteIndex(evaluatedPointerIndex) THEN
                            Assignment(t, {Var(resultVar.scope, resultVar.name, pointerVar.value[evaluatedPointerIndex], resultVar.index), ChangeElementAt(pointerVar, evaluatedPointerIndex, evaluatedValue)})
                        ELSE
                            Assignment(t, {Var(resultVar.scope, resultVar.name, pointerVar.value, resultVar.index), Var(pointerVar.scope, pointerVar.name, evaluatedValue, pointerVar.index)})

                ELSE
                    /\
                        IF HasConcreteIndex(evaluatedResultIndex) /\ HasConcreteIndex(evaluatedPointerIndex) THEN
                            Assignment(t, {ChangeElementAt(resultVar, evaluatedResultIndex, pointerVar.value[evaluatedPointerIndex])})
                        ELSE IF HasConcreteIndex(evaluatedResultIndex) THEN
                            Assignment(t, {ChangeElementAt(resultVar, evaluatedResultIndex, pointerVar.value)})
                        ELSE IF HasConcreteIndex(evaluatedPointerIndex) THEN
                            Assignment(t, {Var(resultVar.scope, resultVar.name, pointerVar.value[evaluatedPointerIndex], resultVar.index)})
                        ELSE
                            Assignment(t, {Var(resultVar.scope, resultVar.name, pointerVar.value, resultVar.index)})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<state,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>



OpBranchCollective(t, label) ==
/\  LET workGroupId == WorkGroupId(t) + 1
        sthreads == ThreadsWithinSubgroupNonTerminated(SubgroupId(t), WorkGroupId(t))
        currentDB == CurrentDynamicBlock(workGroupId, t)
        active_subgroup_threads == currentDB.currentThreadSet[workGroupId] \intersect sthreads
        unknown_subgroup_threads == currentDB.unknownSet[workGroupId] \intersect sthreads
    IN
        \* if there are threads in set not reaching the instruction point,
        \* or there are threads in unknown set, make current thread waiting
        IF unknown_subgroup_threads # {} \/ \E sthread \in active_subgroup_threads: pc[sthread] # pc[t] THEN
            /\  state' = [state EXCEPT ![t] = "subgroup"]
            /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
        ELSE 
            /\  LET labelVal == GetVal(-1, label)
                    \* Update program counter for all active subgroup threads instead of just thread t
                    newPc == [thread \in Threads |-> 
                        IF thread \in active_subgroup_threads THEN 
                            GetVal(-1, label) 
                        ELSE 
                            pc[thread]]
                IN
                    LET counterNewDBSet == BranchConditionalUpdateSubgroup(workGroupId, active_subgroup_threads, pc[t], {labelVal}, active_subgroup_threads, {}, labelVal, -1)
                        newCounter == counterNewDBSet[1]
                        newDBSet == counterNewDBSet[2]
                        newState == StateUpdateSubgroup(workGroupId, active_subgroup_threads, newDBSet)
                        newSnapShotMap == SnapShotUpdateSubgroup(newDBSet, newState, active_subgroup_threads, newPc, newCounter)
                        matchedSnapShot == MeaningfulUpdate(newPc, newState, snapShotMap, newDBSet)
                    IN 
                        IF matchedSnapShot = {} THEN
                            /\  snapShotMap' = newSnapShotMap
                            /\  state' = newState
                            /\  DynamicBlockSet' = newDBSet 
                            /\  pc' = newPc
                            /\  globalCounter' = newCounter
                        ELSE
                            LET previousState == CHOOSE db \in matchedSnapShot: TRUE
                            IN
                                /\ state' = previousState.state
                                /\ DynamicBlockSet' = previousState.dynamicBlockSet
                                /\ globalCounter' = previousState.globalCounter
                                /\ pc' = previousState.pc
                                /\ UNCHANGED  <<threadLocals, globalVars, snapShotMap>>
            /\  UNCHANGED <<threadLocals, globalVars, modOrder, threadView>>

OpBranch(t, label) ==
    /\  LET labelVal == GetVal(-1, label)
            workGroupId == WorkGroupId(t)+1
            newPc == [pc EXCEPT ![t] = GetVal(-1, label)]
        IN
            LET counterNewDBSet == BranchUpdate(workGroupId, t, pc[t], {labelVal}, labelVal, {labelVal})
                newCounter == counterNewDBSet[1]
                newDBSet == counterNewDBSet[2]
                newState == StateUpdate(workGroupId, t, newDBSet)
                newSnapShotMap == SnapShotUpdate(newDBSet, newState, t, newPc, newCounter)
                matchedSnapShot == MeaningfulUpdate(newPc, newState, snapShotMap, newDBSet)
            IN 
                IF matchedSnapShot = {} THEN
                    /\  snapShotMap' = newSnapShotMap
                    /\  state' = newState
                    /\  DynamicBlockSet' = newDBSet 
                    /\  pc' = newPc
                    /\  globalCounter' = newCounter
                ELSE
                    LET previousState == CHOOSE db \in matchedSnapShot: TRUE
                    IN
                        /\ state' = previousState.state
                        /\ DynamicBlockSet' = previousState.dynamicBlockSet
                        /\ globalCounter' = previousState.globalCounter
                        /\ pc' = previousState.pc
                        /\ UNCHANGED  <<threadLocals, globalVars, snapShotMap>>
    /\  UNCHANGED <<threadLocals, globalVars, modOrder, threadView>>


\* Conditional branch executed collectively
OpBranchConditionalCollective(t, condition, trueLabel, falseLabel) == 
    /\  IsLiteral(trueLabel)
    /\  IsLiteral(falseLabel)
    /\  LET workGroupId == WorkGroupId(t) + 1
                        sthreads == ThreadsWithinSubgroupNonTerminated(SubgroupId(t), WorkGroupId(t))
                        currentDB == CurrentDynamicBlock(workGroupId, t)
                        active_subgroup_threads == currentDB.currentThreadSet[workGroupId] \intersect sthreads
                        unknown_subgroup_threads == currentDB.unknownSet[workGroupId] \intersect sthreads
        IN
            \* if there are threads in tangle not reaching the instruction point,
            \* or there are threads in unknown set, make current thread waiting
            IF unknown_subgroup_threads # {} \/ \E sthread \in active_subgroup_threads: pc[sthread] # pc[t] THEN
                /\  state' = [state EXCEPT ![t] = "subgroup"]
                /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
            ELSE 
                /\  LET trueLabelVal == GetVal(-1, trueLabel)
                        falseLabelVal == GetVal(-1, falseLabel)
                        \* Evaluate condition for each thread in the active subgroup
                        trueThreads == {thread \in active_subgroup_threads : EvalExpr(thread, WorkGroupId(thread)+1, condition) = TRUE}
                        falseThreads == active_subgroup_threads \ trueThreads
                        newPc == [thread \in Threads |-> 
                            IF thread \in trueThreads THEN 
                                trueLabelVal
                            ELSE IF thread \in falseThreads THEN 
                                falseLabelVal
                            ELSE 
                                pc[thread]]
                    IN
                        LET counterNewDBSet == BranchConditionalUpdateSubgroup(workGroupId, active_subgroup_threads, pc[t], {trueLabelVal, falseLabelVal}, trueThreads, falseThreads, trueLabelVal, falseLabelVal)
                            newCounter == counterNewDBSet[1]
                            newDBSet == counterNewDBSet[2]
                            newState == StateUpdateSubgroup(workGroupId, active_subgroup_threads, newDBSet)
                            newSnapShotMap == SnapShotUpdateSubgroup(newDBSet, newState, active_subgroup_threads, newPc, newCounter)
                            matchedSnapShot == MeaningfulUpdate(newPc, newState, snapShotMap, newDBSet)
                        IN
                            IF matchedSnapShot = {} THEN
                                /\  snapShotMap' = newSnapShotMap
                                /\  state' = newState   
                                /\  DynamicBlockSet' = newDBSet
                                /\  pc' = newPc
                                /\  globalCounter' = newCounter
                            ELSE 
                                LET previousState == CHOOSE db \in matchedSnapShot: TRUE
                                IN
                                    /\ state' = previousState.state
                                    /\ DynamicBlockSet' = previousState.dynamicBlockSet
                                    /\ globalCounter' = previousState.globalCounter
                                    /\ pc' = previousState.pc
                                    /\ UNCHANGED  <<threadLocals, globalVars, snapShotMap>>
                /\  UNCHANGED <<threadLocals, globalVars, modOrder, threadView>>


OpBranchConditional(t, condition, trueLabel, falseLabel) ==
    /\  IsLiteral(trueLabel)
    /\  IsLiteral(falseLabel)
    /\  LET trueLabelVal == GetVal(-1, trueLabel)
            falseLabelVal == GetVal(-1, falseLabel)
            workGroupId == WorkGroupId(t)+1

        IN
            IF EvalExpr(t, WorkGroupId(t)+1, condition) = TRUE THEN
                /\  LET counterNewDBSet == BranchUpdate(workGroupId, t, pc[t], {trueLabelVal, falseLabelVal}, trueLabelVal, {trueLabelVal, falseLabelVal})
                        newCounter == counterNewDBSet[1]
                        newDBSet == counterNewDBSet[2]
                        newState == StateUpdate(workGroupId, t, newDBSet)
                        newPc == [pc EXCEPT ![t] = trueLabelVal]
                        newSnapShotMap == SnapShotUpdate(newDBSet, newState, t, newPc, newCounter)
                        matchedSnapShot == MeaningfulUpdate(newPc, newState, snapShotMap, newDBSet)
                    IN
                        IF matchedSnapShot = {} THEN
                            /\  snapShotMap' = newSnapShotMap
                            /\  state' = newState   
                            /\  DynamicBlockSet' = newDBSet
                            /\  pc' = newPc
                            /\  globalCounter' = newCounter
                        ELSE 
                            LET previousState == CHOOSE db \in matchedSnapShot: TRUE
                            IN
                                /\ state' = previousState.state
                                /\ DynamicBlockSet' = previousState.dynamicBlockSet
                                /\ globalCounter' = previousState.globalCounter
                                /\ pc' = previousState.pc
                                /\ UNCHANGED  <<threadLocals, globalVars, snapShotMap>>
            ELSE
                /\  LET counterNewDBSet == BranchUpdate(workGroupId, t, pc[t], {trueLabelVal, falseLabelVal}, falseLabelVal, {trueLabelVal, falseLabelVal})
                        newCounter == counterNewDBSet[1]
                        newDBSet == counterNewDBSet[2]
                        newState == StateUpdate(workGroupId, t, newDBSet)
                        newPc == [pc EXCEPT ![t] = falseLabelVal]
                        newSnapShotMap == SnapShotUpdate(newDBSet, newState, t, newPc, newCounter)
                        matchedSnapShot == MeaningfulUpdate(newPc, newState, snapShotMap, newDBSet)

                    IN
                        IF matchedSnapShot = {} THEN
                            /\  snapShotMap' = newSnapShotMap
                            /\  state' = newState
                            /\  DynamicBlockSet' = newDBSet
                            /\  pc' = newPc
                            /\  globalCounter' = newCounter
                        ELSE 
                            LET previousState == CHOOSE db \in matchedSnapShot: TRUE
                            IN
                                /\ state' = previousState.state
                                /\ DynamicBlockSet' = previousState.dynamicBlockSet
                                /\ globalCounter' = previousState.globalCounter
                                /\ pc' = previousState.pc
                                /\ UNCHANGED  <<threadLocals, globalVars, snapShotMap>>
    /\  UNCHANGED <<threadLocals, globalVars, modOrder, threadView>>

    

OpSwitchCollective(t, selector, default, literals, ids) == 
/\  LET workGroupId == WorkGroupId(t) + 1
        sthreads == ThreadsWithinSubgroupNonTerminated(SubgroupId(t), WorkGroupId(t))
        currentDB == CurrentDynamicBlock(workGroupId, t)
        active_subgroup_threads == currentDB.currentThreadSet[workGroupId] \intersect sthreads
        unknown_subgroup_threads == currentDB.unknownSet[workGroupId] \intersect sthreads
    IN
        \* if there are threads in tangle not reaching the instruction point,
        \* or there are threads in unknown set, make current thread waiting
        IF unknown_subgroup_threads # {} \/ \E sthread \in active_subgroup_threads: pc[sthread] # pc[t] THEN
            /\  state' = [state EXCEPT ![t] = "subgroup"]
            /\  UNCHANGED <<pc, threadLocals, globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
        ELSE 
            /\  LET defaultVal == GetVal(-1, default)
                    literalsVal == [idx \in 1..Len(literals) |-> GetVal(-1, literals[idx])]
                    idsVal == [idx \in 1..Len(ids) |-> GetVal(-1, ids[idx])]
                IN
                    IF EvalExpr(t, WorkGroupId(t)+1, selector) \in SeqToSet(literalsVal) THEN
                        LET val == EvalExpr(t, WorkGroupId(t)+1, selector)
                            index == CHOOSE i \in 1..Len(literalsVal): literalsVal[i] = val 
                        IN
                            LET labelSet == SeqToSet(idsVal) \union {defaultVal}
                                falseLabelSet == (CHOOSE postDom \in PostDominated: postDom.node = idsVal[index]).postDominated \intersect labelSet
                                counterNewDBSet == BranchUpdate(workGroupId, t, pc[t], labelSet, idsVal[index], falseLabelSet)
                                newCounter == counterNewDBSet[1]
                                newDBSet == counterNewDBSet[2]
                                newState == StateUpdate(workGroupId, t, newDBSet)
                                newPc == [pc EXCEPT ![t] = idsVal[index]]
                                newSnapShotMap == SnapShotUpdate(newDBSet, newState, t, newPc, newCounter)
                                matchedSnapShot == MeaningfulUpdate(newPc, newState, snapShotMap, newDBSet)
                            IN
                                IF matchedSnapShot = {} THEN
                                    /\  snapShotMap' = newSnapShotMap
                                    /\  state' = newState
                                    /\  DynamicBlockSet' = newDBSet
                                    /\  pc' = newPc
                                    /\  globalCounter' = newCounter
                                ELSE 
                                    LET previousState == CHOOSE db \in matchedSnapShot: TRUE
                                    IN
                                        /\ state' = previousState.state
                                        /\ DynamicBlockSet' = previousState.dynamicBlockSet
                                        /\ globalCounter' = previousState.globalCounter
                                        /\ pc' = previousState.pc
                                        /\ UNCHANGED  <<threadLocals, globalVars, snapShotMap>>
                    ELSE
                        LET labelSet == SeqToSet(idsVal) \union {defaultVal}
                            falseLabelSet == (CHOOSE postDom \in PostDominated: postDom.node = defaultVal).postDominated \intersect (SeqToSet(idsVal) \union {defaultVal})
                            counterNewDBSet == BranchUpdate(workGroupId, t, pc[t], labelSet, defaultVal, falseLabelSet)
                            newCounter == counterNewDBSet[1]
                            newDBSet == counterNewDBSet[2]
                            newState == StateUpdate(workGroupId, t, newDBSet)
                            newPc == [pc EXCEPT ![t] = defaultVal]
                            newSnapShotMap == SnapShotUpdate(newDBSet, newState, t, newPc, newCounter)
                            matchedSnapShot == MeaningfulUpdate(newPc, newState, snapShotMap, newDBSet)
                        IN
                            IF matchedSnapShot = {} THEN
                                /\  snapShotMap' = newSnapShotMap
                                /\  state' = newState
                                /\  DynamicBlockSet' = newDBSet
                                /\  pc' = newPc
                                /\  globalCounter' = newCounter
                            ELSE 
                                LET previousState == CHOOSE db \in matchedSnapShot: TRUE
                                IN
                                    /\ state' = previousState.state
                                    /\ DynamicBlockSet' = previousState.dynamicBlockSet
                                    /\ globalCounter' = previousState.globalCounter
                                    /\ pc' = previousState.pc
                                    /\ UNCHANGED  <<threadLocals, globalVars, snapShotMap>>
            /\  UNCHANGED <<threadLocals, globalVars, modOrder, threadView>>


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
                    /\  LET labelSet == SeqToSet(idsVal) \union {defaultVal}
                            falseLabelSet == (CHOOSE postDom \in PostDominated: postDom.node = idsVal[index]).postDominated \intersect labelSet
                            counterNewDBSet == BranchUpdate(workGroupId, t, pc[t], labelSet, idsVal[index], falseLabelSet)
                            newCounter == counterNewDBSet[1]
                            newDBSet == counterNewDBSet[2]
                            newState == StateUpdate(workGroupId, t, newDBSet)
                            newPc == [pc EXCEPT ![t] = idsVal[index]]
                            newSnapShotMap == SnapShotUpdate(newDBSet, newState, t, newPc, newCounter)
                            matchedSnapShot == MeaningfulUpdate(newPc, newState, snapShotMap, newDBSet)
                        IN
                            IF matchedSnapShot = {} THEN
                                /\  snapShotMap' = newSnapShotMap
                                /\  state' = newState
                                /\  DynamicBlockSet' = newDBSet
                                /\  pc' = newPc
                                /\  globalCounter' = newCounter
                            ELSE 
                                LET previousState == CHOOSE db \in matchedSnapShot: TRUE
                                IN
                                    /\ state' = previousState.state
                                    /\ DynamicBlockSet' = previousState.dynamicBlockSet
                                    /\ globalCounter' = previousState.globalCounter
                                    /\ pc' = previousState.pc
                                    /\ UNCHANGED  <<threadLocals, globalVars, snapShotMap>>
            ELSE
                /\  LET labelSet == SeqToSet(idsVal) \union {defaultVal}
                        falseLabelSet == (CHOOSE postDom \in PostDominated: postDom.node = defaultVal).postDominated \intersect (SeqToSet(idsVal) \union {defaultVal})
                        counterNewDBSet == BranchUpdate(workGroupId, t, pc[t], labelSet, defaultVal, falseLabelSet)
                        newCounter == counterNewDBSet[1]
                        newDBSet == counterNewDBSet[2]
                        newState == StateUpdate(workGroupId, t, newDBSet)
                        newPc == [pc EXCEPT ![t] = defaultVal]
                        newSnapShotMap == SnapShotUpdate(newDBSet, newState, t, newPc, newCounter)
                        matchedSnapShot == MeaningfulUpdate(newPc, newState, snapShotMap, newDBSet)
                    IN
                        IF matchedSnapShot = {} THEN
                            /\  snapShotMap' = newSnapShotMap
                            /\  state' = newState
                            /\  DynamicBlockSet' = newDBSet
                            /\  pc' = newPc
                            /\  globalCounter' = newCounter
                        ELSE 
                            LET previousState == CHOOSE db \in matchedSnapShot: TRUE
                            IN
                                /\ state' = previousState.state
                                /\ DynamicBlockSet' = previousState.dynamicBlockSet
                                /\ globalCounter' = previousState.globalCounter
                                /\ pc' = previousState.pc
                                /\ UNCHANGED  <<threadLocals, globalVars, snapShotMap>>
    /\  UNCHANGED <<threadLocals, globalVars, modOrder, threadView>>


(* structured loop, must immediately precede block termination instruction, which means it must be second-to-last instruction in its block *)
OpLabelCollective(t, label) ==
    LET workGroupId == WorkGroupId(t) + 1
        sthreads == ThreadsWithinSubgroupNonTerminated(SubgroupId(t), WorkGroupId(t))
        currentDB == CurrentDynamicBlock(workGroupId, t)
        active_subgroup_threads == currentDB.currentThreadSet[workGroupId] \intersect sthreads
        unknown_subgroup_threads == currentDB.unknownSet[workGroupId] \intersect sthreads
    IN
        IF unknown_subgroup_threads # {} \/ \E sthread \in active_subgroup_threads: pc[sthread] # pc[t] THEN
            /\  state' = [state EXCEPT ![t] = "subgroup"]
            /\  UNCHANGED <<pc, threadLocals, globalVars, DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
        ELSE
            LET newPc == [thread \in Threads |-> IF thread \in active_subgroup_threads THEN pc[thread] + 1 ELSE pc[thread]]
                newState == StateUpdateSubgroup(workGroupId, active_subgroup_threads, DynamicBlockSet)
            IN
                /\  pc' = newPc
                /\  state' = newState
                /\  UNCHANGED <<threadLocals, globalVars, DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>

OpLabel(t, label) ==
    /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
    /\  UNCHANGED <<state, threadLocals, globalVars, DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>

(* structured loop, must immediately precede block termination instruction, which means it must be second-to-last instruction in its block *)
OpLoopMerge(t, mergeLabel, continueTarget) ==
    \* because the merge instruction must be the second to last instruction in the block, we can find the currren block by looking at the termination instruction
    /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
    /\  UNCHANGED <<state, threadLocals, globalVars, DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>

OpSelectionMerge(t, mergeLabel) ==
    \* because the merge instruction must be the second to last instruction in the block, we can find the currren block by looking at the termination instruction
    /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
    /\  UNCHANGED <<state, threadLocals, globalVars, DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>

Terminate(t) ==
    LET workGroupId == WorkGroupId(t)+1
    IN
        LET newDBSet == TerminateUpdate(workGroupId, t)
            newState == StateUpdate(workGroupId, t, newDBSet)
        IN 
            /\  DynamicBlockSet' = newDBSet
            /\  state' = [newState EXCEPT ![t] = "terminated"]
            /\  UNCHANGED <<pc, threadLocals, globalVars, globalCounter, snapShotMap, modOrder, threadView>>

OpAssert(t, predicate) ==
    LET workGroupId == WorkGroupId(t)+1
    IN
        IF EvalExpr(t, workGroupId, predicate) = FALSE THEN
            /\  Print("Assert failed", FALSE)
        ELSE
            /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
            /\  UNCHANGED <<state, threadLocals, globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>

ExecuteInstruction(t) ==
    LET workGroupId == WorkGroupId(t)+1
        currentInstr == ThreadInstructions[t][pc[t]]
    IN
        IF state[t] # "terminated" THEN
            IF  currentInstr = "Terminate" THEN
                Terminate(t)
            ELSE IF currentInstr = "Assignment" THEN
                /\  Assignment(t, {Mangle(t,ThreadArguments[t][pc[t]][1])})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<state,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>
            ELSE IF currentInstr = "GetGlobalId" THEN
                GetGlobalId(t, ThreadArguments[t][pc[t]][1])
            ELSE IF currentInstr = "OpAtomicIncrement" THEN
                OpAtomicIncrement(t, ThreadArguments[t][pc[t]][1])
            ELSE IF currentInstr = "OpAtomicDecrement" THEN
                OpAtomicDecrement(t, ThreadArguments[t][pc[t]][1])
            ELSE IF currentInstr = "OpLogicalOr" THEN 
                OpLogicalOr(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpLogicalAnd" THEN
                OpLogicalAnd(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpLogicalEqual" THEN
                OpLogicalEqual(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpLogicalNotEqual" THEN
                OpLogicalNotEqual(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpLogicalNot" THEN
                OpLogicalNot(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2])
            ELSE IF currentInstr = "OpBitcast" THEN
                OpBitcast(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2])
            ELSE IF currentInstr = "OpShiftLeftLogical" THEN
                OpShiftLeftLogical(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpShiftRightLogical" THEN
                OpShiftRightLogical(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpEqual" THEN
                OpEqual(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpNotEqual" THEN
                OpNotEqual(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpLess" THEN
                OpLess(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpLessOrEqual" THEN
                OpLessOrEqual(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpGreater" THEN
                OpGreater(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpGreaterOrEqual" THEN
                OpGreaterOrEqual(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpBitwiseOr" THEN
                OpBitwiseOr(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpBitwiseAnd" THEN
                OpBitwiseAnd(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpAdd" THEN
                OpAdd(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpAtomicAdd" THEN
                OpAtomicAdd(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpSub" THEN
                OpSub(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpAtomicSub" THEN
                OpAtomicSub(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpAtomicOr" THEN
                IF IsCollectiveInstruction(currentInstr) \/ IsSynchronousInstruction(currentInstr) THEN
                    OpAtomicOrSync(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
                ELSE
                    OpAtomicOr(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpAtomicAnd" THEN
                IF IsCollectiveInstruction(currentInstr) \/ IsSynchronousInstruction(currentInstr) THEN
                    OpAtomicAndSync(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
                ELSE
                    OpAtomicAnd(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpMul" THEN
                OpMul(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpMod" THEN
                OpMod(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpAtomicExchange" THEN
                OpAtomicExchange(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpAtomicCompareExchange" THEN
                OpAtomicCompareExchange(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3], ThreadArguments[t][pc[t]][4])
            ELSE IF currentInstr = "OpAtomicLoad" THEN
                IF IsCollectiveInstruction(currentInstr) THEN 
                    OpAtomicLoadCollective(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2])
                ELSE IF IsSynchronousInstruction(currentInstr) THEN 
                    OpAtomicLoadSync(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2])
                ELSE
                    OpAtomicLoad(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2])
            ELSE IF currentInstr = "OpAtomicStore" THEN
                IF IsCollectiveInstruction(currentInstr) THEN
                    OpAtomicStoreCollective(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2])
                ELSE IF IsSynchronousInstruction(currentInstr) THEN 
                    OpAtomicStoreSync(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2])
                ELSE
                    OpAtomicStore(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2])
            ELSE IF currentInstr = "OpBranch" THEN
                IF IsCollectiveInstruction(currentInstr) THEN 
                    OpBranchCollective(t, ThreadArguments[t][pc[t]][1])
                ELSE
                    OpBranch(t, ThreadArguments[t][pc[t]][1])
            ELSE IF currentInstr = "OpBranchConditional" THEN
                IF IsCollectiveInstruction(currentInstr) THEN 
                    OpBranchConditionalCollective(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
                ELSE
                    OpBranchConditional(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpSwitch" THEN
                IF IsCollectiveInstruction(currentInstr) THEN 
                    OpSwitchCollective(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3], ThreadArguments[t][pc[t]][4])
                ELSE
                    OpSwitch(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3], ThreadArguments[t][pc[t]][4])
            ELSE IF currentInstr = "OpControlBarrier" THEN
                OpControlBarrier(t, ThreadArguments[t][pc[t]][1])
            ELSE IF currentInstr = "OpGroupAll" THEN
                OpGroupAll(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF currentInstr = "OpGroupAny" THEN
                OpGroupAny(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpGroupNonUniformAll" THEN
                OpGroupNonUniformAll(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpGroupNonUniformAllEqual" THEN
                OpGroupNonUniformAllEqual(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpGroupNonUniformAny" THEN
                OpGroupNonUniformAny(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpGroupNonUniformBroadcast" THEN
                OpGroupNonUniformBroadcast(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2], ThreadArguments[t][pc[t]][3], ThreadArguments[t][pc[t]][4])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpLoopMerge" THEN
                OpLoopMerge(t, ThreadArguments[t][pc[t]][1], ThreadArguments[t][pc[t]][2])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpSelectionMerge" THEN
                OpSelectionMerge(t, ThreadArguments[t][pc[t]][1])
            ELSE IF ThreadInstructions[t][pc[t]] = "OpLabel" THEN
                IF IsCollectiveInstruction(currentInstr) THEN
                    OpLabelCollective(t, ThreadArguments[t][pc[t]][1])
                ELSE
                    OpLabel(t, ThreadArguments[t][pc[t]][1])
            ELSE IF ThreadInstructions[t][pc[t]] = "Assert" THEN
                OpAssert(t, ThreadArguments[t][pc[t]][1])
            ELSE
                FALSE
        ELSE 
            /\ UNCHANGED << threadVars, threadLocals, globalVars,  DynamicBlockSet, globalCounter, snapShotMap, modOrder, threadView>>


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

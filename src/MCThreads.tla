---- MODULE MCThreads ----
LOCAL INSTANCE Integers
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE MCLayout
LOCAL INSTANCE TLC

VARIABLES pc, terminated, barrier, liveVars

(* Helper Functions *)
Range(f) == { f[x] : x \in DOMAIN f }
Min(S) == CHOOSE s \in S : \A t \in S : s <= t

(* Variable *)
Var(varScope, varName, varValue) == [scope |-> varScope, name |-> varName, value |-> varValue]
IsVar(var) ==
    /\ "scope" \in DOMAIN var 
    /\ "name" \in DOMAIN var 
    /\ "value" \in DOMAIN var

IsLiteral(var) ==
    /\ IsVar(var)
    /\ var.scope = "literal"

IsLocal(var) ==
    /\ IsVar(var)
    /\ var.scope = "local"

IsShared(var) ==
    /\ IsVar(var)
    /\ var.scope = "shared"

IsIntermediate(var) ==
    /\ IsVar(var)
    /\ var.scope = "intermediate"
VarExists(workgroupId, name) == \E variable \in liveVars[workgroupId] : variable.name = name
(* todo: resolve scope if duplicate name *)
GetVar(workgroupId, name) == CHOOSE variable \in liveVars[workgroupId]: variable.name = name

Mangle(t, var) == 
    Var(var.scope, Append(t, Append(var.scope, var.name)), var.value)
    
GetVal(workgroupId, var) == 
    IF IsLiteral(var) THEN
        var.value
    ELSE IF VarExists(workgroupId, var.name) THEN
        GetVar(workgroupId, var.name).value
    ELSE 
        FALSE
    
(* Binary Expr *)

\* Mimic Lazy evaluation
BinaryExpr(Op, lhs, rhs) == [operator |-> Op, left |-> lhs, right |-> rhs]

LessThan(lhs, rhs) == lhs < rhs
LessThanOrEqual(lhs, rhs) == lhs <= rhs
GreaterThan(lhs, rhs) == lhs > rhs
GreaterThanOrEqual(lhs, rhs) == lhs >= rhs
Equal(lhs, rhs) == lhs = rhs
NotEqual(lhs, rhs) == lhs /= rhs

BinarOpSet == {"LessThan", "LessThanOrEqual", "GreaterThan", "GreaterThanOrEqual", "Equal", "NotEqual"}

IsBinaryExpr(expr) ==
        IF IsVar(expr) THEN
            FALSE
        ELSE
            /\ "operator" \in DOMAIN expr
            /\ "left" \in DOMAIN expr
            /\ "right" \in DOMAIN expr
            /\ expr["operator"] \in BinarOpSet



(* Unary Expr *)
UnaryExpr(Op, rhs) == [operator |-> Op, right |-> rhs]

Not(rhs) == 
    IF rhs = FALSE THEN 
        TRUE
    ELSE
        FALSE 
Neg(rhs) == -rhs

UnaryOpSet == {"Not", "Neg"}

IsUnaryExpr(expr) ==
    IF IsVar(expr) THEN 
        FALSE
    ELSE
        /\  "operator" \in DOMAIN expr
        /\  "right" \in DOMAIN expr
        /\  expr["operator"] \in UnaryOpSet

\* We have to delcare the recursive function before we can use it for mutual recursion
RECURSIVE ApplyBinaryExpr(_, _, _)
RECURSIVE APplyUnaryExpr(_, _, _)

EvalExpr(t, workgroupId, expr) == 
    IF IsBinaryExpr(expr) THEN
        ApplyBinaryExpr(t, workgroupId, expr)
    IF IsUnaryExpr(expr) THEN 
        ApplyUnaryExpr(t, workgroupId, expr)
    ELSE
        GetVal(workgroupId, Mangle(t, expr))

ApplyBinaryExpr(t, workgroupId, expr) ==
    LET lhsValue == EvalExpr(t, workgroupId, expr["left"])
        rhsValue == EvalExpr(t, workgroupId, expr["right"])
    IN
        IF expr["operator"] = "LessThan" THEN
            LessThan(lhsValue, rhsValue)
        ELSE IF expr["operator"] = "LessThanOrEqual" THEN
            LessThanOrEqual(lhsValue, rhsValue)
        ELSE IF expr["operator"] = "GreaterThan" THEN
            GreaterThan(lhsValue, rhsValue)
        ELSE IF expr["operator"] = "GreaterThanOrEqual" THEN
            GreaterThanOrEqual(lhsValue, rhsValue)
        ELSE IF expr["operator"] = "Equal" THEN
            Equal(lhsValue, rhsValue)
        ELSE IF expr["operator"] = "NotEqual" THEN
            NotEqual(lhsValue, rhsValue)
        ELSE
            FALSE

ApplyUnaryExpr(t, workgroupId, expr) == 
    LET rhsValue == EvalExpr(t, workgroupId, expr["right"])
    IN
        IF expr["operator"] = "Not" THEN
            Not(rhsValue)
        ELSE IF expr["operator"] = "Neg" THEN
            Neg(rhsValue)

        ELSE
            FALSE

InitProgram ==
    /\  liveVars = [t \in 1..NumWorkGroups |-> {Var("shared", "lock", 0)}]



(* Thread Configuration *)
InstructionSet == {"Assignment", "OpAtomicLoad", "OpAtomicStore", "OpAtomicCompareExchange" ,"OpAtomicExchange", "OpBranchConditional", "OpControlBarrier", "Terminate"}
VariableScope == {"local", "shared", "literal", "intermediate"}
ScopeOperand == {"workgroup", "subgroup"}
(* mutex test*)
\* ThreadInstructions ==  [t \in 1..NumThreads |-> <<"Assignment", "OpAtomicCompareExchange", "OpBranchConditional", "OpAtomicStore", "Terminate">> ]
\* ThreadArguments == [t \in 1..NumThreads |-> <<<<Var("local", "old", 1)>>, << Var("local", "old", ""), Var("shared", "lock", ""), Var("literal", "", 0), Var("literal", "", 1)>>, <<BinaryExpr("NotEqual",  Var("local", "old", ""), Var("literal", "", 0)), Var("literal", "", 2), Var("literal", "", 4)>>, <<Var("shared", "lock", ""), Var("literal", "", 0)>> >>]

ThreadInstructions ==  [t \in 1..NumThreads |-> <<"Assignment", "OpBranchConditional", "Assignment", "OpAtomicCompareExchange", "OpBranchConditional", "Assignment", "OpAtomicStore", "OpBranchConditional", "Terminate" >> ]
ThreadArguments == [t \in 1..NumThreads |-> <<
<<Var("local",  "done", FALSE)>>,
<<UnaryExpr("Not",  Var("local", "done", "")), Var("literal", "", 3), Var("literal", "", 8)>>,
<<Var("local", "old", 0)>>,
<<Var("local", "old", ""), Var("shared", "lock", ""), Var("literal", "", 0), Var("literal", "", 1)>>,
<<BinaryExpr("Equal", Var("local", "old", ""), Var("literal", "", 0))>>,
<<Var("local", "done", TRUE)>>,
<<Var("shared", "lock", ""), Var("literal", "", 0)>>,
<<Unary("Not", )>>
>>]
Threads == {tid : tid \in 1..NumThreads}
Scheduler == "OBE"

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


cleanIntermediateVar(t) == 
    /\  LET workgroupId == WorkGroupId(t)+1
            currLiveVars == liveVars[WorkGroupId(t)+1]
        IN
            LET eliminatedVars = {currVar \in currLiveVars : currVar.scope = "intermediate"}
            IN
                /\  liveVars' =  [liveVars EXCEPT ![workgroupId] = (liveVars[workgroupId] \ eliminatedVars) \union vars]


 UpdateBarrier(tid, barrierState) ==
     /\  barrierState \in BarrierSet
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
    /\  UNCHANGED <<liveVars, terminated>>


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
    /\  UNCHANGED <<terminated>>

Assignment(t, vars) == 
    /\  LET workgroupId == WorkGroupId(t)+1
            currLiveVars == liveVars[WorkGroupId(t)+1]
            mangledVars == {Mangle(t, var): var \in vars}
        IN
            \* try to eliminated var with old value and intermediate var
            LET eliminatedVars == {currVar \in currLiveVars : currVar.scope ="intermediate" \/ \E mangledVar \in mangledVars: currVar.name = mangledVar.name}
            IN
                /\  liveVars' =  [liveVars EXCEPT ![workgroupId] = (liveVars[workgroupId] \ eliminatedVars) \union vars]


\* todo: fix the logic so the result could be used argument when it is intermediate variable
OpAtomicLoad(t, result, pointer) ==
    LET mangledResult = Mangle(t, result)
        mangledPointer = Mangle(t, pointer)
    IN
        /\
            \/  
                /\  IsLocal(mangledResult)
                /\  VarExists(WorkGroupId(t)+1, mangledResult.name)
            \/  
                /\  IsShared(mangledResult)
                /\  VarExists(WorkGroupId(t)+1, mangledResult.name)
            \/  IsIntermediate(mangledResult)
        /\  
            \/  IsLocal(mangledPointer)
            \/  IsShared(mangledPointer)
        /\  VarExists(WorkGroupId(t)+1, mangledPointer.name)
        /\  IF IsIntermediate(mangledResult) THEN 
                LET pointerVar == GetVar(WorkGroupId(t)+1, mangledPointer.name)
                IN 
                    /\  Assignment(t, Var("intermediate", mangledResult.name, pointerVar.value))
            ELSE
                LET pointerVar == GetVar(WorkGroupId(t)+1, mangledPointer.name)
                    resultVar == GetVar(WorkGroupId(t)+1, mangledResult.name)
                IN
                    /\  Assignment(t, Var(resultVar.scope, resultVar.name, pointerVar.value))
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<terminated, barrier>>

OpAtomicStore(t, pointer, value) == 
    LET mangledPointer = Mangle(t, pointer)
    IN
        /\  
            \/  IsLocal(mangledPointer)
            \/  IsShared(mangledPointer)
        /\  VarExists(WorkGroupId(t)+1, mangledPointer.name)
        /\  IsLiteral(value)
        /\  LET pointerVar == GetVar(WorkGroupId(t)+1, mangledPointer.name)
            IN
                /\  Assignment(t, {Var(pointerVar.scope, pointerVar.name, value.value)})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<terminated, barrier>>

\* todo: logic is incorrect
\* result should be either true or false
OpGroupAll(t, result, predicate, scope) ==
    LET mangledResult = Mangle(t, result)
    IN
        /\  
            \/  
                /\  IsLocal(mangledResult)
                /\  VarExists(WorkGroupId(t)+1, mangledResult.name)
            \/  
                /\  IsShared(mangledResult)
                /\  VarExists(WorkGroupId(t)+1, mangledResult.name)
            \/  IsIntermediate(mangledResult)
        /\  scope \in ScopeOperand
        /\  IF scope = "subgroup" THEN
                /\  LET sthreads = {ThreadsWithinSubgroup(SubgroupId(t), WorkGroupId(t))}
                    IN
                        /\  IF \A sthread \in sthreads: EvalExpr(355521552wfkmfkjfjmdsfjdsflerkf
                        sthread, WorkGroupId(t)+1, predicate) = TRUE THEN 
                                /\  Assignment(t, {Var(mangledResult.scope, mangledResult.name, TRUE)})
                            ELSE 
                                /\  Assignment(t, {Var(mangledResult.scope, mangledResult.name, FALSE)})
            ELSE IF scope = "workgroup" THEN 
                /\  LET wthreads = {ThreadsWithinWorkGroup(WorkGroupId(t))}
                    IN
                        /\  IF \A wthread \in wthreads: EvalExpr(wthread, WorkGroupId(t)+1, predicate) = TRUE THEN 
                                /\  Assignment(t, {Var(mangledResult.scope, mangledResult.name, TRUE)})
                            ELSE 
                                /\  Assignment(t, {Var(mangledResult.scope, mangledResult.name, FALSE)})
            ELSE
                /\  FALSE
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<terminated, barrier>>


(* result and pointer are variable, value is literal *)
OpAtomicExchange(t, result, pointer, value) ==
    LET mangledResult = Mangle(t, result)
        mangledPointer = Mangle(t, pointer)
    IN
        /\  
            \/  IsLocal(mangledResult)
            \/  IsShared(mangledResult)
        /\  VarExists(WorkGroupId(t)+1, mangledResult.name)
        /\  
            \/  IsLocal(mangledPointer)
            \/  IsShared(mangledPointer)
        /\  VarExists(WorkGroupId(t)+1, mangledPointer.name)
        /\  IsLiteral(value)
        /\  LET resultVar == GetVar(WorkGroupId(t)+1, mangledResult.name)
                pointerVar == GetVar(WorkGroupId(t)+1, mangledPointer.name)
            IN
                /\  Assignment(t, {Var(resultVar.scope, resultVar.name, pointerVar.value), Var(pointerVar.scope, pointerVar.name, value.value)})
        /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
        /\  UNCHANGED <<terminated, barrier>>

(* result and pointer are variable, compare and value are literal *)
OpAtomicCompareExchange(t, result, pointer, compare, value) ==
    LET mangledResult = Mangle(t, result)
        mangledPointer = Mangle(t, pointer)
    IN
        /\  
            \/  IsLocal(mangledResult)
            \/  IsShared(mangledResult)
        /\  VarExists(WorkGroupId(t)+1, mangledResult.name)
        /\  
            \/  IsLocal(mangledPointer)
            \/  IsShared(mangledPointer)
        /\  VarExists(WorkGroupId(t)+1, mangledPointer.name)
        /\  IsLiteral(compare)
        /\  IsLiteral(value)
        /\  LET resultVar == GetVar(WorkGroupId(t)+1, mangledResult.name)
                pointerVar == GetVar(WorkGroupId(t)+1, mangledPointer.name)
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
    /\  IF EvalExpr(t, WorkGroupId(t)+1, condition) THEN
            /\  pc' = [pc EXCEPT ![t] = trueLabel.value]
        ELSE
            /\  pc' = [pc EXCEPT ![t] = falseLabel.value]
    /\  UNCHANGED <<terminated, barrier>>


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
                /\  Assignment(t, {ThreadArguments[t][pc[t]][1]})
                /\  pc' = [pc EXCEPT ![t] = pc[t] + 1]
                /\  UNCHANGED <<terminated, barrier>>
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
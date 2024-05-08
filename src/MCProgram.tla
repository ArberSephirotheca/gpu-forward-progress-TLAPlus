---- MODULE MCProgram ----
LOCAL INSTANCE Integers
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
\* LOCAL INSTANCE MCLayout
LOCAL INSTANCE TLC

VARIABLES globalVars, threadLocals

(* Layout Configuration *)
SubgroupSize == 2
WorkGroupSize == 2
NumWorkGroups == 2
NumThreads == WorkGroupSize * NumWorkGroups

Threads == {tid : tid \in 1..NumThreads}
Scheduler == "OBE"


(* Variable *)
Var(varScope, varName, varValue) == 
    [scope |-> varScope,
     name |-> varName, 
     value |-> varValue]
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

IsGlobal(var) ==
    /\ IsVar(var)
    /\ var.scope = "global"

IsVariable(var) ==
    \/ IsLocal(var)
    \/ IsShared(var)
    \/ IsGlobal(var)

IsIntermediate(var) ==
    /\ IsVar(var)
    /\ var.scope = "intermediate"


Range(f) == { f[x] : x \in DOMAIN f }
Min(S) == CHOOSE s \in S : \A t \in S : s <= t
MinIndices(s, allowedIndices) ==
    LET allowedValues == {s[i] : i \in DOMAIN s \cap allowedIndices}
        minVal == IF allowedValues = {} THEN 1000
                  ELSE Min(allowedValues)
    IN {i \in DOMAIN s \cap allowedIndices : s[i] = minVal}

VarExists(workgroupId, var) == 
    IF var.scope = "global" THEN 
        \E variable \in globalVars : variable.name = var.name 
    ELSE 
        \E variable \in threadLocals[workgroupId] : (variable.name = var.name /\ variable.scope = var.scope)
(* todo: resolve scope if duplicate name *)
GetVar(workgroupId, var) == 
    IF var.scope = "global" THEN 
        CHOOSE variable \in globalVars : variable.name = var.name 
    ELSE 
        CHOOSE variable \in threadLocals[workgroupId]: (variable.name = var.name /\ variable.scope = var.scope)

\* only mangling local and intermediate variables
Mangle(t, var) ==
    IF var.scope = "local" THEN
        Var(var.scope, Append(ToString(t), Append(var.scope, var.name)), var.value)
    ELSE IF var.scope = "intermediate" THEN
        Var(var.scope, Append(ToString(t), Append(var.scope, var.name)), var.value)
    ELSE
        var
    
GetVal(workgroupId, var) == 
    IF IsLiteral(var) THEN
        var.value
    ELSE IF VarExists(workgroupId, var) THEN
        GetVar(workgroupId, var).value
    ELSE 
        /\  Print("Don't has such variable", var)
        /\  FALSE
    

    
(* Binary Expr *)

\* Mimic Lazy evaluation
BinaryExpr(Op, lhs, rhs) == 
    [operator |-> Op,
     left |-> lhs,
     right |-> rhs]

LessThan(lhs, rhs) == lhs < rhs
LessThanOrEqual(lhs, rhs) == lhs <= rhs
GreaterThan(lhs, rhs) == lhs > rhs
GreaterThanOrEqual(lhs, rhs) == lhs >= rhs
Equal(lhs, rhs) == lhs = rhs
NotEqual(lhs, rhs) == lhs /= rhs

BinarOpSet == {"LessThan", "LessThanOrEqual", "GreaterThan", "GreaterThanOrEqual", "Equal", "NotEqual"}

IsBinaryExpr(expr) ==
    IF IsVar(expr) = TRUE THEN
        FALSE
    ELSE
        /\ "operator" \in DOMAIN expr
        /\ "left" \in DOMAIN expr
        /\ "right" \in DOMAIN expr
        /\ expr["operator"] \in BinarOpSet


(* Unary Expr *)
UnaryExpr(Op, rhs) == [operator |-> Op, right |-> rhs]

Not(rhs) ==
    /\  IF rhs = FALSE THEN 
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
RECURSIVE ApplyUnaryExpr(_, _, _)

EvalExpr(t, workgroupId, expr) == 
    IF IsBinaryExpr(expr) = TRUE THEN
        ApplyBinaryExpr(t, workgroupId, expr)
    ELSE IF IsUnaryExpr(expr) = TRUE THEN 
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
    /\  LET rhsValue == EvalExpr(t, workgroupId, expr["right"])
        IN
            /\  IF expr["operator"] = "Not" THEN
                    Not(rhsValue)
                ELSE IF expr["operator"] = "Neg" THEN
                    Neg(rhsValue)

                ELSE
                    FALSE

InitProgram ==
    /\  threadLocals = [t \in 1..NumWorkGroups |-> {}]
    /\  globalVars = {Var("global", "lock", 0)}


(* Thread Configuration *)
InstructionSet == {"Assignment", "OpAtomicLoad", "OpAtomicStore", "OpGroupAll", "OpAtomicCompareExchange" ,"OpAtomicExchange", "OpBranchConditional", "OpControlBarrier", "Terminate"}
VariableScope == {"global", "shared", "local", "literal", "intermediate"}
ScopeOperand == {"workgroup", "subgroup"}
(* spinlock test *)
\* ThreadInstructions ==  [t \in 1..NumThreads |-> <<"Assignment", "OpAtomicCompareExchange", "OpBranchConditional", "OpAtomicStore", "Terminate">> ]
\* ThreadArguments == [t \in 1..NumThreads |-> <<
\* <<Var("local", "old", 1)>>,
\* << Var("local", "old", ""), Var("global", "lock", ""), Var("literal", "", 0), Var("literal", "", 1)>>,
\* <<BinaryExpr("NotEqual",  Var("local", "old", ""), Var("literal", "", 0)), Var("literal", "", 2), Var("literal", "", 4)>>,
\* <<Var("global", "lock", ""), Var("literal", "", 0)>>
\* >>]

(* spinlock test with subgroupall *)
ThreadInstructions ==  [t \in 1..NumThreads |-> <<"Assignment", "OpBranchConditional", "OpAtomicCompareExchange", "OpBranchConditional", "Assignment", "OpAtomicStore", "OpGroupAll", "OpBranchConditional", "Terminate" >> ]
ThreadArguments == [t \in 1..NumThreads |-> <<
<<Var("local",  "done", FALSE)>>,
<<UnaryExpr("Not",  Var("local", "done", "")), Var("literal", "", 3), Var("literal", "", 7)>>,
<<Var("local", "old", ""), Var("global", "lock", ""), Var("literal", "", 0), Var("literal", "", 1)>>,
<<BinaryExpr("Equal", Var("local", "old", ""), Var("literal", "", 0)), Var("literal", "", 5), Var("literal", "", 7)>>,
<<Var("local", "done", TRUE)>>,
<<Var("global", "lock", ""), Var("literal", "", 0)>>,
<<Var("intermediate", "groupall", ""), Var("local", "done", TRUE) ,"subgroup">>,
<<UnaryExpr("Not", Var("intermediate", "groupall", "")), Var("literal", "", 2),Var("literal", "", 9) >>,
<< >>
>>]

(* producer-consumer *)
\* ThreadInstructions ==  [t \in 1..NumThreads |-> <<"GLobalInvocationId", "Assignment", "OpAtomicLoad", "OpBranchConditional", "OpAtomicStore", "Terminate">> ]
\* ThreadArguments == [t \in 1..NumThreads |-> < <
\* <<Var("local", "old", 1)>>,
\* << Var("local", "old", ""), Var("shared", "lock", ""), Var("literal", "", 0), Var("literal", "", 1)>>,
\* <<BinaryExpr("NotEqual",  Var("local", "old", ""), Var("literal", "", 0)), Var("literal", "", 2), Var("literal", "", 4)>>,
\* <<Var("shared", "lock", ""), Var("literal", "", 0)>>
\* >>]

(* producer-consumer with subgroupall *)

INSTANCE ProgramConf


GlobalInvocationId(tid) == tid-1

LocalInvocationId(tid) == GlobalInvocationId(tid) % WorkGroupSize

WorkGroupId(tid) == GlobalInvocationId(tid) \div WorkGroupSize
    
SubgroupId(tid) == LocalInvocationId(tid) \div SubgroupSize

SubgroupInovcationId(tid) == LocalInvocationId(tid) % SubgroupSize

====



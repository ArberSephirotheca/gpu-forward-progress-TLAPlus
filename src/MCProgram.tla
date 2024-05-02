---- MODULE MCProgram ----
LOCAL INSTANCE Integers
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE MCLayout
LOCAL INSTANCE TLC

VARIABLES liveVars


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

VarExists(workgroupId, name) == \E variable \in liveVars[workgroupId] : variable.name = name
(* todo: resolve scope if duplicate name *)
GetVar(workgroupId, name) == CHOOSE variable \in liveVars[workgroupId]: variable.name = name
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


(* Built-in Function *)
Function(expr) ==
    

\* We have to delcare the recursive function before we can use it for mutual recursion
RECURSIVE ApplyBinaryExpr(_, _)
RECURSIVE APplyUnaryExpr(_, _)

EvalExpr(workgroupId, expr) == 
    IF IsBinaryExpr(expr) THEN
        ApplyBinaryExpr(workgroupId, expr)
    IF IsUnaryExpr(expr) THEN 
        ApplyUnaryExpr(workgroupId, expr)
    ELSE
        GetVal(workgroupId, expr)

ApplyBinaryExpr(workgroupId, expr) ==
    LET lhsValue == EvalExpr(workgroupId, expr["left"])
        rhsValue == EvalExpr(workgroupId, expr["right"])
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

ApplyUnaryExpr(workgroupId, expr) == 
    LET rhsValue == EvalExpr(workgroupId, expr["right"])
    IN
        IF expr["operator"] = "Not" THEN
            Not(rhsValue)
        ELSE IF expr["operator"] = "Neg" THEN
            Neg(rhsValue)

        ELSE
            FALSE

InitProgram ==
    /\  liveVars = [t \in 1..NumWorkGroups |-> {Var("shared", "lock", 0)}]
====
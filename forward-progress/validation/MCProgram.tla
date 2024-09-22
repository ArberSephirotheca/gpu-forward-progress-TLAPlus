---- MODULE MCProgram ----
LOCAL INSTANCE Integers
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE FiniteSets
\* LOCAL INSTANCE MCLayout
LOCAL INSTANCE TLC

VARIABLES globalVars, threadLocals, CFG, MaxPathLength
(* Layout Configuration *)

\* NumThreads == WorkGroupSize * NumWorkGroups

Threads == {tid : tid \in 1..NumThreads}
\* SubgroupSize == 1
\* WorkGroupSize == 1
\* NumWorkGroups == 2
\* Scheduler == "OBE"


(* Variable *)
Var(varScope, varName, varValue, index) == 
    [scope |-> varScope,
     name  |-> varName, 
     value |-> varValue,
     index |-> index]

\* Label(name, pc) == 
\*     [name |-> name,
\*      pc |-> pc]

Index(idx) == 
    [realIndex |-> idx]

IsVar(var) ==
    /\ "scope" \in DOMAIN var 
    /\ "name" \in DOMAIN var 
    /\ "value" \in DOMAIN var
    /\ "index" \in DOMAIN var

IsArray(var) ==
    /\ IsVar(var)
    /\ var.index.realIndex >= 0

\* We do it only to make TLC happy, as index could be an expression
IsIndex(var) ==
    /\ "realIndex" \in DOMAIN var

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
Max(S) == CHOOSE s \in S : \A t \in S : s >= t
Min(S) == CHOOSE s \in S : \A t \in S : s <= t
MinIndices(s, allowedIndices) ==
    LET allowedValues == {s[i] : i \in DOMAIN s \cap allowedIndices}
        minVal == IF allowedValues = {} THEN 1000
                  ELSE Min(allowedValues)
    IN {i \in DOMAIN s \cap allowedIndices : s[i] = minVal}

VarExists(workgroupId, var) == 
    IF IsShared(var) \/ IsGlobal(var) THEN 
        \E variable \in globalVars : variable.name = var.name 
    ELSE 
        \E variable \in threadLocals[workgroupId] : (variable.name = var.name /\ variable.scope = var.scope)


(* todo: resolve scope if duplicate name *)
GetVar(workgroupId, var) == 
    IF IsShared(var) \/ IsGlobal(var) THEN 
        CHOOSE variable \in globalVars : variable.name = var.name 
    ELSE 
        CHOOSE variable \in threadLocals[workgroupId]: (variable.name = var.name /\ variable.scope = var.scope)

\* only mangling local and intermediate variables
Mangle(t, var) ==
    IF var.scope = "local" THEN
        Var(var.scope, Append(ToString(t), Append(var.scope, var.name)), var.value, var.index)
    ELSE IF var.scope = "intermediate" THEN
        Var(var.scope, Append(ToString(t), Append(var.scope, var.name)), var.value, var.index)
    ELSE
        var
    
GetVal(workgroupId, var) == 
    IF IsLiteral(var) THEN
        var.value
    ELSE IF VarExists(workgroupId, var) THEN
        IF IsArray(var) /\ var.index > 0 THEN
            GetVar(workgroupId, var).value[var.index]
        ELSE
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
Plus(lhs, rhs) == lhs + rhs
Minus(lhs, rhs) == lhs - rhs
Multiply(lhs, rhs) == lhs * rhs
Indexing(lhs, idx) == lhs[idx]

BinarOpSet == {"LessThan", "LessThanOrEqual", "GreaterThan", "GreaterThanOrEqual", "Equal", "NotEqual", "Plus", "Minus", "Multiply", "Indexing"}

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

    
IsExpression(var) ==
    \/ IsBinaryExpr(var)
    \/ IsUnaryExpr(var)

\* We have to delcare the recursive function before we can use it for mutual recursion
RECURSIVE ApplyBinaryExpr(_, _, _)
RECURSIVE ApplyUnaryExpr(_, _, _)

EvalExpr(t, workgroupId, expr) ==
    IF IsIndex(expr) THEN
        expr.realIndex
    ELSE IF IsBinaryExpr(expr) = TRUE THEN
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
        ELSE IF expr["operator"] = "Plus" THEN
            Plus(lhsValue, rhsValue)
        ELSE IF expr["operator"] = "Minus" THEN
            Minus(lhsValue, rhsValue)
        ELSE IF expr["operator"] = "Multiply" THEN
            Multiply(lhsValue, rhsValue)
        ELSE IF expr["operator"] = "Indexing" THEN
            Indexing(lhsValue, rhsValue)
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

GlobalInvocationId(tid) == tid-1

LocalInvocationId(tid) == GlobalInvocationId(tid) % WorkGroupSize

WorkGroupId(tid) == GlobalInvocationId(tid) \div WorkGroupSize
    
SubgroupId(tid) == LocalInvocationId(tid) \div SubgroupSize

SubgroupInovcationId(tid) == LocalInvocationId(tid) % SubgroupSize

ThreadsWithinWorkGroup(wgid) ==  {tid \in Threads : WorkGroupId(tid) = wgid}

ThreadsWithinSubgroup(sid, wgid) == {tid \in Threads : SubgroupId(tid) = sid} \intersect ThreadsWithinWorkGroup(wgid)

(* Thread Configuration *)
InstructionSet == {"Assignment", "GetGlobalId", "OpAtomicLoad", "OpAtomicStore", "OpAtomicAdd" , "OpAtomicSub", "OpGroupAll", 
"OpAtomicCompareExchange" ,"OpAtomicExchange", "OpBranch", "OpBranchConditional", "OpControlBarrier", "OpLoopMerge",
"OpSelectionMerge", "OpLabel", "Terminate", "OpEqual", "OpNotEqual", "OpLess", "OpLessOrEqual", "OpGreater",
"OpGreaterOrEqual", "OpAdd", "OpSub", "OpMul", "Indexing"}
VariableScope == {"global", "shared", "local", "literal", "intermediate"}
ScopeOperand == {"workgroup", "subgroup", "tangle"}
BlockTypeSet == {"Merge", "None"}


(*Program *)
\* (* spinlock test *)
\* ThreadInstructions ==  [t \in 1..NumThreads |-> <<"Assignment", "OpAtomicCompareExchange", "OpBranchConditional", "OpAtomicStore", "Terminate">> ]
\* ThreadArguments == [t \in 1..NumThreads |-> <<
\* <<Var("local", "old", 1, Index(-1))>>,
\* << Var("local", "old", "", Index(-1)), Var("global", "lock", "", Index(-1)), Var("literal", "", 0, Index(-1)), Var("literal", "", 1, Index(-1))>>,
\* <<BinaryExpr("NotEqual",  Var("local", "old", "", Index(-1)), Var("literal", "", 0, Index(-1))), Var("literal", "", 2, Index(-1)), Var("literal", "", 4, Index(-1))>>,
\* <<Var("global", "lock", "", Index(-1)), Var("literal", "", 0, Index(-1))>>
\* >>]

(* spinlock test with subgroupall *)
\* ThreadInstructions ==  [t \in 1..NumThreads |-> 
\* <<
\* "Assignment", 
\* "OpBranchConditional", 
\* "Assignment",
\* "OpAtomicCompareExchange", 
\* "OpBranchConditional", 
\* "Assignment", 
\* "OpAtomicStore", 
\* "OpGroupAll", 
\* "OpBranchConditional", 
\* "Terminate"
\* >> ]


\* ThreadArguments == [t \in 1..NumThreads |-> 
\* <<
\* <<Var("local", "done", FALSE, Index(-1))>>,
\* <<UnaryExpr("Not",  Var("local", "done", "", Index(-1))), Var("literal", "", 3, Index(-1)), Var("literal", "", 8, Index(-1))>>,
\* <<Var("local", "old", 0, Index(-1))>>,
\* <<Var("local", "old", "", Index(-1)), Var("global", "lock", "", Index(-1)), Var("literal", "", 0, Index(-1)), Var("literal", "", 1, Index(-1))>>,
\* <<BinaryExpr("Equal", Var("local", "old", "", Index(-1)), Var("literal", "", 0, Index(-1))), Var("literal", "", 6, Index(-1)), Var("literal", "", 8, Index(-1))>>,
\* <<Var("local", "done", TRUE, Index(-1))>>,
\* <<Var("global", "lock", "", Index(-1)), Var("literal", "", 0, Index(-1))>>,
\* <<Var("intermediate", "groupall", "", Index(-1)), Var("local", "done", TRUE, Index(-1)) ,"subgroup">>,
\* <<UnaryExpr("Not", Var("intermediate", "groupall", "", Index(-1))), Var("literal", "", 2, Index(-1)),Var("literal", "", 10, Index(-1)) >>,
\* << >>
\* >>]

(* producer-consumer *)
\* ThreadInstructions ==  [t \in 1..NumThreads |-> 
\* <<
\* "Assignment",
\* "OpAtomicLoad",
\* "OpBranchConditional",
\* "OpAtomicStore",
\* "Terminate"
\* >>]
\* ThreadArguments == [t \in 1..NumThreads |-> 
\* <<
\* <<Var("local", "gid", t-1, Index(-1))>>,
\* <<Var("intermediate", "load", "", Index(-1)), Var("global", "msg", "", Index(-1))>>,
\* <<BinaryExpr("NotEqual", Var("local", "gid", "", Index(-1)), Var("intermediate", "load", "", Index(-1))), Var("literal", "", 2, Index(-1)), Var("literal", "", 4, Index(-1))>>,
\* <<Var("global", "msg", "", Index(-1)), BinaryExpr("Plus", Var("local", "gid", "", Index(-1)), Var("literal", "", 1, Index(-1)))>>,
\* << >>
\* >>]

(* producer-consumer with subgroupall *)
\* ThreadInstructions ==  [t \in 1..NumThreads |-> 
\* <<
\* "Assignment", 
\* "Assignment",
\* "OpBranchConditional",
\* "OpAtomicLoad",
\* "OpBranchConditional", 
\* "OpAtomicStore", 
\* "Assignment", 
\* "OpGroupAll", 
\* "OpBranchConditional", 
\* "Terminate"
\* >> ]


\* ThreadArguments == [t \in 1..NumThreads |-> 
\* <<
\* <<Var("local", "gid", t-1, Index(-1))>>,
\* <<Var("local", "done", FALSE, Index(-1))>>,
\* <<UnaryExpr("Not",  Var("local", "done", "", Index(-1))), Var("literal", "", 4, Index(-1)), Var("literal", "", 8, Index(-1))>>,
\* <<Var("intermediate", "load", "", Index(-1)), Var("global", "msg", "", Index(-1))>>,
\* <<BinaryExpr("Equal", Var("local", "gid", "", Index(-1)), Var("intermediate", "load", "", Index(-1))), Var("literal", "", 6, Index(-1)), Var("literal", "", 8, Index(-1))>>,
\* <<Var("global", "msg", "", Index(-1)), BinaryExpr("Plus", Var("local", "gid", "", Index(-1)), Var("literal", "", 1, Index(-1)))>>,
\* <<Var("local", "done", TRUE, Index(-1))>>,
\* <<Var("intermediate", "groupall", "", Index(-1)), Var("local", "done", TRUE, Index(-1)) ,"subgroup">>,
\* <<UnaryExpr("Not", Var("intermediate", "groupall", "", Index(-1))), Var("literal", "", 3, Index(-1)),Var("literal", "", 10, Index(-1)) >>,
\* << >>
\* >>]


(* decoupled lookback *)
\* ThreadInstructions ==  [t \in 1..NumThreads |-> 
\* <<
\* "Assignment",     \* Create a local vriable partitionId
\* "Assignment",    \* Create a local variable localResult
\* "OpBranchConditional", \* if local thread idx == 0
\* "OpAtomicExchange",    \* then, increment the global partition index by 1 and atomic store the original partition index to workgroup partition.
\* "OpControlBarrier",    \* wait for threads within subgroup to reach here
\* "OpAtomicLoad",     \* load the workgroup partition to local variable partitionId
\* "OpBranchConditional",  \* True if the partitionId is equal to 0, 
\* "OpAtomicStore",    \* then store 2 to globalResult, index would be partitionId * WorkGroupSize + tid
\* "OpAtomicStore",    \* else store 1 to globalResult, index would be partitionId * WorkGroupSize + tid
\* "OpBranchConditional",  \* For loop, end if the partitionId is equal or less than 0
\* "OpAtomicLoad",     \* then, load the globalResult from other workgroup to local variable result
\* "OpBranchConditional",  \* True if the result is 2, meanning we have inclusive result. If False, jump to next OpBranchConditional
\* "OpAtomicStore",    \* then, atomic store 2 to globalResult
\* "OpBranchConditional",  \* True if the result is 1, meanning we have aggregated result. If False, jump to the if statement
\* "OpAtomicSub",    \* then, reduce the local partitionId by 1
\* "OpBranch",  \* TJump to the for loop
\* "Terminate"
\* >> ]


\* ThreadArguments == [t \in 1..NumThreads |-> 
\* <<
\* <<Var("local", "partitionId", 0, Index(-1))>>,
\* <<Var("local", "localResult", 0, Index(-1))>>,
\* <<BinaryExpr("Equal",  Var("literal", "", (t-1) % WorkGroupSize, Index(-1)), Var("literal", "", 0, Index(-1))), Var("literal", "", 4, Index(-1)), Var("literal", "", 5, Index(-1))>>,
\* <<Var("global", "workgroupPartition", "", Index(((t-1) \div WorkGroupSize)+1)), Var("global", "partition", "", Index(-1)), BinaryExpr("Plus", Var("global", "partition", "", Index(-1)), Var("literal", "", 1, Index(-1)))>>,
\* <<"subgroup">>,
\* <<Var("local", "partitionId", "", Index(-1)), Var("global", "workgroupPartition", "", Index(((t-1) \div WorkGroupSize)+1))>>,
\* <<BinaryExpr("Equal", Var("local", "partitionId", "", Index(-1)), Var("literal", "", 0, Index(-1))), Var("literal", "", 8, Index(-1)), Var("literal", "", 9, Index(-1))>>,
\* <<Var("global", "result", "", BinaryExpr("Plus", BinaryExpr("Multiply", Var("local", "partitionId", "", Index(-1)), Var("literal", "", WorkGroupSize, Index(-1))), Var("literal", "", t, Index(-1)))), Var("literal", "", 2, Index(-1))>>,
\* <<Var("global", "result", "", BinaryExpr("Plus", BinaryExpr("Multiply", Var("local", "partitionId", "", Index(-1)), Var("literal", "", WorkGroupSize, Index(-1))), Var("literal", "", t, Index(-1)))), Var("literal", "", 1, Index(-1))>>,
\* <<BinaryExpr("GreaterThan", Var("local", "partitionId", "", Index(-1)), Var("literal", "", 0, Index(-1))), Var("literal", "", 11, Index(-1)), Var("literal", "", 17, Index(-1))>>,
\* <<Var("local", "localResult", "", Index(-1)), Var("global", "result", "", BinaryExpr("Plus", BinaryExpr("Multiply", BinaryExpr("Minus", Var("local", "partitionId", "", Index(-1)), Var("literal", "", 1, Index(-1))), Var("literal", "", WorkGroupSize, Index(-1))), Var("literal", "", t, Index(-1))))>>,
\* <<BinaryExpr("Equal", Var("local", "localResult", "", Index(-1)), Var("literal", "", 2, Index(-1))), Var("literal", "", 13, Index(-1)), Var("literal", "", 15, Index(-1))>>,
\* <<Var("global", "result", "", BinaryExpr("Plus", BinaryExpr("Multiply", Var("local", "partitionId", "", Index(-1)), Var("literal", "", WorkGroupSize, Index(-1))), Var("literal", "", t, Index(-1)))), Var("literal", "", 2, Index(-1))>>,
\* <<BinaryExpr("Equal", Var("local", "localResult", "", Index(-1)), Var("literal", "", 1, Index(-1))), Var("literal", "", 16, Index(-1)), Var("literal", "", 10, Index(-1)) >>,
\* <<Var("local", "partitionId", "", Index(-1))>>,
\* <<Var("literal", "", 10, Index(-1))>>,
\* <<>>
\* >>]


(* maximal reconvergence test *)
\* ThreadInstructions ==  [t \in 1..NumThreads |-> 
\* <<
\* "OpLabel",
\* "OpLoopMerge",
\* "OpBranch",
\* "OpLabel",
\* "OpSelectionMerge",
\* "OpBranchConditional",
\* "OpLabel",
\* "OpBranch",
\* "OpLabel",
\* "OpBranch",
\* "OpLabel",
\* "OpBranch",
\* "OpLabel",
\* "Terminate"
\* >>]
\* ThreadArguments == [t \in 1..NumThreads |-> 
\* <<
\* <<Var("literal", "loop", 1, Index(-1))>>,
\* <<Var("literal", "D", 13, Index(-1)), Var("literal", "continue", 11, Index(-1))>>,
\* <<Var("literal", "A", 4, Index(-1))>>,
\* <<Var("literal", "A", 4, Index(-1))>>,
\* <<Var("literal", "C", 9, Index(-1))>>,
\* <<Var("literal", "", TRUE, Index(-1)), Var("literal", "B", 7, Index(-1)), Var("literal", "C", 9, Index(-1))>>,
\* <<Var("literal", "B", 7, Index(-1))>>,
\* <<Var("literal", "D", 13, Index(-1))>>,
\* <<Var("literal", "C", 9, Index(-1))>>,
\* <<Var("literal", "continue", 11, Index(-1))>>,
\* <<Var("literal", "continue", 11, Index(-1))>>,
\* <<Var("literal", "loop", 1, Index(-1))>>,
\* <<Var("literal", "D", 13, Index(-1))>>,
\* <<>>
\* >>]

(* Program *)

INSTANCE ProgramConf

(* Inovactions within a tangle are required to execute tangled instruction concurrently, examples or opGroup operations and opControlBarrier  *)
TangledInstructionSet == {"OpControlBarrier, OpGroupAll"}
MergedInstructionSet == {"OpLoopMerge", "OpSelectionMerge"}
BlockTerminationInstructionSet == {"OpBranch", "OpBranchConditional", "Terminate"}
BranchInstructionSet == {"OpBranch", "OpBranchConditional"}
\* Tangle: 
Tangle(ts) == 
    [threads |-> ts]
\* Block: A contiguous sequence of instructions starting with an OpLabel, ending with a block termination instruction. A block has no additional label or block termination instructions.
\* block termination instruction: OpBranch, OpBranchConditional, Terminate
\* OpLabel is define as a variable that has pc as its value field and its opLabel as its name field
Block(opLabel, terminatedInstr, tangle, type) == 
    [opLabelIdx |-> opLabel,
    terminatedInstrIdx |-> terminatedInstr,
    tangle |-> tangle,
    type |-> type]

GenerateCFG(blocks, branch) == 
    [node |-> blocks,
    edge |-> branch]


IsTerminationInstruction(instr) ==
    instr \in BlockTerminationInstructionSet

IsBranchInstruction(instr) ==
    instr \in BranchInstructionSet

IsMergedInstruction(instr) ==
    instr \in MergedInstructionSet

IsOpLabel(instr) ==
    instr = "OpLabel"

IsMergeBlock(block) ==
    block.type = "Merge"

\* helper function to extract the OpLabel field from the block
ExtractOpLabelIdxSet(blocks) ==
    {blocks[blockIdx].opLabelIdx : blockIdx \in 1..Len(blocks)}

\* make non-order-sensitive sequence becomes enumerable
SeqToSet(seq) == { seq[i]: i \in 1..Len(seq) }

\* update the sequence of sets
newSeqOfSets(seq, idx, newSet) == [seq EXCEPT ![idx] = newSet]

\* BoundedSeq: return a set of all sequences of length at most n, this helps to make the sequence enumerable
BoundedSeq(S, N) == UNION { [1..n -> S]: n \in 0..N}

(* Helper function to find the block that contains the given index *)
FindCurrentBlock(blocks, index) == 
    CHOOSE block \in SeqToSet(blocks): block.opLabelIdx <= index /\ block.terminatedInstrIdx >= index

\* (* Helper function to find the block that starts with the given name to OpLabel *)
\* FindBlockbyOpLabel(blocks, name) == 
\*     CHOOSE k \in 1..Len(blocks) : \E j \in 1..Len(ThreadInstructions[1]) : ThreadInstructions[1][j] = "OpLabel" /\ GetVal(ThreadArguments[1][blocks[k].opLabelIdx]) = j

(* Helper function to find the block that starts with the given index to OpLabel *)
FindBlockbyOpLabelIdx(blocks, index) == 
    CHOOSE block \in SeqToSet(blocks): block.opLabelIdx = index

(* Helper function to find the block that ends with the given index to termination instruction *)
FindBlockByTerminationIns(blocks, index) == 
    CHOOSE block \in SeqToSet(blocks): block.terminatedInstrIdx = index


\* function to determine if the merge instruction contains the given label as operand
\* mergeInsIdx is the pc of the merge instruction
\* opLabel is the value(label) that we are looking for
MergeInstContainsLabel(mergeInsIdx, opLabel) == 
   IF ThreadInstructions[1][mergeInsIdx] = "OpLoopMerge" THEN
        ThreadArguments[1][mergeInsIdx][1].name = opLabel \/ ThreadArguments[1][mergeInsIdx][2].name = opLabel
    ELSE IF ThreadInstructions[1][mergeInsIdx] = "OpSelectionMerge" THEN
        ThreadArguments[1][mergeInsIdx][1].name = opLabel
    ELSE
        FALSE

MergeInstContainsLabelIdx(mergeInsIdx, opLabelIdx) == 
   IF ThreadInstructions[1][mergeInsIdx] = "OpLoopMerge" THEN
        GetVal(-1, ThreadArguments[1][mergeInsIdx][1]) = opLabelIdx \/ GetVal(-1, ThreadArguments[1][mergeInsIdx][2]) = opLabelIdx
    ELSE IF ThreadInstructions[1][mergeInsIdx] = "OpSelectionMerge" THEN
        GetVal(-1, ThreadArguments[1][mergeInsIdx][1]) = opLabelIdx
    ELSE
        FALSE


\* lookback funciton that helps to determine if the current block is a merge block
\* startIdx is the pc of the instruction(OpLabel) that starts the current block
DetermineBlockType(startIdx) ==
    IF \E instIdx \in 1..(startIdx-1):
        IsMergedInstruction(ThreadInstructions[1][instIdx]) /\ MergeInstContainsLabelIdx(instIdx, startIdx)
    THEN 
        "Merge"
    ELSE 
        "None"


\* node is the index to the opLabel
RECURSIVE DFS(_, _, _, _, _)
DFS(node, cfg, visited, finished, backEdges) ==
    LET
        newVisited == visited \union {node}
        successors == {n \in ExtractOpLabelIdxSet(cfg.node) : <<node, n>> \in cfg.edge}
        newBackEdges == 
            LET
                newLoopEdges == 
                    {<<node, s>> : s \in visited} \cap 
                    {<<node, s>> : s \in successors}
            IN
            backEdges \union {edge \in newLoopEdges: edge[2] \notin finished}
    IN
    IF node \in finished THEN
        [visited |-> visited, finished |-> finished, backEdges |-> backEdges]
    ELSE IF \A s \in successors : s \in visited
    THEN 
        [visited |-> newVisited, 
         finished |-> finished \union {node}, 
         backEdges |-> newBackEdges]
    ELSE
        LET
            unvisitedSuccs == {s \in successors : s \notin visited}
            RECURSIVE DFSAll(_, _, _, _)
            DFSAll(nodes, v, f, b) ==
                IF nodes = {} THEN [visited |-> v, finished |-> f, backEdges |-> b]
                ELSE
                    LET 
                        next == CHOOSE n \in nodes : TRUE
                        result == DFS(next, cfg, v, f, b)
                    IN
                    DFSAll(nodes \ {next}, result.visited, result.finished, result.backEdges)
        IN
        LET
            result == DFSAll(unvisitedSuccs, newVisited, finished, newBackEdges)
        IN
        [visited |-> result.visited, 
         finished |-> result.finished \union {node}, 
         backEdges |-> result.backEdges]

\* Given a CFG, identify all the back edges in the CFG
\* Node is the index to the opLabel
IdentifyLoops(cfg) ==
    LET
        startNode == 1 \* Start from the entry block
        result == DFS(startNode, cfg, {}, {}, {})
    IN
    result.backEdges

RECURSIVE LoopNestingDepth(_, _, _, _)
LoopNestingDepth(node, cfg, loops, visited) ==
    LET
        successors == {n \in ExtractOpLabelIdxSet(cfg.node) : <<node, n>> \in cfg.edge}
        loopEdges == {e \in loops : e[2] = node}
    IN
    IF node \in visited THEN 0  \* Prevent infinite recursion on cycles
    ELSE IF loopEdges = {} THEN 0
    ELSE 1 + Max({LoopNestingDepth(e[1], cfg, loops \ {e}, visited \union {node}) : e \in loopEdges})

MaxLoopNestingDepth(cfg) ==
    LET 
        loops == IdentifyLoops(cfg)
    IN
    Max({LoopNestingDepth(n, cfg, loops, {}) : n \in ExtractOpLabelIdxSet(cfg.node)})


SuggestedPathLength(cfg) ==
    LET
        loopDepth == MaxLoopNestingDepth(cfg)
        nodeCount == Cardinality(DOMAIN cfg.node)
    IN
        nodeCount * (2 ^ loopDepth)


RECURSIVE GeneratePaths(_, _, _)
GeneratePaths(node, cfg, length) ==
  IF length = 0 THEN {<<>>}
  ELSE
    LET 
      successors == {n \in ExtractOpLabelIdxSet(cfg.node) : <<node, n>> \in cfg.edge}
      subpaths == UNION {GeneratePaths(s, cfg, length - 1) : s \in successors}
    IN
    {<<node>> \o path : path \in subpaths}

ValidPaths(startNode, cfg, maxPathLength) == 
    UNION {GeneratePaths(startNode, cfg, len) : len \in 1..MaxPathLength}

\* return a set of all paths in graph G
StructuredControlFlowPaths(G) == {
    \* fixme: we need to use ExtractOpLabelIdxSet as node are records, which are non-enumerable
    \* p \in BoundedSeq(ExtractOpLabelIdxSet(CFG.node), MaxPathLength) :
    p \in ValidPaths(1, CFG, MaxPathLength) :
        /\ p # <<>>(* p is not an empty sequence *)
        /\ \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in CFG.edge
    }

\* Return the set of paths from the entry block to block B
\* B is the index to the opLabel
\* StructuredControlFlowPathsTo(B) =={
\*     p \in BoundedSeq(ExtractOpLabelIdxSet(CFG.node), Len(CFG.node)) :
\*         /\ p # <<>>(* p is not an empty sequence *)
\*         /\ p[1] = 1
\*         /\ p[Len(p)] = B
\*         /\ \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in CFG.edge
\*     }
\* StructuredControlFlowPathsTo(B) =={
\*     p \in BoundedSeq(CFG.node, Len(CFG.node)) :
\*         /\ p # <<>>(* p is not an empty sequence *)
\*         /\ p[1].opLabelIdx = 1
\*         /\ p[Len(p)].opLabelIdx = B
\*         /\ \A i \in 1..(Len(p) - 1) : <<p[i].opLabelIdx, p[i+1].opLabelIdx>> \in CFG.edge
\*     }

\* fixme: maximum length of the path should be sounded.
StructuredControlFlowPathsTo(B) =={
    \* fixme: we need to use ExtractOpLabelIdxSet as node are records, which are non-enumerable
    \* p \in BoundedSeq(ExtractOpLabelIdxSet(CFG.node), MaxPathLength) :
    p \in ValidPaths(1, CFG, MaxPathLength) :
        /\ p # <<>>(* p is not an empty sequence *)
        /\ p[1] = 1
        /\ p[Len(p)] = B
        /\ \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in CFG.edge
    }



\* A block A structurally dominates a block B if every structured control flow path to B includes A
\* A and B are the indice to the opLabel
StructurallyDominates(A, B) == \A p \in StructuredControlFlowPathsTo(B) : \E i \in 1..Len(p) : p[i] = A

\* A block A strictly structurally dominates a block B if A structurally dominates B and A != B
\* A and B are the indice to the opLabel
StrictlyStructurallyDominates(A, B) == 
    /\ StructurallyDominates(A, B)
    /\ A # B

\* Generate blocks from the instructions
GenerateBlocks(insts) == 
  [i \in 1..Len(insts) |-> 
     IF IsOpLabel(insts[i]) THEN 
       LET terminationIndex == Min({j \in i+1..Len(insts) : IsTerminationInstruction(insts[j])} \cup {Len(insts)})
           tangle == IF i = 1 THEN [wg \in 1..NumWorkGroups |-> ThreadsWithinWorkGroup(wg-1)] ELSE [wg \in 1..NumWorkGroups |-> {}]  (* First OpLabel includes all threads as tangle *)
       IN 
            Block(i, terminationIndex, tangle, DetermineBlockType(i))
     ELSE Block(-1, <<>>, <<>>, "None")
  ]


\* startIndex is the pc of the instruction(OpLabel) that starts the block
\* terminationIndex is the pc of the termination instruction that terminates the block
\* return set of indices to the OpLabel instructions
\* OpLabel is obtained from the merge instruction and branch instruction
FindTargetBlocks(startIndex, terminationIndex) == 
    LET
        mergeInstr == IF terminationIndex > startIndex THEN ThreadInstructions[1][terminationIndex - 1] ELSE <<>>
    IN
        IF mergeInstr = "OpLoopMerge" THEN
            {GetVal(-1, ThreadArguments[1][terminationIndex - 1][1]), GetVal(-1, ThreadArguments[1][terminationIndex - 1][2])} \cup 
                (IF ThreadInstructions[1][terminationIndex] = "OpBranch" THEN
                    {GetVal(-1, ThreadArguments[1][terminationIndex][1])}
                ELSE IF ThreadInstructions[1][terminationIndex] = "OpBranchConditional" THEN
                    {GetVal(-1, ThreadArguments[1][terminationIndex][2]), GetVal(-1, ThreadArguments[1][terminationIndex][3])}
                ELSE
                    {})
        ELSE IF mergeInstr = "OpSelectionMerge" THEN
            {GetVal(-1, ThreadArguments[1][terminationIndex - 1][1])} \cup 
                (IF ThreadInstructions[1][terminationIndex] = "OpBranch" THEN
                    {GetVal(-1, ThreadArguments[1][terminationIndex][1])}
                ELSE IF ThreadInstructions[1][terminationIndex] = "OpBranchConditional" THEN
                    {GetVal(-1, ThreadArguments[1][terminationIndex][2]), GetVal(-1, ThreadArguments[1][terminationIndex][3])}
                ELSE
                    {})
        ELSE 
            IF ThreadInstructions[1][terminationIndex] = "OpBranch" THEN
                {GetVal(-1, ThreadArguments[1][terminationIndex][1])}
            ELSE IF ThreadInstructions[1][terminationIndex] = "OpBranchConditional" THEN
                {GetVal(-1, ThreadArguments[1][terminationIndex][2]), GetVal(-1, ThreadArguments[1][terminationIndex][3])}
            ELSE
                {}

                    
                    
\* startIndex is the pc of the instruction(OpLabel) that starts the block
\* terminationIndex is the pc of the termination instruction that terminates the block
\* return set of indices to the OpLabel instructions of the merge block for current header block
\* OpLabel is obtained from the merge instruction and branch instruction
FindMergeBlocksIdx(startIndex, terminationIndex) == 
    LET
        mergeInstr == IF terminationIndex > startIndex THEN ThreadInstructions[1][terminationIndex - 1] ELSE <<>>
    IN
        IF mergeInstr = "OpLoopMerge" THEN
            {GetVal(-1, ThreadArguments[1][terminationIndex - 1][1]), GetVal(-1, ThreadArguments[1][terminationIndex - 1][2])}
        ELSE IF mergeInstr = "OpSelectionMerge" THEN
            {GetVal(-1, ThreadArguments[1][terminationIndex - 1][1])}
        ELSE 
            {}

\* mergeBlock is the current merge block,
\* return set of header blocks for current merge block
FindHeaderBlocks(mergeBlock) == 
    {block \in SeqToSet(CFG.node):
        mergeBlock.opLabelIdx \in FindMergeBlocksIdx(block.opLabelIdx, block.terminatedInstrIdx)}

\* Rule 4: If there exists OpKill in the block, then remove thread itself from the tangle of all merge blocks as well as current block
\* for every header block that structurally dominates the current block
TerminateUpdate(wgid, t, currentLabelIdx) ==
    [i \in 1..Len(CFG.node) |->
        IF IsMergeBlock(CFG.node[i]) /\ (\E block \in FindHeaderBlocks(CFG.node[i]) : 
            StrictlyStructurallyDominates(block.opLabelIdx, currentLabelIdx)) 
        THEN
            \* Block(CFG.node[i].opLabelIdx, CFG.node[i].terminatedInstrIdx, CFG.node[i].tangle \ {t}, CFG.node[i].type)
            Block(CFG.node[i].opLabelIdx, CFG.node[i].terminatedInstrIdx, newSeqOfSets(CFG.node[i].tangle, wgid, CFG.node[i].tangle[wgid] \{t}), CFG.node[i].type)
        ELSE
            CFG.node[i]
    ] 

\* BranchUpdate: update the tangle of the blocks that are pointed by the branch instruction
\* tangle is the tangle that is going to be updated to the blocks, each workgroup has its own tangle
\* opLabelIdxSet is the set of indices to the opLabel instructions that are pointed by the branch instruction
\* choosenBranchIdx is the index to the opLabel instruction that is choosen by the branch instruction
BranchUpdate(wgid, t, tangle, opLabelIdxSet, choosenBranchIdx) ==
    [i \in 1..Len(CFG.node) |-> 
        IF CFG.node[i].opLabelIdx \in opLabelIdxSet THEN
            \* rule 2: If a thread reaches a branch instruction and the block it points to has empty tangle, update the tangle of tha block to the tangle of the merge instruction
            \* And remove the thread itself from the tangle of unchoosen block if that block is not a merge block
            IF CFG.node[i].tangle[wgid] = {} THEN
                \* unchoosen block and is not a merge block
                IF CFG.node[i].opLabelIdx # choosenBranchIdx /\ CFG.node[i].type # "Merge" THEN
                    \* Block(CFG.node[i].opLabelIdx, CFG.node[i].terminatedInstrIdx, tangle \ {t}, CFG.node[i].type)
                    Block(CFG.node[i].opLabelIdx, CFG.node[i].terminatedInstrIdx, newSeqOfSets(CFG.node[i].tangle, wgid, tangle \{t}), CFG.node[i].type)
                ELSE
                    Block(CFG.node[i].opLabelIdx, CFG.node[i].terminatedInstrIdx, newSeqOfSets(CFG.node[i].tangle, wgid, tangle), CFG.node[i].type)
            \* rule 3: If the unchoosen block has non-empty tangle and is not a merge block, remove the thread from the tangle
            ELSE IF CFG.node[i].opLabelIdx # choosenBranchIdx /\ CFG.node[i].type # "Merge" THEN
                \* Block(CFG.node[i].opLabelIdx, CFG.node[i].terminatedInstrIdx, CFG.node[i].tangle \ {t}, CFG.node[i].type)
                Block(CFG.node[i].opLabelIdx, CFG.node[i].terminatedInstrIdx, newSeqOfSets(CFG.node[i].tangle, wgid, tangle \{t}), CFG.node[i].type)
            ELSE 
                CFG.node[i]
        ELSE 
            CFG.node[i]
    ]

\* Helper function that return the updated blocks in CFG regarding the merge instruction
MergeUpdate(wgid, currentLabelIdx, tangle, opLabelIdxSet) ==
    [i \in 1..Len(CFG.node) |-> 
        IF CFG.node[i].opLabelIdx \in opLabelIdxSet THEN
            \* rule 1: If a thread reaches a merge instruction and the block it points to has empty tangle, update the tangle of tha block to the tangle of the merge instruction
            IF CFG.node[i].tangle[wgid] = {} THEN
                Block(CFG.node[i].opLabelIdx, CFG.node[i].terminatedInstrIdx, newSeqOfSets(CFG.node[i].tangle, wgid, tangle), CFG.node[i].type) 
            ELSE 
                CFG.node[i]
        ELSE
            CFG.node[i]
    ]



\* GetLabelPc(label) == 
\*     CHOOSE i \in 1..Len(ThreadInstructions[1]) : ThreadInstructions[1][i] = "OpLabel" /\ GetVal(-1, ThreadArguments[1][i][1]) = GetVal(-1, label)
    
InitCFG == 
    LET blocks == SelectSeq(GenerateBlocks(ThreadInstructions[1]), LAMBDA b: b.opLabelIdx # -1)
        graph == GenerateCFG(blocks, 
                UNION { {<<blocks[i].opLabelIdx, target>> : target \in FindTargetBlocks(blocks[i].opLabelIdx, blocks[i].terminatedInstrIdx)} : i \in DOMAIN blocks }
                )
    IN 
        /\  CFG = graph
        /\  MaxPathLength = SuggestedPathLength(graph)

\* InitGPU ==
\*     \* for spinlock
\*     \* /\  globalVars = {Var("global", "lock", 0, Index(-1))}
\*     \* for producer-consumer
\*     /\  globalVars = {Var("global", "msg", 0, Index(-1))}
\*     \* decoupled lookback
\*     \* /\ globalVars = {Var("global", "partition", 0, Index(-1)), Var("global", "result", [t \in 1..NumThreads |-> 0], Index(0)), Var("global", "workgroupPartition", [wg \in 1..NumWorkGroups |-> 0], Index(0))}

(* Global Variables *)

InitProgram ==
    /\ InitCFG
    /\ InitGPU

====



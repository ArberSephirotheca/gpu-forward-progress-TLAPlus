---- MODULE MCProgram ----
LOCAL INSTANCE Integers
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
\* LOCAL INSTANCE MCLayout
LOCAL INSTANCE TLC

VARIABLES globalVars, threadLocals, CFG, labels

(* Layout Configuration *)
SubgroupSize == 1
WorkGroupSize == 1
NumWorkGroups == 2
NumThreads == WorkGroupSize * NumWorkGroups

Threads == {tid : tid \in 1..NumThreads}

Scheduler == "OBE"


(* Variable *)
Var(varScope, varName, varValue, index) == 
    [scope |-> varScope,
     name  |-> varName, 
     value |-> varValue,
     index |-> index]

Label(name, pc) == 
    [name |-> name,
     pc |-> pc]

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

(* Thread Configuration *)
InstructionSet == {"Assignment", "GetGlobalId", "OpAtomicLoad", "OpAtomicStore", "OpAtomicAdd" , "OpAtomicSub", "OpGroupAll", 
"OpAtomicCompareExchange" ,"OpAtomicExchange", "OpBranch", "OpBranchConditional", "OpControlBarrier", "OpLoopMerge",
"OpSelectionMerge", "OpLabel", "Terminate"}
VariableScope == {"global", "shared", "local", "literal", "intermediate"}
ScopeOperand == {"workgroup", "subgroup", "tangle"}
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
ThreadInstructions ==  [t \in 1..NumThreads |-> 
<<
"OpLabel",
"OpLoopMerge",
"OpBranch",
"OpLabel",
"OpSelectionMerge",
"OpBranchConditional",
"OpLabel",
"OpBranch",
"OpLabel",
"OpBranch",
"OpLabel",
"OpBranch",
"OpLabel",
"Terminate"
>>]
ThreadArguments == [t \in 1..NumThreads |-> 
<<
<<Var("literal", "", "loop", Index(-1))>>,
<<Var("literal", "", "D", Index(-1)), Var("literal", "", "continue", Index(-1))>>,
<<Var("literal", "", "A", Index(-1))>>,
<<Var("literal", "", "A", Index(-1))>>,
<<Var("literal", "", "C", Index(-1))>>,
<<Var("literal", "", TRUE, Index(-1)), Var("literal", "", "B", Index(-1)), Var("literal", "", "C", Index(-1))>>,
<<Var("literal", "", "B", Index(-1))>>,
<<Var("literal", "", "D", Index(-1))>>,
<<Var("literal", "", "C", Index(-1))>>,
<<Var("literal", "", "continue", Index(-1))>>,
<<Var("literal", "", "continue", Index(-1))>>,
<<Var("literal", "", "loop", Index(-1))>>,
<<Var("literal", "", "D", Index(-1))>>>,
<<>>
>>]

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
Block(opLabel, terminatedInstr, tangle, type) == 
    [opLabel |-> opLabel,
    terminatedInstr |-> terminatedInstr,
    tangle |-> tangle
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

IsMergeBlcok(block) ==
    block.type = "Merge"
            
GenerateBlocks(insts) == 
  [i \in 1..Len(insts) |-> 
     IF IsOpLabel(insts[i]) THEN 
       LET terminationIndex == Min({j \in i+1..Len(insts) : IsTerminationInstruction(insts[j])} \cup {Len(insts)})
           tangle == IF i = 1 THEN [t \in 1..NumThreads |-> t] ELSE <<>>  (* First OpLabel includes all threads as tangle *)
       IN Block(i, terminationIndex, tangle, "None")
     ELSE Block(<<>>, <<>>, <<>>, "None")
  ]

(* Helper function to find the block that contains the given index *)
FindCurrentBlock(blocks, index) == 
    CHOOSE k \in 1..Len(blocks) : blocks[k].opLabel <= index /\ blocks[k].terminatedInstr >= index

(* Helper function to find the block that starts with the given index to OpLabel *)
FindBlockbyOpLabel(blocks, index) == 
    CHOOSE k \in 1..Len(blocks) : blocks[k].opLabel = index

(* Helper function to find the block that ends with the given index to termination instruction *)
FindBlockByTerminationIns(blocks, index) == 
    CHOOSE k \in 1..Len(blocks) : blocks[k].terminatedInstr = index

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
FindMergeBlocks(startIndex, terminationIndex) == 
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
    {blcok \in StructuredControlFlowPathsTo(mergeBlock.opLabel) : mergeBlock.opLabel \in FindMergeBlocks(block.opLabel, block.terminatedInstr)}
        
\* return a set of all paths in graph G
StructuredControlFlowPaths(G) == 
    {p \in Seq(G.node) :
    /\ p # << >>
    /\ \A i \in 1..(Len(p)-1) : <<p[i].opLabel, p[i+1].opLabel>> \in G.edge}

\* Return the set of paths from the entry block to block B
\* B is the index to the opLabel
StructuredControlFlowPathsTo(B) == {p \in Seq(CFG.node) :
                  /\ p # << >>
                  /\ p[1].opLabel = 1
                  /\ p[Len(p)].opLabel = B
                  /\ \A i \in 1..(Len(p)-1) : <<p[i].opLabel, p[i+1].opLabel>> \in edges}



\* A block A structurally dominates a block B if every structured control flow path to B includes A
\* A and B are the indice to the opLabel
StructurallyDominates(A, B) == \A p \in StructuredControlFlowPathsTo(B) : \E i \in 1..Len(p) : p[i] = A

\* A block A strictly structurally dominates a block B if A structurally dominates B and A != B
\* A and B are the indice to the opLabel
StrictlyStructurallyDominates(A, B) == /\ StructurallyDominates(A, B)
                           /\ A # B

\* If there exists OpKill in the block, then remove thread itself from the tangle of all merge blocks as well as current block
\* for every header block that structurally dominates the current block
TerminateUpdate(t, currentLabelIdx) ==
    CFG.blocks' = [i \in 1..Len(CFG.blocks) |->
        IF IsMergeBlcok(CFG.blocks[i]) /\ \E block \in FindHeaderBlocks(CFG.blocks[i]) : StrictlyStructurallyDominates(block.opLabel, currentLabelIdx) THEN
            Block(CFG.blocks[i].opLabel, CFG.blocks[i].terminatedInstr, CFG.blocks[i].tangle \ {t}, CFG.blocks[i].type)
        ELSE
            CFG.blocks[i]
    ] 

BranchUpdate(t, tangle, opLabelIdxSet, choosenBranchIdx) ==
    CFG.blocks' = [i \in 1..Len(CFG.blocks) |-> 
        IF CFG.blocks[i].opLabel \in opLabelIdxSet THEN
            \* rule 2: If a thread reaches a branch instruction and the block it points to has empty tangle, update the tangle of tha block to the tangle of the merge instruction
            \* And remove the thread itself from the tangle of unchoosen block if that block is not a merge block
            IF CFG.blocks[i].tangle = <<>> THEN
                \* unchoosen block and is not a merge block
                IF CFG.blocks[i].opLabel # choosenBranchIdx /\ CFG.blocks[i].type # "Merge" THEN
                    Block(CFG.blocks[i].opLabel, CFG.blocks[i].terminatedInstr, tangle \ {t}, CFG.blocks[i].type)
                ELSE
                    Block(CFG.blocks[i].opLabel, CFG.blocks[i].terminatedInstr, tangle, CFG.blocks[i].type)
            \* rule 3: If the unchoosen block has non-empty tangle and is not a merge block, remove the thread from the tangle
            ELSE IF CFG.blocks[i].opLabel # choosenBranchIdx /\ CFG.blocks[i].type # "Merge" THEN
                Block(CFG.blocks[i].opLabel, CFG.blocks[i].terminatedInstr, CFG.blocks[i].tangle \ {t}, CFG.blocks[i].type)
            ELSE 
                CFG.blocks[i]
        ELSE 
            CFG.blocks[i]
    ]

\* Helper function to update the related blocks regarding the merge instruction
MergeUpdate(currentLabelIdx, tangle, opLabelIdxSet) ==
    CFG.blocks' = [i \in 1..Len(CFG.blocks) |-> 
        IF CFG.blocks[i].opLabel \in opLabelIdxSet THEN
            \* rule 1: If a thread reaches a merge instruction and the block it points to has empty tangle, update the tangle of tha block to the tangle of the merge instruction
            IF CFG.blocks[i].tangle = <<>> THEN
                Block(CFG.blocks[i].opLabel, CFG.blocks[i].terminatedInstr, tangle) 
            ELSE 
                CFG.blocks[i]
        ELSE
            CFG.blocks[i]
    ]



GetLabelPc(label) == 
    CHOOSE i \in 1..Len(ThreadInstructions[1]) : ThreadInstructions[1][i] = "OpLabel" /\ GetVal(-1, ThreadArguments[1][i][1]) = GetVal(-1, label)
    
InitCFG == 
    LET blocks == SelectSeq(GenerateBlocks(ThreadInstructions[1]), LAMBDA b: b.opLabel # <<>>) 
    IN 
        CFG = GenerateCFG(blocks, 
                UNION { {<<i, target>> : target \in FindTargetBlocks(blocks[i].opLabel, blocks[i].terminatedInstr)} : i \in DOMAIN blocks }
                )
InitGPU ==
    \* for spinlock
    \* /\  globalVars = {Var("global", "lock", 0, Index(-1))}
    \* for producer-consumer
    /\  globalVars = {Var("global", "msg", 0, Index(-1))}
    \* decoupled lookback
    \* /\ globalVars = {Var("global", "partition", 0, Index(-1)), Var("global", "result", [t \in 1..NumThreads |-> 0], Index(0)), Var("global", "workgroupPartition", [wg \in 1..NumWorkGroups |-> 0], Index(0))}
    /\  labels = {}

InitProgram ==
    /\ InitCFG
    /\ InitGPU

GlobalInvocationId(tid) == tid-1

LocalInvocationId(tid) == GlobalInvocationId(tid) % WorkGroupSize

WorkGroupId(tid) == GlobalInvocationId(tid) \div WorkGroupSize
    
SubgroupId(tid) == LocalInvocationId(tid) \div SubgroupSize

SubgroupInovcationId(tid) == LocalInvocationId(tid) % SubgroupSize

====



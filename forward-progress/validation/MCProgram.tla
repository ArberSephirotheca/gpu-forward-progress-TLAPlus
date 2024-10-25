---- MODULE MCProgram ----
LOCAL INSTANCE Integers
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE FiniteSets
\* LOCAL INSTANCE MCLayout
LOCAL INSTANCE TLC

VARIABLES globalVars, threadLocals, CFG, MaxPathLength, validPaths
(* Layout Configuration *)

Threads == {tid : tid \in 1..NumThreads}

(* Variable *)
Var(varScope, varName, varValue, index) == 
    [scope |-> varScope,
     name  |-> varName, 
     value |-> varValue,
     index |-> index]

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
    \* IF IsShared(var) \/ IsGlobal(var) THEN 
    IF IsGlobal(var) THEN 
        \E variable \in globalVars : variable.name = var.name 
    ELSE 
        \E variable \in threadLocals[workgroupId] : (variable.name = var.name /\ variable.scope = var.scope)


(* todo: resolve scope if duplicate name *)
GetVar(workgroupId, var) == 
    IF IsGlobal(var) THEN 
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
        \* GetVal(workgroupId, expr)
    

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

SubgroupInvocationId(tid) == LocalInvocationId(tid) % SubgroupSize

ThreadsWithinWorkGroup(wgid) ==  {tid \in Threads : WorkGroupId(tid) = wgid}

ThreadsWithinSubgroup(sid, wgid) == {tid \in Threads : SubgroupId(tid) = sid} \intersect ThreadsWithinWorkGroup(wgid)

(* Thread Configuration *)
InstructionSet == {"Assignment", "OpAtomicLoad", "OpAtomicStore", "OpAtomicIncrement" , "OpAtomicDecrement", "OpGroupAll", "OpGroupAny", "OpGroupNonUniformAll", "OpGroupNonUniformAny",
"OpAtomicCompareExchange" ,"OpAtomicExchange", "OpBranch", "OpBranchConditional", "OpSwitch", "OpControlBarrier", "OpLoopMerge",
"OpSelectionMerge", "OpLabel", "Terminate", "OpLogicalOr", "OpLogicalAnd", "OpLogicalEqual", "OpLogicalNotEqual", "OpLogicalNot",
"OpEqual", "OpNotEqual", "OpLess", "OpLessOrEqual", "OpGreater", "OpGreaterOrEqual",
"OpAdd", "OpAtomicAdd", "OpSub", "OpAtomicSub", "OpMul"}
VariableScope == {"global", "shared", "local", "literal", "intermediate"}
ScopeOperand == {"workgroup", "subgroup", "tangle"}
MemoryOperationSet == {"OpAtomicLoad", "OpAtomicStore", "OpAtomicIncrement" , "OpAtomicDecrement", "OpAtomicAdd" , "OpAtomicSub", "OpAtomicCompareExchange" ,"OpAtomicExchange"}

IsMemoryOperation(inst) == 
    inst \in MemoryOperationSet
(* Program *)


EntryLabel == Min({idx \in 1..Len(ThreadInstructions[1]) : ThreadInstructions[1][idx] = "OpLabel"})

INSTANCE ProgramConf

(* Inovactions within a tangle are required to execute tangled instruction concurrently, examples or opGroup operations and opControlBarrier  *)
TangledInstructionSet == {"OpControlBarrier, OpGroupAll", "OpGroupAny", "OpGroupNonUniformAll", "OpGroupNonUniformAny"}
MergedInstructionSet == {"OpLoopMerge", "OpSelectionMerge"}
BlockTerminationInstructionSet == {"OpBranch", "OpBranchConditional", "OpSwitch", "Terminate"}
BranchInstructionSet == {"OpBranch", "OpBranchConditional", "OpSwitch"}
\* Tangle: 
Tangle(ts) == 
    [threads |-> ts]


\* Block: A contiguous sequence of instructions starting with an OpLabel, ending with a block termination instruction. 
\* A block has no additional label or block termination instructions.
\* block termination instruction: OpBranch, OpBranchConditional, Terminate
\* OpLabel is define as a variable that has pc as its value field and its opLabel as its name field
Block(opLabel, terminatedInstr, tangle, merge, initialized, mergeSet) == 
    [opLabelIdx |-> opLabel,
    terminatedInstrIdx |-> terminatedInstr,
    tangle |-> tangle,
    merge |-> merge,
    initialized |-> initialized,
    mergeSet |-> mergeSet]

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
    block.merge = TRUE

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

\* helper function that returns the index of the first OpLabel instruction
\* We do not need to worry about empty set as we are guaranteed to have 
\* at least one OpLabel instruction (entry block)
\* EntryLabel(insts) ==
\*     Min({idx \in 1..Len(insts) : insts[idx] = "OpLabel"})


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
        GetVal(-1, ThreadArguments[1][mergeInsIdx][1]) = opLabelIdx 
        \/ GetVal(-1, ThreadArguments[1][mergeInsIdx][2]) = opLabelIdx
    ELSE IF ThreadInstructions[1][mergeInsIdx] = "OpSelectionMerge" THEN
        GetVal(-1, ThreadArguments[1][mergeInsIdx][1]) = opLabelIdx
    ELSE
        FALSE


\* lookback function that helps to determine if the current block is a merge block
\* startIdx is the pc of the instruction(OpLabel) that starts the current block
DetermineBlockType(startIdx) ==
    IF \E instIdx \in 1..(startIdx-1):
        IsMergedInstruction(ThreadInstructions[1][instIdx]) 
        /\ MergeInstContainsLabelIdx(instIdx, startIdx)
    THEN 
        TRUE
    ELSE 
        FALSE


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
        startNode == EntryLabel \* Start from the entry block
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
  IF length = 0 THEN
    {<<>>}
  ELSE
    LET 
      successors == {n \in ExtractOpLabelIdxSet(cfg.node) : <<node, n>> \in cfg.edge}
      subpaths == UNION {GeneratePaths(s, cfg, length - 1) : s \in successors}
    IN
    {<<node>> \o path : path \in subpaths}

\* ValidPaths(startNode, cfg, maxPathLength) == 
\*     UNION {GeneratePaths(startNode, cfg, len) : len \in 1..maxPathLength}

\* only generate paths that are valid and size of maxPathLength
ValidPaths(startNode, cfg, maxPathLength) == 
    GeneratePaths(startNode, cfg, maxPathLength)
\* return a set of all paths in graph G
\* this should only be used as Init phase as validPath does not change during execution
StructuredControlFlowPaths(cfg, maxPathLength) == {
    p \in ValidPaths(EntryLabel, cfg, maxPathLength) :
        /\ p # <<>>(* p is not an empty sequence *)
        /\ p[1] = EntryLabel
        /\ \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in cfg.edge
    }


\* fixme: maximum length of the path should be sounded.
StructuredControlFlowPathsTo(B) =={
    p \in validPaths:
        /\ p # <<>>(* p is not an empty sequence *)
        /\ p[1] = EntryLabel
        /\ p[Len(p)] = B
        /\ \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in CFG.edge
    }

StructuredControlFlowPathsFromTo(StartNode, B) == {
    p \in validPaths:
        /\ p # <<>>  \* p is not an empty sequence
        /\ p[1] = StartNode
        /\ p[Len(p)] = B
        /\ \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in CFG.edge
}

StructurallyReachable(B) == StructuredControlFlowPathsTo(B) # {}

StructurallyReachableFrom(StartNode, B) == StructuredControlFlowPathsFromTo(StartNode, B) # {}

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
       LET terminationIndex == Min({j \in i+1..Len(insts) : 
           IsTerminationInstruction(insts[j])} \cup {Len(insts)})
           tangle == IF 
                        i = EntryLabel
                     THEN 
                        [wg \in 1..NumWorkGroups |-> ThreadsWithinWorkGroup(wg-1)] 
                     ELSE 
                        [wg \in 1..NumWorkGroups |-> {}]
           initialization == IF i = EntryLabel THEN [wg \in 1..NumWorkGroups |-> TRUE] ELSE [wg \in 1..NumWorkGroups |-> FALSE]
           mergeSet == IF ThreadInstructions[1][terminationIndex-1] = "OpLoopMerge" THEN
                    {GetVal(-1, ThreadArguments[1][terminationIndex-1][1]), GetVal(-1, ThreadArguments[1][terminationIndex-1][2])}
                ELSE IF ThreadInstructions[1][terminationIndex-1] = "OpSelectionMerge" THEN
                    {GetVal(-1, ThreadArguments[1][terminationIndex-1][1])}
                ELSE
                    {}
        
       IN 
            Block(i, terminationIndex, tangle, DetermineBlockType(i), initialization, mergeSet)
     ELSE Block(-1, <<>>, <<>>, FALSE, <<>>, {})
  ]


\* startIndex is the pc of the instruction(OpLabel) that starts the block
\* terminationIndex is the pc of the termination instruction that terminates the block
\* return set of indices to the OpLabel instructions
\* OpLabel is obtained from the merge instruction and branch instruction
FindTargetBlocks(startIndex, terminationIndex) == 
    LET
        mergeInstr == IF 
                        terminationIndex > startIndex 
                      THEN 
                      ThreadInstructions[1][terminationIndex - 1] 
                      ELSE 
                        <<>>
    IN
        IF mergeInstr = "OpLoopMerge" THEN
            {GetVal(-1, ThreadArguments[1][terminationIndex - 1][1]), 
                GetVal(-1, ThreadArguments[1][terminationIndex - 1][2])} \cup 
                (IF ThreadInstructions[1][terminationIndex] = "OpBranch" THEN
                    {GetVal(-1, ThreadArguments[1][terminationIndex][1])}
                ELSE IF ThreadInstructions[1][terminationIndex] = "OpBranchConditional" THEN
                    {GetVal(-1, ThreadArguments[1][terminationIndex][2]), 
                        GetVal(-1, ThreadArguments[1][terminationIndex][3])}
                ELSE
                    {})
        ELSE IF mergeInstr = "OpSelectionMerge" THEN
            {GetVal(-1, ThreadArguments[1][terminationIndex - 1][1])} \cup 
                (IF ThreadInstructions[1][terminationIndex] = "OpBranch" THEN
                    {GetVal(-1, ThreadArguments[1][terminationIndex][1])}
                ELSE IF ThreadInstructions[1][terminationIndex] = "OpBranchConditional" THEN
                    {GetVal(-1, ThreadArguments[1][terminationIndex][2]), 
                        GetVal(-1, ThreadArguments[1][terminationIndex][3])}
                ELSE
                    {})
        ELSE 
            IF ThreadInstructions[1][terminationIndex] = "OpBranch" THEN
                {GetVal(-1, ThreadArguments[1][terminationIndex][1])}
            ELSE IF ThreadInstructions[1][terminationIndex] = "OpBranchConditional" THEN
                {GetVal(-1, ThreadArguments[1][terminationIndex][2]), 
                    GetVal(-1, ThreadArguments[1][terminationIndex][3])}
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

\* Rule 4: If there exists termination instruction in the block, 
\* then remove thread itself from the tangle of all merge blocks as well as current block
\* for every header block that structurally dominates the current block
TerminateUpdate(wgid, t, currentLabelIdx) ==
    [i \in 1..Len(CFG.node) |->
        IF IsMergeBlock(CFG.node[i]) /\ (\E block \in FindHeaderBlocks(CFG.node[i]) : 
            StrictlyStructurallyDominates(block.opLabelIdx, currentLabelIdx)) 
        THEN
            Block(CFG.node[i].opLabelIdx, CFG.node[i].terminatedInstrIdx, 
            newSeqOfSets(CFG.node[i].tangle, wgid, CFG.node[i].tangle[wgid] \{t}), 
            CFG.node[i].merge, CFG.node[i].initialized, CFG.node[i].mergeSet)
        ELSE
            CFG.node[i]
    ] 

\* BranchUpdate: update the tangle of the blocks that are pointed by the branch instruction
\* tangle is the tangle that is going to be updated to the blocks, each workgroup has its own tangle
\* opLabelIdxSet is the set of indices to the opLabel instructions that are pointed by the branch instruction
\* choosenBranchIdx is the index to the opLabel instruction that is choosen by the branch instruction
BranchUpdate(wgid, t, currentBlock, tangle, opLabelIdxSet, chosenBranchIdx) ==
    [i \in 1..Len(CFG.node) |-> 
        IF  
            \* keep this order to avoid performance issue
            /\ CFG.node[i].opLabelIdx <= chosenBranchIdx 
            /\ currentBlock.opLabelIdx # CFG.node[i].opLabelIdx 
            /\ StructurallyReachableFrom(currentBlock.opLabelIdx, CFG.node[i].opLabelIdx) 
        THEN
            \* rule 2: If a thread reaches a branch instruction, for any reachable unitialized block from current block to chosen block,
            \* update the tangle of tha block to be the same as the tangle of current block.
            \* and remove the thread itself from the tangle of unchoosen block if that block is not a merge block for current block
            IF CFG.node[i].initialized[wgid] = FALSE THEN
                \* unchoosen block and is not a merge block
                IF CFG.node[i].opLabelIdx # chosenBranchIdx /\  CFG.node[i].opLabelIdx \notin  currentBlock.mergeSet THEN
                    Block(CFG.node[i].opLabelIdx, CFG.node[i].terminatedInstrIdx, 
                        newSeqOfSets(CFG.node[i].tangle, wgid, tangle \{t}), CFG.node[i].merge, [CFG.node[i].initialized EXCEPT ![wgid] = TRUE], CFG.node[i].mergeSet)
                ELSE
                    Block(CFG.node[i].opLabelIdx, CFG.node[i].terminatedInstrIdx,
                        newSeqOfSets(CFG.node[i].tangle, wgid, tangle), CFG.node[i].merge, [CFG.node[i].initialized EXCEPT ![wgid] = TRUE], CFG.node[i].mergeSet)
            \* rule 3: If the unchoosen block is initialized and is not a merge block for current block,
            \* remove the thread from the tangle
            ELSE IF CFG.node[i].opLabelIdx # chosenBranchIdx /\ CFG.node[i].opLabelIdx \notin currentBlock.mergeSet /\ CFG.node[i].initialized[wgid] = TRUE THEN
                Block(CFG.node[i].opLabelIdx, CFG.node[i].terminatedInstrIdx,
                newSeqOfSets(CFG.node[i].tangle, wgid, CFG.node[i].tangle[wgid] \{t}), CFG.node[i].merge, CFG.node[i].initialized, CFG.node[i].mergeSet)
            ELSE 
                CFG.node[i]
        ELSE 
            CFG.node[i]
    ]

\* Helper function that return the updated blocks in CFG regarding the merge instruction
MergeUpdate(wgid, currentLabelIdx, tangle, opLabelIdxSet) ==
    [i \in 1..Len(CFG.node) |-> 
        IF CFG.node[i].opLabelIdx \in opLabelIdxSet THEN
            \* rule 1: If a thread reaches a merge instruction and the block it points to has empty tangle, 
            \* update the tangle of tha block to the tangle of the merge instruction
            IF CFG.node[i].initialized[wgid] = FALSE THEN
                Block(CFG.node[i].opLabelIdx, CFG.node[i].terminatedInstrIdx, 
                    newSeqOfSets(CFG.node[i].tangle, wgid, tangle), CFG.node[i].merge, [CFG.node[i].initialized EXCEPT ![wgid] = TRUE], CFG.node[i].mergeSet) 
            ELSE 
                CFG.node[i]
        ELSE
            CFG.node[i]
    ]    
    
InitCFG == 
    LET blocks == SelectSeq(GenerateBlocks(ThreadInstructions[1]), LAMBDA b: b.opLabelIdx # -1)
        graph == GenerateCFG(blocks, 
                UNION { {<<blocks[i].opLabelIdx, target>> : 
                    target \in FindTargetBlocks(blocks[i].opLabelIdx, blocks[i].terminatedInstrIdx)} : i \in DOMAIN blocks }
                )
    IN 
        /\  LET maxPathLength == SuggestedPathLength(graph) 
            IN
                /\  CFG = graph
                /\  MaxPathLength = maxPathLength
                /\  validPaths = StructuredControlFlowPaths(graph, maxPathLength)


(* Global Variables *)

InitProgram ==
    /\ InitCFG
    /\ InitGPU

====



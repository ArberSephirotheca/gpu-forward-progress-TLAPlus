---- MODULE MCProgram ----
LOCAL INSTANCE Integers
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE FiniteSets
\* LOCAL INSTANCE MCLayout
LOCAL INSTANCE TLC

VARIABLES globalVars, threadLocals, Blocks
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

Inter(S) ==
  { x \in UNION S : \A t \in S : x \in t }
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

(* CFG *)

INSTANCE ProgramConf

(* Inovactions within a tangle are required to execute tangled instruction concurrently, examples or opGroup operations and opControlBarrier  *)
TangledInstructionSet == {"OpControlBarrier, OpGroupAll", "OpGroupAny", "OpGroupNonUniformAll", "OpGroupNonUniformAny"}
MergedInstructionSet == {"OpLoopMerge", "OpSelectionMerge"}
BlockTerminationInstructionSet == {"OpBranch", "OpBranchConditional", "OpSwitch", "Terminate"}
BranchInstructionSet == {"OpBranch", "OpBranchConditional", "OpSwitch"}
ConstructTypeSet == {"Selection", "Loop", "Switch", "Continue", "Case"}
\* Tangle: 
Tangle(ts) == 
    [threads |-> ts]


\* Block: A contiguous sequence of instructions starting with an OpLabel, ending with a block termination instruction. 
\* A block has no additional label or block termination instructions.
\* block termination instruction: OpBranch, OpBranchConditional, Terminate
\* OpLabel is define as a variable thatGeneratePaths has pc as its value field and its opLabel as its name field
Block(opLabel, terminatedInstr, tangle, merge, initialized, constructType, mergeBlock, continueBlock, caseBlocks) == 
    [opLabelIdx |-> opLabel,
    terminatedInstrIdx |-> terminatedInstr,
    tangle |-> tangle,
    merge |-> merge,
    initialized |-> initialized,
    constructType |-> constructType,
    mergeBlock |-> mergeBlock,
    continueBlock |-> continueBlock,
    caseBlocks |-> caseBlocks]

\* GenerateCFG(blocks, branch) == 
\*     [node |-> blocks,
\*     edge |-> branch]

\* make non-order-sensitive sequence becomes enumerable
SeqToSet(seq) == { seq[i]: i \in 1..Len(seq) }

\* update the sequence of sets
newSeqOfSets(seq, idx, newSet) == [seq EXCEPT ![idx] = newSet]

\* BoundedSeq: return a set of all sequences of length at most n, this helps to make the sequence enumerable
BoundedSeq(S, N) == UNION { [1..n -> S]: n \in 0..N}


\* helper function to extract the OpLabel field from the block
ExtractOpLabelIdxSet(blocks) ==
    {blocks[blockIdx].opLabelIdx : blockIdx \in 1..Len(blocks)}

        

\* mergeBlock is the current merge block,
\* return header block for current merge block
FindHeaderBlock(blocks, mBlock) == 
    CHOOSE block \in SeqToSet(blocks) : mBlock.opLabelIdx = block.mergeBlock

\* (* Helper function to find the block that starts with the given name to OpLabel *)
\* FindBlockbyOpLabel(blocks, name) == 
\*     CHOOSE k \in 1..Len(blocks) : \E j \in 1..Len(ThreadInstructions[1]) : ThreadInstructions[1][j] = "OpLabel" /\ GetVal(ThreadArguments[1][blocks[k].opLabelIdx]) = j

(* Helper function to find the block that starts with the given index to OpLabel *)
FindBlockbyOpLabelIdx(blocks, index) == 
    CHOOSE block \in SeqToSet(blocks): block.opLabelIdx = index

(* Helper function to find the block that ends with the given index to termination instruction *)
FindBlockByTerminationIns(blocks, index) == 
    CHOOSE block \in SeqToSet(blocks): block.terminatedInstrIdx = index

GetSwitchTargets(block) ==
    LET
        switchInstrIdx == block.terminatedInstrIdx
        switchTargets == {GetVal(-1, ThreadArguments[1][switchInstrIdx][i]) : i \in 2..Len(ThreadArguments[1][switchInstrIdx])}
    IN
        switchTargets
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

IsHeaderBlock(block) ==
    block.mergeBlock # -1

IsLoopHeaderBlock(block) ==
    /\ IsHeaderBlock(block)
    /\ block.constructType = "Loop"

IsContinueBlockOf(currentBlock, headerBlock) ==
    /\ IsLoopHeaderBlock(headerBlock)
    /\ IsMergeBlock(currentBlock)
    /\ headerBlock.continueBlock = currentBlock.opLabelIdx

IsExitBlock(block) ==
  IsTerminationInstruction(block.terminatedInstrIdx)
(* Helper function to find the block that contains the given index *)
FindCurrentBlock(blocks, index) == 
    CHOOSE block \in SeqToSet(blocks): block.opLabelIdx <= index /\ block.terminatedInstrIdx >= index

\* IndexOfNode(nodeId) ==
\*   CHOOSE i \in 1..Len(Blocks) : Blocks[i].opLabelIdx = nodeId


\* FindBackEdge(cfg, target) == 
\*     CHOOSE edge \in CFGEdges : edge[2] = target.opLabelIdx /\ edge[1] > target.opLabelIdx

\* IsBackEdge(node, target) ==
\*     IF  node.opLabelIdx > target.opLabelIdx THEN \* target is before current node (back edge)
\*         FALSE
\*     ELSE 
\*         /\  IsHeaderBlock(target)  \* target block is a header block
\*         /\  target.continueBlock = node.opLabelIdx \* target merge instruction is OpLoopMerge


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
\* RECURSIVE DFS(_, _, _, _, _)
\* DFS(node, cfg, visited, finished, backEdges) ==
\*     LET
\*         newVisited == visited \union {node}
\*         successors == {n \in ExtractOpLabelIdxSet(Blocks) : <<node, n>> \in CFGEdges}
\*         newBackEdges == 
\*             LET
\*                 newLoopEdges == 
\*                     {<<node, s>> : s \in visited} \cap 
\*                     {<<node, s>> : s \in successors}
\*             IN
\*             backEdges \union {edge \in newLoopEdges: edge[2] \notin finished}
\*     IN
\*     IF node \in finished THEN
\*         [visited |-> visited, finished |-> finished, backEdges |-> backEdges]
\*     ELSE IF \A s \in successors : s \in visited
\*     THEN 
\*         [visited |-> newVisited, 
\*          finished |-> finished \union {node}, 
\*          backEdges |-> newBackEdges]
\*     ELSE
\*         LET
\*             unvisitedSuccs == {s \in successors : s \notin visited}
\*             RECURSIVE DFSAll(_, _, _, _)
\*             DFSAll(nodes, v, f, b) ==
\*                 IF nodes = {} THEN [visited |-> v, finished |-> f, backEdges |-> b]
\*                 ELSE
\*                     LET 
\*                         next == CHOOSE n \in nodes : TRUE
\*                         result == DFS(next, cfg, v, f, b)
\*                     IN
\*                     DFSAll(nodes \ {next}, result.visited, result.finished, result.backEdges)
\*         IN
\*         LET
\*             result == DFSAll(unvisitedSuccs, newVisited, finished, newBackEdges)
\*         IN
\*         [visited |-> result.visited, 
\*          finished |-> result.finished \union {node}, 
\*          backEdges |-> result.backEdges]

\* Given a CFG, identify all the back edges in the CFG
\* Node is the index to the opLabel
\* IdentifyLoops(cfg) ==
\*     LET
\*         startNode == EntryLabel \* Start from the entry block
\*         result == DFS(startNode, cfg, {}, {}, {})
\*     IN
\*     result.backEdges

\* RECURSIVE LoopNestingDepth(_, _, _, _)
\* LoopNestingDepth(node, cfg, loops, visited) ==
\*     LET
\*         successors == {n \in ExtractOpLabelIdxSet(Blocks) : <<node, n>> \in CFGEdges}
\*         loopEdges == {e \in loops : e[2] = node}
\*     IN
\*     IF node \in visited THEN 0  \* Prevent infinite recursion on cycles
\*     ELSE IF loopEdges = {} THEN 0
\*     ELSE 1 + Max({LoopNestingDepth(e[1], cfg, loops \ {e}, visited \union {node}) : e \in loopEdges})

\* MaxLoopNestingDepth(cfg) ==
\*     LET 
\*         loops == IdentifyLoops(cfg)
\*     IN
\*     Max({LoopNestingDepth(n, cfg, loops, {}) : n \in ExtractOpLabelIdxSet(Blocks)})


\* SuggestedPathLength(cfg) ==
\*     LET
\*         loopDepth == MaxLoopNestingDepth(cfg)
\*         nodeCount == Cardinality(DOMAIN Blocks)
\*     IN
\*         nodeCount * (2 ^ loopDepth)


(* Helper function to handle back edges *)
\* BackEdgeCheck(node, target, cfg, activeHeaders, loopStack) ==
\*   \* If the target is a loop header, ensure that the loop header is still in the stack
\*   IF IsBackEdge(node, target) THEN
\*     \* /\ target \in activeHeaders  \* Ensure loop header is still active
\*     /\ \E i \in 1..Len(loopStack) : loopStack[i] = target.opLabelIdx
\*   ELSE
\*     TRUE


(* Note: currently GeneratePaths function is not used as it severely affects the performance when length is long *)
\* RECURSIVE GeneratePaths(_, _, _, _)
\* GeneratePaths(node, cfg, length, visitedLoopHeader) ==
\*   IF length = 0 THEN
\*     {<<node.opLabelIdx>>}
\*   ELSE 
\*     LET
\*     \* We do not want to visit the same loop header twice via a back edge
\*     \* So whenever we visit a continue block, we add the corresponding header block to the visited set
\*      newVisitedLoopHeader == 
\*         IF IsMergeBlock(node) = TRUE THEN
\*             LET headerBlock == FindHeaderBlock(node) IN
\*                 IF IsContinueBlockOf(node, headerBlock) THEN
\*                      visitedLoopHeader \union {headerBlock.opLabelIdx}
\*                 ELSE
\*                      visitedLoopHeader
\*         ELSE 
\*             visitedLoopHeader
\*       successors == {n \in SeqToSet(Blocks) : <<node.opLabelIdx, n.opLabelIdx>> \in CFGEdges}
\*       \* we only allow visited node to be visited again if we are in a loop
\*       filteredSuccessors == {
\*           s \in successors :
\*             \* Doing so we can gaurentee that we are not going to visit the back edge twice
\*             /\ s.opLabelIdx \notin visitedLoopHeader
\*       }
\*       subpaths == UNION {GeneratePaths(s, cfg, length - 1, newVisitedLoopHeader) : s \in filteredSuccessors}
\*       result == {<<node.opLabelIdx>> \o path : path \in subpaths}
\*     IN
\*       result

\* ValidPaths(startNode, cfg, maxPathLength) == 
\*     UNION {GeneratePaths(startNode, cfg, len, {}) : len \in 1..maxPathLength}



\* Successors(n) == { m \in ExtractOpLabelIdxSet(Blocks) : <<n, m>> \in CFGEdges }
\* Predecessors(n) == { m \in ExtractOpLabelIdxSet(Blocks) : <<m, n>> \in CFGEdges }

\* RECURSIVE Reachable(_, _, _)

\* Reachable(currentNode, targetNode, visited) ==
\*   IF currentNode = targetNode THEN
\*     TRUE
\*   ELSE IF currentNode \in visited THEN
\*     FALSE
\*   ELSE
\*     LET
\*       newVisited == visited \cup {currentNode}
\*     IN
\*       \E n \in Successors(currentNode) : Reachable(n, targetNode, newVisited)

\* InitDom == [ n \in 1..Len(Blocks) |-> IF Blocks[n].opLabelIdx = EntryLabel THEN {EntryLabel} ELSE {} ]


\* ComputeDom(dom) ==
\*   [ n \in 1..Len(Blocks)|-> 
\*       LET
\*         nodeId == Blocks[n].opLabelIdx
\*         preds == Predecessors(nodeId)
\*         predDoms == { dom[IndexOfNode(p)] : p \in preds }
\*         interPreDoms == Inter(predDoms)
\*       IN
\*         IF preds = {}
\*         THEN 
\*             {nodeId}
\*         ELSE
\*             {nodeId} \cup interPreDoms
\*   ]

\* RECURSIVE DominationSequence(_)

\* DominationSequence(k) ==
\*     IF k = 0 THEN 
\*         InitDom
\*     ELSE
\*         ComputeDom(DominationSequence(k - 1))

\* dom == DominationSequence(Len(Blocks) + 1)

\* ComputePostDom(postDom) ==
\*   [ n \in DOMAIN Blocks |->
\*       LET
\*         succs == Successors(Blocks[n].opLabelIdx)
\*         succPostDoms == { postDom[IndexOfNode(s)] : s \in succs }
\*         interSuccPostDoms == IF succPostDoms = {} THEN {} ELSE Inter(succPostDoms)
\*       IN
\*         {Blocks[n].opLabelIdx} \cup interSuccPostDoms
\*   ]

\* RECURSIVE PostDomSequence(_)

\* PostDomSequence(k) ==
\*   IF k = 0 THEN 
\*     [n \in DOMAIN Blocks |->
\*        IF IsExitBlock(Blocks[n]) THEN {Blocks[n].opLabelIdx} ELSE DOMAIN Blocks]
\*   ELSE 
\*     ComputePostDom(PostDomSequence(k - 1))

\* postDom == PostDomSequence(Len(Blocks) + 1)


\* return a set of all paths in graph G from start block to end block
\* this should only be used as Init phase as validPath does not change during execution
\* StructuredControlFlowPaths(cfg, maxPathLength) == {
\*     p \in ValidPaths(Blocks[1], cfg, maxPathLength) :
\*         /\ p # <<>>(* p is not an empty sequence *)
\*         /\ p[1] = EntryLabel
\*         /\ p[Len(p)] = Blocks[Len(Blocks)].opLabelIdx
\*         /\ \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in CFGEdges
\*     }


\* \* fixme: maximum length of the path should be sounded.
\* StructuredControlFlowPathsTo(B) =={
\*     p \in validPaths:
\*         /\ p # <<>>(* p is not an empty sequence *)
\*         /\ \E idx \in 1..Len(p) : p[idx] = B
\*         /\ \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in CFGEdges
\*     }

\* StructuredControlFlowPathsFromTo(StartNode, B) == {
\*     p \in validPaths:
\*         /\ p # <<>>  \* p is not an empty sequence
\*         /\ \E startIdx, endIdx \in 1..Len(p) :
\*             /\ p[startIdx] = StartNode
\*             /\ p[endIdx] = B
\*             /\ startIdx < endIdx
\*         /\ \A i \in 1..(Len(p) - 1) : <<p[i], p[i+1]>> \in CFGEdges
\* }

\* StructurallyReachable(B) == Reachable(EntryLabel, B, {})

\* StructurallyReachableFrom(currentNode, targetNode) == 
\*     Reachable(currentNode, targetNode, {})


\* StructurallyReachableFrom(StartNode, B) == StructuredControlFlowPathsFromTo(StartNode, B) # {}

\* A block A structurally dominates a block B if every structured control flow path to B includes A
\* A and B are the indice to the opLabel
\* StructurallyDominates(A, B) == A \in dom[IndexOfNode(B)]
\* StructurallyDominates(A, B) == \A p \in StructuredControlFlowPathsTo(B) : \E i \in 1..Len(p) : p[i] = A
\* StructurallyPostDominates(nodeA, nodeB) ==
\*   nodeA \in postDom[IndexOfNode(nodeB)]
\* A block A strictly structurally dominates a block B if A structurally dominates B and A != B
\* A and B are the indice to the opLabel
\* StrictlyStructurallyDominates(A, B) == 
\*     /\ A # B
\*     /\ StructurallyDominates(A, B)

\* FindHeaderBlockForConstruct(blockIdx, blocks) ==
\*   CHOOSE header \in {h \in DOMAIN blocks : 
\*                      /\ Blocks[h].constructType \in ConstructTypeSet
\*                      /\ h < blockIdx
\*                      /\ StructurallyDominates(Blocks[h].opLabelIdx, Blocks[blockIdx].opLabelIdx)
\*                      /\ h # blockIdx} :
\*     TRUE

\* \* a selection construct: the blocks structurally dominated by a selection header, 
\* \* excluding blocks structurally dominated by the selection header’s merge block
\* BlocksInSelectionConstruct(headerIdx, blocks) ==
\*   LET
\*     mergeBlockIdx == blocks[headerIdx].mergeBlock
\*     dominatedBlocks == {b \in SeqToSet(blocks) : StructurallyDominates(blocks[headerIdx].opLabelIdx, b.opLabelIdx)}
\*     mergeDominatedBlocks == {b \in SeqToSet(blocks) : StructurallyDominates(mergeBlockIdx, b.opLabelIdx)}
\*   IN
\*     (dominatedBlocks \ {blocks[headerIdx]}) \ mergeDominatedBlocks


\* \* a continue construct: the blocks that are both structurally dominated by an OpLoopMerge Continue Target 
\* \* and structurally post dominated by the corresponding loop’s back-edge block
\* BlocksInContinueConstruct(loopHeaderIdx, blocks) ==
\*   LET
\*     continueTargetIdx == blocks[loopHeaderIdx].continueBlock
\*     backEdgeBlockIdx == FindBackEdge(CFG, blocks[loopHeaderIdx])
\*     dominatedBlocks == {b \in SeqToSet(blocks) : StructurallyDominates(continueTargetIdx, b.opLabelIdx)}
\*     postDominatedBlocks == {b \in SeqToSet(blocks) : StructurallyPostDominates(backEdgeBlockIdx, b.opLabelIdx)}
\*   IN
\*     dominatedBlocks \intersect postDominatedBlocks

\* \* a loop construct: the blocks structurally dominated by a loop header, '
\* \* excluding both the loop header’s continue construct and the blocks structurally dominated by the loop header’s merge block
\* BlocksInLoopConstruct(headerIdx, blocks) ==
\*   LET
\*     continueConstructBlocks == BlocksInContinueConstruct(headerIdx, blocks)
\*     mergeBlockIdx == blocks[headerIdx].mergeBlock
\*     dominatedBlocks == {b \in SeqToSet(blocks) : StructurallyDominates(blocks[headerIdx].opLabelIdx, b.opLabelIdx)}
\*     mergeDominatedBlocks == {b \in SeqToSet(blocks) : StructurallyDominates(mergeBlockIdx, b.opLabelIdx)}
\*   IN
\*     (dominatedBlocks \ {blocks[headerIdx]}) \ (continueConstructBlocks \union  mergeDominatedBlocks)

\* BlocksInCaseConstruct(caseBlockIdx, switchHeader, blocks) ==
\*   LET
\*     mergeBlock == blocks[switchHeader].mergeBlock
\*     dominatedBlocks == {b \in  SeqToSet(blocks): StructurallyDominates(caseBlockIdx, b.opLabelIdx)}
\*     mergeDominatedBlocks == {b \in SeqToSet(blocks) : StructurallyDominates(mergeBlock, b.opLabelIdx)}
\*   IN
\*     (dominatedBlocks \ {caseBlockIdx}) \ mergeDominatedBlocks


\* \* a switch construct: the blocks structurally dominated by a switch header,
\* \* excluding blocks structurally dominated by the switch header’s merge block
\* BlocksInSwitchConstruct(headerIdx, blocks) ==
\*   LET
\*     mergeBlockIdx == blocks[headerIdx].mergeBlock
\*     dominatedBlocks == {b \in SeqToSet(blocks) : StructurallyDominates(blocks[headerIdx].opLabelIdx, b.opLabelIdx)}
\*     mergeDominatedBlocks == {b \in SeqToSet(blocks) : StructurallyDominates(mergeBlockIdx, b.opLabelIdx)}
\*   IN
\*     (dominatedBlocks \ {blocks[headerIdx]}) \ mergeDominatedBlocks    

\* find blocks witihin the same construct, if current block does not belong to any construct, return itself instead
\* This function is useful because it helps to determine the blocks that are being affeced by the change of tangle of current block
BlocksInSameConstruct(blockIdx) ==
    IF \e c \in ControlFlowConstructs : blockIdx \in c.blocks
    THEN
        c.blocks
    ELSE
        {blockIdx}

\* BlocksInSameConstruct(blockIdx, blocks) ==
\*   LET headerIdx == FindHeaderBlockForConstruct(blockIdx, blocks)
\*       constructType == blocks[headerIdx].constructType
\*   IN
\*     IF headerIdx = -1 THEN {blockIdx}  \* no header found, it is not part of any construct
\*     ELSE
\*         CASE constructType = "Selection" -> BlocksInSelectionConstruct(headerIdx, blocks)
\*             [] constructType = "Loop" -> BlocksInLoopConstruct(headerIdx, blocks)
\*             [] constructType = "Switch" -> 
\*             \* If the block is the switch header or dominated by the header, it's in the switch construct
\*                 IF StructurallyDominates(headerIdx, blockIdx) THEN
\*                     BlocksInSwitchConstruct(headerIdx, blocks)
\*                 ELSE
\*                     \* The block might be part of a specific case construct
\*                     LET caseBlockIdx == CHOOSE case \in GetSwitchTargets(blocks[headerIdx]) :
\*                                 StructurallyDominates(case, blockIdx)
\*                     IN
\*                         BlocksInCaseConstruct(caseBlockIdx, headerIdx, blocks)
\*             [] constructType = "Continue" -> BlocksInContinueConstruct(headerIdx, blocks)
\*             [] OTHER -> {}

\* Generate blocks from the instructions
\* GenerateBlocks(insts) == 
\*   [i \in 1..Len(insts) |-> 
\*      IF IsOpLabel(insts[i]) THEN 
\*        LET terminationIndex == Min({j \in i+1..Len(insts) : 
\*            IsTerminationInstruction(insts[j])} \cup {Len(insts)})
\*            tangle == IF 
\*                         i = EntryLabel
\*                      THEN 
\*                         [wg \in 1..NumWorkGroups |-> ThreadsWithinWorkGroup(wg-1)] 
\*                      ELSE 
\*                         [wg \in 1..NumWorkGroups |-> {}]
\*             initialization == IF i = EntryLabel THEN [wg \in 1..NumWorkGroups |-> TRUE] ELSE [wg \in 1..NumWorkGroups |-> FALSE]
\*             constructType ==
\*                 IF ThreadInstructions[1][terminationIndex-1] = "OpSelectionMerge" THEN
\*                     IF ThreadInstructions[1][terminationIndex] = "OpBranchConditional" THEN
\*                         "Selection"
\*                     ELSE IF ThreadInstructions[1][terminationIndex] = "OpSwitch" THEN
\*                         "Switch"
\*                     ELSE
\*                         "None"
\*                 ELSE IF ThreadInstructions[1][terminationIndex-1] = "OpLoopMerge" THEN
\*                     "Loop"
\*                 ELSE 
\*                     "None"
\*             mergeBlock == 
\*                 IF IsMergedInstruction(ThreadInstructions[1][terminationIndex-1]) THEN 
\*                     GetVal(-1, ThreadArguments[1][terminationIndex-1][1])
\*                 ELSE
\*                     -1
\*             continueBlock ==
\*                 IF ThreadInstructions[1][terminationIndex-1] = "OpLoopMerge" THEN
\*                     GetVal(-1, ThreadArguments[1][terminationIndex-1][2])
\*                 ELSE
\*                     -1
\*        IN 
\*             Block(i, terminationIndex, tangle, DetermineBlockType(i), initialization, constructType, mergeBlock, continueBlock)
\*      ELSE Block(-1, <<>>, <<>>, FALSE, "None", <<>>, -1, -1, <<>>)
\*   ]


\* startIndex is the pc of the instruction(OpLabel) that starts the block
\* terminationIndex is the pc of the termination instruction that terminates the block
\* return set of indices to the OpLabel instructions
\* OpLabel is obtained from the merge instruction and branch instruction
\* FindTargetBlocks(startIndex, terminationIndex) == 
\*     LET
\*         mergeInstr == IF 
\*                         terminationIndex > startIndex 
\*                       THEN 
\*                       ThreadInstructions[1][terminationIndex - 1] 
\*                       ELSE 
\*                         <<>>
\*     IN
\*         IF mergeInstr = "OpLoopMerge" THEN
\*             {GetVal(-1, ThreadArguments[1][terminationIndex - 1][1]), 
\*                 GetVal(-1, ThreadArguments[1][terminationIndex - 1][2])} \cup 
\*                 (IF ThreadInstructions[1][terminationIndex] = "OpBranch" THEN
\*                     {GetVal(-1, ThreadArguments[1][terminationIndex][1])}
\*                 ELSE IF ThreadInstructions[1][terminationIndex] = "OpBranchConditional" THEN
\*                     {GetVal(-1, ThreadArguments[1][terminationIndex][2]), 
\*                         GetVal(-1, ThreadArguments[1][terminationIndex][3])}
\*                 ELSE
\*                     {})
\*         ELSE IF mergeInstr = "OpSelectionMerge" THEN
\*             {GetVal(-1, ThreadArguments[1][terminationIndex - 1][1])} \cup 
\*                 (IF ThreadInstructions[1][terminationIndex] = "OpBranch" THEN
\*                     {GetVal(-1, ThreadArguments[1][terminationIndex][1])}
\*                 ELSE IF ThreadInstructions[1][terminationIndex] = "OpBranchConditional" THEN
\*                     {GetVal(-1, ThreadArguments[1][terminationIndex][2]), 
\*                         GetVal(-1, ThreadArguments[1][terminationIndex][3])}
\*                 ELSE
\*                     {})
\*         ELSE 
\*             IF ThreadInstructions[1][terminationIndex] = "OpBranch" THEN
\*                 {GetVal(-1, ThreadArguments[1][terminationIndex][1])}
\*             ELSE IF ThreadInstructions[1][terminationIndex] = "OpBranchConditional" THEN
\*                 {GetVal(-1, ThreadArguments[1][terminationIndex][2]), 
\*                     GetVal(-1, ThreadArguments[1][terminationIndex][3])}
\*             ELSE
\*                 {}

                    
                    
\* startIndex is the pc of the instruction(OpLabel) that starts the block
\* terminationIndex is the pc of the termination instruction that terminates the block
\* return set of indices to the OpLabel instructions of the merge block for current header block
\* OpLabel is obtained from the merge instruction and branch instruction
\* FindMergeBlocksIdx(startIndex, terminationIndex) == 
\*     LET
\*         mergeInstr == IF terminationIndex > startIndex THEN ThreadInstructions[1][terminationIndex - 1] ELSE <<>>
\*     IN
\*         IF mergeInstr = "OpLoopMerge" THEN
\*             {GetVal(-1, ThreadArguments[1][terminationIndex - 1][1]), GetVal(-1, ThreadArguments[1][terminationIndex - 1][2])}
\*         ELSE IF mergeInstr = "OpSelectionMerge" THEN
\*             {GetVal(-1, ThreadArguments[1][terminationIndex - 1][1])}
\*         ELSE 
\*             {}


\* Rule 4: If there exists termination instruction in the block, 
\* Simply remove the thread from the tangle of all blocks as the thread has terminated.
TerminateUpdate(wgid, t, currentLabelIdx) ==
    [i \in 1..Len(Blocks) |->
        \* IF IsMergeBlock(Blocks[i]) /\ StrictlyStructurallyDominates(FindHeaderBlock(Blocks[i]).opLabelIdx, currentLabelIdx)
        IF TRUE
        THEN
            Block(Blocks[i].opLabelIdx, Blocks[i].terminatedInstrIdx, 
            newSeqOfSets(Blocks[i].tangle, wgid, Blocks[i].tangle[wgid] \{t}), 
            Blocks[i].merge, Blocks[i].initialized, Blocks[i].constructType, Blocks[i].mergeBlock, Blocks[i].continueBlock, Blocks[i].caseBlocks)
        ELSE
            Blocks[i]
    ] 

\* BranchUpdate: update the tangle of the blocks that are pointed by the branch instruction
\* tangle is the tangle that is going to be updated to the blocks, each workgroup has its own tangle
\* opLabelIdxSet is the set of indices to the opLabel instructions that are pointed by the branch instruction
\* choosenBranchIdx is the index to the opLabel instruction that is choosen by the branch instruction
BranchUpdate(wgid, t, currentBlock, tangle, opLabelIdxSet, chosenBranchIdx) ==
    LET blockIdx == CHOOSE i \in 1..Len(Blocks) : Blocks[i].opLabelIdx = currentBlock.opLabelIdx
        blocksWithinConstruct == BlocksInSameConstruct(blockIdx)
    IN 
        [i \in 1..Len(Blocks) |-> 
            IF  
                /\ Blocks[i] \in blocksWithinConstruct
            \* keep this order to avoid performance issue
            \* /\ Blocks[i].opLabelIdx <= chosenBranchIdx 
            \* /\ currentBlock.opLabelIdx # Blocks[i].opLabelIdx 
            \* /\ StructurallyReachableFrom(currentBlock.opLabelIdx, Blocks[i].opLabelIdx) 
            THEN
            \* rule 2: If a thread reaches a branch instruction, for any reachable unitialized block from current block to chosen block,
            \* update the tangle of tha block to be the same as the tangle of current block.
            \* and remove the thread itself from the tangle of unchoosen block if that block is not a merge block for current block
                IF Blocks[i].initialized[wgid] = FALSE THEN
                \* unchoosen block and is not a merge block
                    IF Blocks[i].opLabelIdx # chosenBranchIdx /\  Blocks[i].opLabelIdx # currentBlock.mergeBlock THEN
                        Block(Blocks[i].opLabelIdx, Blocks[i].terminatedInstrIdx, 
                            newSeqOfSets(Blocks[i].tangle, wgid, tangle \{t}), Blocks[i].merge, [Blocks[i].initialized EXCEPT ![wgid] = TRUE], Blocks[i].constructType, Blocks[i].mergeBlock, Blocks[i].continueBlock, Blocks[i].caseBlocks)
                    ELSE
                        Block(Blocks[i].opLabelIdx, Blocks[i].terminatedInstrIdx,
                            newSeqOfSets(Blocks[i].tangle, wgid, tangle), Blocks[i].merge, [Blocks[i].initialized EXCEPT ![wgid] = TRUE], Blocks[i].constructType, Blocks[i].mergeBlock, Blocks[i].continueBlock, Blocks[i].caseBlocks)
            \* FIXME: current scope for rule 3 is too huge as it may remove itself from further blocks, try to frame the scope within the construct
            \* rule 3: If the unchoosen block is initialized and is not a merge block for current block,
            \* remove the thread from the tangle
                ELSE IF Blocks[i].opLabelIdx # chosenBranchIdx /\ Blocks[i].opLabelIdx # currentBlock.mergeBlock /\ Blocks[i].initialized[wgid] = TRUE THEN
                    Block(Blocks[i].opLabelIdx, Blocks[i].terminatedInstrIdx,
                    newSeqOfSets(Blocks[i].tangle, wgid, Blocks[i].tangle[wgid] \{t}), Blocks[i].merge, Blocks[i].initialized, Blocks[i].constructType, Blocks[i].mergeBlock, Blocks[i].continueBlock, Blocks[i].caseBlocks)
                ELSE 
                    Blocks[i]
            ELSE 
                Blocks[i]
        ]

\* Helper function that return the updated blocks in CFG regarding the merge instruction
MergeUpdate(wgid, currentLabelIdx, tangle, opLabelIdxSet) ==
    [i \in 1..Len(Blocks) |-> 
        IF Blocks[i].opLabelIdx \in opLabelIdxSet THEN
            \* rule 1: If a thread reaches a merge instruction and the block it points to has empty tangle, 
            \* update the tangle of tha block to the tangle of the merge instruction
            IF Blocks[i].initialized[wgid] = FALSE THEN
                Block(Blocks[i].opLabelIdx, Blocks[i].terminatedInstrIdx, 
                    newSeqOfSets(Blocks[i].tangle, wgid, tangle), Blocks[i].merge, [Blocks[i].initialized EXCEPT ![wgid] = TRUE], Blocks[i].constructType, Blocks[i].mergeBlock, Blocks[i].continueBlock, Blocks[i].caseBlocks) 
            ELSE 
                Blocks[i]
        ELSE
            Blocks[i]
    ]    

\* InitCFG == 
    \* LET blocks == SelectSeq(GenerateBlocks(ThreadInstructions[1]), LAMBDA b: b.opLabelIdx # -1)
        \* Initialize constructs for selection, loop, switch, and continue constructs
        \* selectionConstructs == UNION { SelectionConstruct(i, blocks) : 
        \*                                i \in DOMAIN blocks /\ blocks[i].constructType = "Selection" }
        \* loopConstructs == UNION { LoopConstruct(i, blocks) : 
        \*                           i \in DOMAIN blocks /\ blocks[i].constructType = "Loop" }
        \* switchConstructs == UNION { SwitchConstruct(i, blocks) : 
        \*                             i \in DOMAIN blocks /\ blocks[i].constructType = "Switch" }
        \* continueConstructs == UNION { ContinueConstruct(i, blocks) : 
        \*                               i \in DOMAIN blocks /\ blocks[i].constructType = "Loop" /\ blocks[i].continueBlock # -1 }

        \* Update each block to include information about its construct membership

        \* graph == GenerateCFG(blocks, 
        \*         UNION { {<<blocks[i].opLabelIdx, target>> : 
        \*             target \in FindTargetBlocks(blocks[i].opLabelIdx, blocks[i].terminatedInstrIdx)} : i \in DOMAIN blocks }
        \*         )
        
        \* constructEdges == UNION {
        \*     \* If the block is a loop header block, add an edge from the header block to the continue block and merge block
        \*     IF blocks[i].constructType = "Loop" THEN
        \*         {<<blocks[i].opLabelIdx, blocks[i].mergeBlock>>} \cup 
        \*         (IF blocks[i].continueBlock # -1 THEN {<<blocks[i].opLabelIdx, blocks[i].continueBlock>>} ELSE {})
        \*     \* If the block is a selection header block, add an edge from the header block to the merge block
        \*     ELSE IF blocks[i].constructType = "Selection" THEN
        \*         {<<blocks[i].opLabelIdx, blocks[i].mergeBlock>>}
        \*     ELSE IF blocks[i].constructType = "Switch" THEN
        \*         LET
        \*             switcHeader == blocks[i].opLabelIdx
        \*             mergeBlock == blocks[i].mergeBlock
        \*             targets == GetSwitchTargets(blocks[i])
        \*             caseBlocks == {t \in targets: {n \in DOMAIN blocks : StructurallyDominates(t, blocks[n].opLabelIdx) /\ ~StructurallyDominates(mergeBlock, blocks[n].opLabelIdx)}}
        \*         IN 
        \*             UNION { {<<switcHeader, c>> : c \in caseBlocks} }
        \*     ELSE 
        \*         {}
        \*     : i \in DOMAIN blocks
        \* }
    \* IN 
    \*     /\  LET maxPathLength == SuggestedPathLength(graph) 
    \*         IN
    \*             /\  CFG = graph
    \*             /\  MaxPathLength = maxPathLength
    \*             /\  validPaths = {}\*StructuredControlFlowPaths(graph, maxPathLength)


(* Global Variables *)

InitProgram ==
    /\ InitBlocks
    \* /\ InitCFG
    /\ InitGPU

====



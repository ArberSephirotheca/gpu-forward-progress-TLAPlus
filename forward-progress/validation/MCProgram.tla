---- MODULE MCProgram ----
LOCAL INSTANCE Integers
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE FiniteSets
\* LOCAL INSTANCE MCLayout
LOCAL INSTANCE TLC

VARIABLES globalVars, threadLocals, state, DynamicNodeSet
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

Push(seq, x) ==
    Append(seq, x)

\* For simplicity we can pop an empty stack
\* Which will be a noop
Pop(seq) == 
  SubSeq(seq, 1, Len(seq)-1)


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
ThreadsWithinWorkGroupNonTerminated(wgid) ==  {tid \in Threads : WorkGroupId(tid) = wgid /\ state[tid] # "terminated"}

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

\* order matters so we use sequence instead of set
\* currentThreadSet is the set of threads that are currently executing the block
\* executeSet is the set of blocks that have been executed by the threads
\* currentThreadSet != {} => executeSet != {}
\* executeSet = {} => currentThreadSet = {}
DynamicNode(currentThreadSet, executeSet, notExecuteSet, unknownSet, labelIdx, (*mergeStack,*) iterationVec) ==
    [
        currentThreadSet |-> currentThreadSet,
        executeSet |-> executeSet,
        notExecuteSet |-> notExecuteSet,
        unknownSet |-> unknownSet,
        labelIdx |-> labelIdx,
        \* mergeStack |-> mergeStack,
        iterationVec |-> iterationVec
    ]


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


\* it is only possible for a thread to be in one DB at a time
CurrentDynamicNode(wgid, tid) ==
    CHOOSE DB \in DynamicNodeSet : tid \in DB.currentThreadSet[wgid]

FindDB(labelIdx) ==
    CHOOSE DB \in DynamicNodeSet : DB.labelIdx = labelIdx

IsMergeBlockOfLoop(blockIdx) ==
    /\ \E construct \in ControlFlowConstructs : construct.constructType = "Loop" /\ construct.mergeBlock = blockIdx

IsBlockWithinLoop(blockIdx) ==
    LET matchingConstructs == {c \in ControlFlowConstructs : blockIdx \in c.blocks}
    IN
        /\ matchingConstructs # {}
        /\ \E c \in matchingConstructs : c.constructType = "Loop" 
\* find blocks witihin the same construct, if current block does not belong to any construct, return itself instead
\* blockIdx is the opLabel index of the block
\* This function is useful because it helps to determine the blocks that are being affeced by the change of tangle of current block
BlocksInSameConstruct(blockIdx) ==
    LET matchingConstructs == {c \in ControlFlowConstructs : blockIdx \in c.blocks}
    IN 
        IF matchingConstructs # {}
        THEN 
            UNION {c.blocks : c \in matchingConstructs}
        ELSE 
            {blockIdx}

                
Iteration(blockIdx, iter) == 
    [blockIdx |-> blockIdx,
     iter |-> iter]

FindIteration(blockIdx, iterationsVec, tid) ==
    \* LET iterSet ==
    \*     {iter \in DOMAIN iterationsVec : iterationsVec[iter].blockIdx = blockIdx}
    \* IN
    \*     IF iterSet # {} 
    \*     THEN
    \*         LET idx == CHOOSE iter \in iterSet : TRUE
    \*             IN
    \*                 iterationsVec[idx]
    \*     ELSE
    \*         Iteration(blockIdx, 0)
    IF Len(iterationsVec) = 0
    THEN
        Iteration(blockIdx, 0)
    ELSE IF iterationsVec[Len(iterationsVec)].blockIdx = blockIdx
    THEN
        iterationsVec[Len(iterationsVec)]
    ELSE
        Iteration(blockIdx, 0)

SameIterationVector(left, right) ==
    /\ Len(left) = Len(right)
    /\ \A idx \in 1..Len(left):
        /\ left[idx].blockIdx = right[idx].blockIdx
        /\ left[idx].iter = right[idx].iter

CanMergeSameIterationVector(curr, remaining) ==
    \E idx \in 1..Len(remaining):
        SameIterationVector(curr, remaining[idx])

\* 1. Push the merge block to the merge stack of current DB.
\* 2. Update the iteration vector of current DB for current thread.
LoopMergeUpdate(wgid, t, currentLabelIdx, mergeBlock) ==
    LET

        currentDB == CurrentDynamicNode(wgid, t)
        \* updatedThreadMergeStack == Push(currentDB.mergeStack[t], mergeBlock)
        currentIteration == FindIteration(currentLabelIdx, currentDB.iterationVec[t], t)
        \* if new iteration is created, we need to add it to the iteration vector
        \* otherwise we just need to increment the iteration number of top element of the iteration vector
        updatedThreadIterationVec == IF currentIteration.iter = 0
        THEN 
            Push(currentDB.iterationVec[t], Iteration(currentLabelIdx, 1))
        ELSE 
            [currentDB.iterationVec[t] EXCEPT ![Len(currentDB.iterationVec[t])] = Iteration(currentIteration.blockIdx, currentIteration.iter + 1)]
        hasExistingBlock == \E DB \in DynamicNodeSet : DB.labelIdx = currentLabelIdx /\ CanMergeSameIterationVector(updatedThreadIterationVec, DB.iterationVec)
        filterDynamicNode == {DB \in DynamicNodeSet : t \notin DB.currentThreadSet[wgid]}
    IN
        \* if we has existing block with the same iteration vector, we need to merge the current block with the existing block
        IF hasExistingBlock THEN
            {
                IF DB.labelIdx = currentLabelIdx /\ CanMergeSameIterationVector(updatedThreadIterationVec, DB.iterationVec)
                THEN
                    DynamicNode([DB.currentThreadSet EXCEPT ![wgid] = DB.currentThreadSet[wgid] \union {t}],
                    [DB.executeSet EXCEPT ![wgid] = DB.executeSet[wgid] \union {t}],
                    [DB.notExecuteSet EXCEPT ![wgid] = DB.notExecuteSet[wgid] \ {t}],
                    [DB.unknownSet EXCEPT ![wgid] = DB.unknownSet[wgid] \ {t}],
                    DB.labelIdx,
                    \* [DB.mergeStack EXCEPT ![t] = updatedThreadMergeStack],
                    [DB.iterationVec EXCEPT ![t] = updatedThreadIterationVec])
                ELSE 
                    DB
                : DB \in filterDynamicNode
                }
        ELSE
        filterDynamicNode
        \union 
        (
             { DynamicNode(currentDB.currentThreadSet,
                        currentDB.executeSet,
                        currentDB.notExecuteSet,
                        currentDB.unknownSet,
                        currentLabelIdx,
                        \* currentDB.mergeStack,
                        [currentDB.iterationVec EXCEPT ![t] = updatedThreadIterationVec])
            }
        )
        \* {
        \*     IF t \in DB.currentThreadSet[wgid] THEN
        \*       DynamicNode(currentDB.currentThreadSet,
        \*                 currentDB.executeSet,
        \*                 currentDB.notExecuteSet,
        \*                 currentDB.unknownSet,
        \*                 currentLabelIdx,
        \*                 \* currentDB.mergeStack,
        \*                 [currentDB.iterationVec EXCEPT ![t] = updatedThreadIterationVec])
            
        \*     ELSE 
        \*         DB
        \*     : DB \in DynamicNodeSet
        \* }
\* each time there is a divergent, we have following situation:
\* header block:
\* 1. do nothing as already hanlded in MergeUpdate
\* merge block:
\* 1. We need to pop the block from the merge stack of generated dynamic node.
\* 2. merge the current exeuction set and not execution set with other dynamic nodes with same unique id.
\* 3. update the unknown set after merge to ensure that we don't have any thread in the unknown set that is in execution set or not execution set
\* continue block:
\* normal block:
\* do nothing
\* Update behaivior across all type of blocks:
\* 1. remove current thread from currentThreadSet of the current DB
\* 2. Add current thread to the execution set of the new DB for true branch
\* 3. Add current thread to the notExecuteSet of the new DB for false branch
\* 4. Update the unknown set of the new DB to ensure that we don't have any thread in the unknown set that is in execution set or not execution set
BranchUpdate(wgid, t, pc, opLabelIdxSet, chosenBranchIdx) ==
    LET
        currentDB == CurrentDynamicNode(wgid, t)
        falseLabelIdxSet == opLabelIdxSet \ {chosenBranchIdx}
        newFalseLabelIdxSet == {
            falselabelIdx \in falseLabelIdxSet: (\E DB \in DynamicNodeSet: DB.labelIdx = falselabelIdx /\ SameIterationVector(DB.iterationVec, currentDB.iterationVec))
        }
        labelIdxSet == {DB.labelIdx : DB \in DynamicNodeSet}
        choosenBlock == FindBlockbyOpLabelIdx(Blocks, chosenBranchIdx)
        currentBlock == FindBlockbyOpLabelIdx(Blocks, currentDB.labelIdx)
        currentIteration == FindIteration(currentDB.labelIdx, currentDB.iterationVec[t], t)
        \* if new iteration is created, we need to add it to the iteration vector
        \* otherwise we just need to increment the iteration number of top element of the iteration vector
        updatedThreadIterationVec == IF currentIteration.iter = 0
        THEN 
            Push(currentDB.iterationVec, Iteration(currentDB.labelIdx, 1))
        ELSE 
            [currentDB.iterationVec EXCEPT ![Len(currentDB.iterationVec[t])] = Iteration(currentIteration.blockIdx, currentIteration.iter + 1)]
        isLoopHeader == IsLoopHeaderBlock(currentBlock)
        loopBranchIdx == IF isLoopHeader THEN
            ThreadArguments[t][pc-1][1].value
        ELSE
            -1
    IN  
        \* update the existing dynamic blocks
        {
            \* Encounter current DB, remove current thread set from current DB as it creates/moves to a new DB
            \* We could derive unique id from the combination of labelIdx and iterationVec
            IF DB.labelIdx = currentDB.labelIdx /\ SameIterationVector(DB.iterationVec, currentDB.iterationVec) THEN
                DynamicNode([DB.currentThreadSet EXCEPT ![wgid] = DB.currentThreadSet[wgid] \ {t}],
                    DB.executeSet,
                    DB.notExecuteSet,
                    DB.unknownSet,
                    DB.labelIdx,
                    \* DB.mergeStack,
                    DB.iterationVec)
            \* Encounter the block that is choosen by the branch instruction
            \* Check if the choosen block is the merge block 
            \* If the choosen block is a merge block, we need to:
                    \* 1. pop the merge block of current thread from the merge stack of that DB
                    \* 2. Merge the current execution set and not execution set with other dynamic nodes with same unique id.
                    \* 3. Remove the unknown set after merge to ensure that we don't have any thread in the unknown set that is in execution set or not execution set
            \* If it is a merge block of a loop (e.g. thread exit the loop), we also need to :
                \* Pop the iterationation vector of current thread from the iteration vector of that DB
            \* add current thread to the new DB,
            \* add current thread to the executeSet of the new DB
            \* remove current thread from the unknownSet of the new DB
            \* The if condition:
                \* 1. the merge block has the same OpLabel index as the choosen branch.
                \* 2. The iteration vector of the current thread is the same as the iteration vector of the DB
            \* This condition is sound because when merge block is wthin the loop, we must ensure that it is the same iteration so we can merge.
            \* If the merge block is not within the loop, the iteration vector is always the same (empty).
            ELSE IF DB.labelIdx = chosenBranchIdx THEN
                \*merge block of a loop header (exit the loop)
                IF IsMergeBlock(choosenBlock) /\ IsMergeBlockOfLoop(chosenBranchIdx) /\ SameIterationVector(DB.iterationVec, Pop(currentDB.iterationVec)) THEN 
                    DynamicNode([DB.currentThreadSet EXCEPT ![wgid] = DB.currentThreadSet[wgid] \union {t}],
                        [DB.executeSet EXCEPT ![wgid] = DB.executeSet[wgid] \union {t}],
                        DB.notExecuteSet,
                        [DB.unknownSet EXCEPT ![wgid] = DB.unknownSet[wgid] \ {t}],
                        DB.labelIdx,
                        \* [DB.mergeStack EXCEPT ![t] = Pop(DB.mergeStack[t])],
                        DB.iterationVec)
                \* if the choosen branch index is the branch to the loop body
                ELSE IF DB.labelIdx = loopBranchIdx /\ SameIterationVector(DB.iterationVec, updatedThreadIterationVec) THEN
                    DynamicNode([DB.currentThreadSet EXCEPT ![wgid] = DB.currentThreadSet[wgid] \union {t}],
                        [DB.executeSet EXCEPT ![wgid] = DB.executeSet[wgid] \union {t}],
                        DB.notExecuteSet,
                        [DB.unknownSet EXCEPT ![wgid] = DB.unknownSet[wgid] \ {t}],
                        DB.labelIdx,
                        \* [DB.mergeStack EXCEPT ![t] = Pop(DB.mergeStack[t])],
                        DB.iterationVec)
                ELSE IF SameIterationVector(DB.iterationVec, currentDB.iterationVec) THEN 
                    DynamicNode([DB.currentThreadSet EXCEPT ![wgid] = DB.currentThreadSet[wgid] \union {t}],
                        [DB.executeSet EXCEPT ![wgid] = DB.executeSet[wgid] \union {t}],
                        DB.notExecuteSet,
                        [DB.unknownSet EXCEPT ![wgid] = DB.unknownSet[wgid] \ {t}],
                        DB.labelIdx,
                        \* [DB.mergeStack EXCEPT ![t] = Pop(DB.mergeStack[t])],
                        DB.iterationVec)
                ELSE
                    DB
            \* Encounter the block that is not choosen by the branch instruction
            \* add current thread to the notExecuteSet of the new DB
            \* remove current thread from the unknownSet of the new DB
            ELSE IF DB.labelIdx \in falseLabelIdxSet 
                /\ ((IsMergeBlockOfLoop(DB.labelIdx) /\ SameIterationVector(DB.iterationVec, Pop(currentDB.iterationVec)))
                    \/ (DB.labelIdx = loopBranchIdx /\ SameIterationVector(DB.iterationVec, updatedThreadIterationVec))
                    \/ (IsMergeBlock(FindBlockbyOpLabelIdx(Blocks, DB.labelIdx)) /\ SameIterationVector(DB.iterationVec, currentDB.iterationVec))
                    )
            THEN
                DynamicNode(DB.currentThreadSet,
                    DB.executeSet,
                    [DB.notExecuteSet EXCEPT ![wgid] = DB.notExecuteSet[wgid] \union {t}],
                    [DB.unknownSet EXCEPT ![wgid] = DB.unknownSet[wgid] \ {t}],
                    DB.labelIdx,
                    \* DB.mergeStack,
                    DB.iterationVec)
            ELSE
                DB
            : DB \in DynamicNodeSet
        }
        \* union with the new true branch DB if does not exist
        \union
        (
            IF \E DB \in DynamicNodeSet: 
                \/  (DB.labelIdx = chosenBranchIdx /\ SameIterationVector(DB.iterationVec, currentDB.iterationVec)) 
                \/  (IsMergeBlock(choosenBlock) /\ IsMergeBlockOfLoop(chosenBranchIdx) /\ SameIterationVector(DB.iterationVec, Pop(currentDB.iterationVec)))
                \/  (DB.labelIdx = loopBranchIdx /\ SameIterationVector(DB.iterationVec, updatedThreadIterationVec))
            THEN 
                {} 
            ELSE
                \* if the choosen block is a merge block of a loop, we need to pop the iteration vector of current thread from the iteration vector of that DB
                IF IsMergeBlockOfLoop(chosenBranchIdx) THEN 
                    {
                        DynamicNode([wg \in 1..NumWorkGroups |-> IF wg = wgid THEN {t} ELSE {}],
                                    [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN {t} ELSE {}],
                                    [wg \in 1..NumWorkGroups |-> {}],
                                    [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN ThreadsWithinWorkGroupNonTerminated(wgid-1) \ {t}  ELSE ThreadsWithinWorkGroupNonTerminated(wg-1)],
                                    chosenBranchIdx,
                                    \* currentDB.mergeStack,
                                    \* [currentDB.iterationVec EXCEPT ![t] = Pop(currentDB.iterationVec)]
                                    Pop(currentDB.iterationVec)
                                    )
                    }
                \* if the chosen block is a new block for loop body, we need to update the iteration vector. 
                ELSE IF chosenBranchIdx = loopBranchIdx THEN
                    {
                        DynamicNode([wg \in 1..NumWorkGroups |-> IF wg = wgid THEN {t} ELSE {}],
                                    [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN {t} ELSE {}],
                                    [wg \in 1..NumWorkGroups |-> {}],
                                    [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN ThreadsWithinWorkGroupNonTerminated(wgid-1) \ {t}  ELSE ThreadsWithinWorkGroupNonTerminated(wg-1)],
                                    chosenBranchIdx,
                                    \* currentDB.mergeStack,
                                    updatedThreadIterationVec)
                    }
                ELSE
                    {
                        DynamicNode([wg \in 1..NumWorkGroups |-> IF wg = wgid THEN {t} ELSE {}],
                                    [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN {t} ELSE {}],
                                    [wg \in 1..NumWorkGroups |-> {}],
                                    [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN ThreadsWithinWorkGroupNonTerminated(wgid-1) \ {t}  ELSE ThreadsWithinWorkGroupNonTerminated(wg-1)],
                                    chosenBranchIdx,
                                    \* currentDB.mergeStack,
                                    currentDB.iterationVec)
                    }
        )
        \* union with the new false branch DB if does not exist
        \union
        (
        {
            IF IsMergeBlockOfLoop(falselabelIdx) THEN 
                DynamicNode([wg \in 1..NumWorkGroups |-> {}], \* currently no thread is executing the false block
                            [wg \in 1..NumWorkGroups |-> {}], \* currently no thread has executed the false block
                            \* current thread is not executed in the false block, but we don't know if the threads executed in precedessor DB will execute the block or not
                            [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN {t} ELSE {}],
                            \* we don't know if the threads executed in precedessor DB will execute the block or not
                            [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN ThreadsWithinWorkGroupNonTerminated(wgid-1) \ {t}  ELSE ThreadsWithinWorkGroupNonTerminated(wg-1)],
                            falselabelIdx,
                            \* currentDB.mergeStack,
                            Pop(currentDB.iterationVec))
            ELSE IF falselabelIdx = loopBranchIdx THEN
                DynamicNode([wg \in 1..NumWorkGroups |-> {}], \* currently no thread is executing the false block
                            [wg \in 1..NumWorkGroups |-> {}], \* currently no thread has executed the false block
                            \* current thread is not executed in the false block, but we don't know if the threads executed in precedessor DB will execute the block or not
                            [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN {t} ELSE {}],
                            \* we don't know if the threads executed in precedessor DB will execute the block or not
                            [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN ThreadsWithinWorkGroupNonTerminated(wgid-1) \ {t}  ELSE ThreadsWithinWorkGroupNonTerminated(wg-1)],
                            falselabelIdx,
                            \* currentDB.mergeStack,
                            updatedThreadIterationVec)
            ELSE 
                DynamicNode([wg \in 1..NumWorkGroups |-> {}], \* currently no thread is executing the false block
                            [wg \in 1..NumWorkGroups |-> {}], \* currently no thread has executed the false block
                            \* current thread is not executed in the false block, but we don't know if the threads executed in precedessor DB will execute the block or not
                            [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN {t} ELSE {}],
                            \* we don't know if the threads executed in precedessor DB will execute the block or not
                            [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN ThreadsWithinWorkGroupNonTerminated(wgid-1) \ {t}  ELSE ThreadsWithinWorkGroupNonTerminated(wg-1)],
                            falselabelIdx,
                            \* currentDB.mergeStack,
                            currentDB.iterationVec)
            : falselabelIdx \in newFalseLabelIdxSet
        }
        )

TerminateUpdate(wgid, t) ==
    {
        DynamicNode([DB.currentThreadSet EXCEPT ![wgid] = DB.currentThreadSet[wgid] \ {t}],
            [DB.executeSet EXCEPT ![wgid] = DB.executeSet[wgid] \ {t}],
            [DB.notExecuteSet EXCEPT ![wgid] = DB.notExecuteSet[wgid] \union {t}],
            [DB.unknownSet EXCEPT ![wgid] = DB.unknownSet[wgid] \ {t}],
            DB.labelIdx,
            \* DB.mergeStack,
            DB.iterationVec)
        : DB \in DynamicNodeSet
    }

(* Global Variables *)

InitProgram ==
    /\ InitDB
    /\ InitGPU

\* Invariant: Each thread belongs to exactly one DB
ThreadBelongsExactlyOne ==
    /\ \A t \in Threads:
        \E DB \in DynamicNodeSet:
            t \in DB.currentThreadSet[WorkGroupId(t) + 1]
    /\ \A t1, t2 \in Threads:
        IF WorkGroupId(t1) = WorkGroupId(t2) THEN 
            /\ \A DB1, DB2 \in DynamicNodeSet:
                (t1 \in DB1.currentThreadSet[WorkGroupId(t1) + 1] /\ t2 \in DB2.currentThreadSet[WorkGroupId(t2) + 1]) => DB1 = DB2
        ELSE
            TRUE

\* Invariant: Each dynamic execution graph has a unique block sequence
UniquelabelIdxuence ==
    \A DB1, DB2 \in DynamicNodeSet:
        DB1.labelIdx = DB2.labelIdx => DB1 = DB2
====



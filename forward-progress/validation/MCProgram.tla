---- MODULE MCProgram ----
LOCAL INSTANCE Integers
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
LOCAL INSTANCE FiniteSets
\* LOCAL INSTANCE MCLayout
LOCAL INSTANCE TLC

VARIABLES globalVars, threadLocals, state, DynamicExecutionGraphSet
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
(* Program *)


EntryLabel == Min({idx \in 1..Len(ThreadInstructions[1]) : ThreadInstructions[1][idx] = "OpLabel"})


\* order matters so we use sequence instead of set
\* currentThreadSet is the set of threads that are currently executing the block
\* executeSet is the set of blocks that have been executed by the threads
\* currentThreadSet != {} => executeSet != {}
\* executeSet = {} => currentThreadSet = {}
DynamicExecutionGraph(currentThreadSet, blockSeq, executeSet, notExecuteSet, unknownSet) ==
    [
        currentThreadSet |-> currentThreadSet,
        blockSeq |-> blockSeq,
        executeSet |-> executeSet,
        notExecuteSet |-> notExecuteSet,
        unknownSet |-> unknownSet
    ]

\* it is only possible for a thread to be in one DB at a time
CurrentDynamicExecutionGraph(wgid, tid) ==
    CHOOSE DB \in DynamicExecutionGraphSet : tid \in DB.currentThreadSet[wgid]

FindDB(blockSeq) ==
    CHOOSE DB \in DynamicExecutionGraphSet : DB.blockSeq = blockSeq

BranchUpdate(wgid, t, opLabelIdxSet, chosenBranchIdx) ==
    LET
        currentDB == CurrentDynamicExecutionGraph(wgid, t)
        updatedTrueBlockSeq == Append(currentDB.blockSeq, chosenBranchIdx)
        falseLabelIdxSet == opLabelIdxSet \ {chosenBranchIdx}
        updatedFalseBlockSeqSet == {Append(currentDB.blockSeq, idx) : idx \in falseLabelIdxSet}
        BlockSeqSet == {DB.blockSeq : DB \in DynamicExecutionGraphSet}
    IN
        {
            \* Encounter current DB, remove current thread set from current DB as it creates/moves to a new DB
            IF DB.blockSeq = currentDB.blockSeq THEN
                DynamicExecutionGraph([DB.currentThreadSet EXCEPT ![wgid] = DB.currentThreadSet[wgid] \ {t}],
                    DB.blockSeq,
                    DB.executeSet,
                    DB.notExecuteSet,
                    DB.unknownSet)
            \* Encounter the block that is choosen by the branch instruction
            \* add current thread to the new DB,
            \* add current thread to the executeSet of the new DB
            \* remove current thread from the unknownSet of the new DB
            ELSE IF DB.blockSeq = updatedTrueBlockSeq THEN
                DynamicExecutionGraph([DB.currentThreadSet EXCEPT ![wgid] = DB.currentThreadSet[wgid] \union {t}],
                    DB.blockSeq,
                    [DB.executeSet EXCEPT ![wgid] = DB.executeSet[wgid] \union {t}],
                    DB.notExecuteSet,
                    [DB.unknownSet EXCEPT ![wgid] = DB.unknownSet[wgid] \ {t}])
            \* Encounter the block that is not choosen by the branch instruction
            \* add current thread to the notExecuteSet of the new DB
            \* remove current thread from the unknownSet of the new DB
            ELSE IF DB.blockSeq \in updatedFalseBlockSeqSet THEN
                DynamicExecutionGraph(DB.currentThreadSet,
                    DB.blockSeq,
                    DB.executeSet,
                    [DB.notExecuteSet EXCEPT ![wgid] = DB.notExecuteSet[wgid] \union {t}],
                    [DB.unknownSet EXCEPT ![wgid] = DB.unknownSet[wgid] \ {t}])
            ELSE
                DB
            : DB \in DynamicExecutionGraphSet
        }
        \* union with the new true branch DB if does not exist
        \union 
            IF updatedTrueBlockSeq \in BlockSeqSet
            THEN 
                {} 
            ELSE                        
                {DynamicExecutionGraph( [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN {t} ELSE {}], \* we only add current thread to the new DB
                                        updatedTrueBlockSeq,
                                        [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN {t} ELSE {}], \* we don't know if the threads executed in precedessor DB will execute the block or not
                                        currentDB.notExecuteSet, \* but we know that the threads that are not executed in the previous block will also not execute the block
                                        \* we don't know if the threads executed in precedessor DB will execute the block or not
                                        [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN ThreadsWithinWorkGroupNonTerminated(wgid-1) \ {t}  ELSE ThreadsWithinWorkGroupNonTerminated(wg-1)])
                }
        \* union with the new false branch DB if does not exist
        \union 
        {
            IF falseBlockSeq \in BlockSeqSet
            THEN 
                {} 
            ELSE 
                DynamicExecutionGraph([wg \in 1..NumWorkGroups |-> {}], \* currently no thread is executing the false block
                                        falseBlockSeq,
                                        [wg \in 1..NumWorkGroups |-> {}], \* currently no thread has executed the false block
                                        \* current thread is not executed in the false block, but we don't know if the threads executed in precedessor DB will execute the block or not
                                        [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN {t} ELSE {}],
                                        \* we don't know if the threads executed in precedessor DB will execute the block or not
                                        [wg \in 1..NumWorkGroups |-> IF wg = wgid THEN ThreadsWithinWorkGroupNonTerminated(wgid-1) \ {t}  ELSE ThreadsWithinWorkGroupNonTerminated(wg-1)])
            : falseBlockSeq \in updatedFalseBlockSeqSet
        }

TerminateUpdate(wgid, t) ==
    {
        DynamicExecutionGraph([DB.currentThreadSet EXCEPT ![wgid] = DB.currentThreadSet[wgid] \ {t}],
            DB.blockSeq,
            [DB.executeSet EXCEPT ![wgid] = DB.executeSet[wgid] \ {t}],
            [DB.notExecuteSet EXCEPT ![wgid] = DB.notExecuteSet[wgid] \union {t}],
            [DB.unknownSet EXCEPT ![wgid] = DB.unknownSet[wgid] \ {t}])
        : DB \in DynamicExecutionGraphSet
    }


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
Block(opLabel, terminatedInstr, tangle, merge, initialized, constructType, mergeBlock, continueBlock, defaultBlock, caseBlocks) == 
    [opLabelIdx |-> opLabel,
    terminatedInstrIdx |-> terminatedInstr,
    tangle |-> tangle,
    merge |-> merge,
    initialized |-> initialized,
    constructType |-> constructType,
    mergeBlock |-> mergeBlock,
    continueBlock |-> continueBlock,
    defaultBlock |-> defaultBlock,
    caseBlocks |-> caseBlocks]

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


\* blockIdx is the opLabel index of the block
\* DynamicInstance(blockIdx, thread) == 


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


(* Global Variables *)

InitProgram ==
    /\ InitDB
    /\ InitGPU

\* Invariant: Each thread belongs to exactly one DB
ThreadBelongsExactlyOne ==
    /\ \A t \in Threads:
        \E DB \in DynamicExecutionGraphSet:
            t \in DB.currentThreadSet[WorkGroupId(t) + 1]
    /\ \A t1, t2 \in Threads:
        IF WorkGroupId(t1) = WorkGroupId(t2) THEN 
            /\ \A DB1, DB2 \in DynamicExecutionGraphSet:
                (t1 \in DB1.currentThreadSet[WorkGroupId(t1) + 1] /\ t2 \in DB2.currentThreadSet[WorkGroupId(t2) + 1]) => DB1 = DB2
        ELSE
            TRUE

\* Invariant: Each dynamic execution graph has a unique block sequence
UniqueBlockSequence ==
    \A DB1, DB2 \in DynamicExecutionGraphSet:
        DB1.blockSeq = DB2.blockSeq => DB1 = DB2
====



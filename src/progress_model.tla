---- MODULE progress_model ----
EXTENDS Integers, Naturals, Sequences

\*CONSTANTS Threads

Instructions == {"AtomicExchange", "Store", "Terminate"}

Thread == [id: Int, pc: Int, instructions: Seq(Instruction)] \* define a thread as a record with an id, a program counter, and a sequence of instructions

(* Define two threads *)

t1 == [id |-> 1, pc |-> 1, instructions |-> << "AtomicExchange", "Store", "Terminate">>]
t2 == [id |-> 2, pc |-> 1, instructions |-> << "AtomicExchange", "Store", "Terminate">>]

Threads == {t1, t2}


TypeInvariant == 
    \A t \in Threads: 
        \A i \in t.instructions:
            t.instructions[i] \in Instructions
(* Define a sequence of instructions for each thread *)
\*ThreadInstructions == [t \in Threads |-> Instructions]


VARIABLES activeThreads, checkLock, lockOwner, currentIndices, nextInstructions

vars == <<activeThreads, checkLock, lockOwner, currentIndices, nextInstructions>>


AtomicExchange(t, checkVal, jumpInst, doExch, exchVal) ==
    /\ LET newCurrentIndex == IF checkLock = checkVal THEN jumpInst ELSE currentIndices[t] + 1
            newCheckLock == IF doExch THEN exchVal ELSE checkLock
        IN 
            /\ currentIndices' = [currentIndices EXCEPT ![t] = newCurrentIndex]
            /\ checkLock' = newCheckLock



AcquireLock(t) ==
  /\ lockOwner = ""
  /\ lockOwner' = t

ReleaseLock(t) ==
  /\ lockOwner = t
  /\ lockOwner' = ""
(* Initialization of the variables *)
\* Init == 
\*     /\ ThreadInstructions
\*     /\ F = {} \* initialize the fair execution set to be empty
\*     /\ checkLock = FALSE \* initialize the lock to be unlocked
\*     /\ lockOwner = NULL \* initialize the lock owner to be NULL
\*     /\ currentIndices = [t \in Threads |-> 1] \* initialize the program counter for each thread to be 1
\*     /\ nextInstructions = [t \in Threads |-> NULL] \* initialize the next instruction of the thread
 Init == 
     /\ checkLock = FALSE \* initialize the lock to be unlocked
     /\ lockOwner = "" \* initialize the lock owner to be NULL
     /\ activeThreads = {} 

AddThread(t) ==
    /\ t \notin Threads
    /\ Threads' = Threads \/ {t}
    /\ UNCHANGED <<lockOwner, activeThreads>>

RemoveThread(t) ==
    /\ t \in Threads
    /\ Threads' = Threads \ {t}
    /\ UNCHANGED <<lockOwner, activeThreads>>

MarkActive(t) ==
    /\ t \in Threads
    /\ activeThreads' = activeThreads \/ {t}
    /\ UNCHANGED <<lockOwner, Threads>>

MarkInactive(t) ==
    /\ t \in Threads
    /\ activeThreads' = activeThreads \ {t}
    /\ UNCHANGED <<lockOwner, Threads>>


\* GetNextInstruction(t) ==
\*     LET currentIndex == currentIndices[t]
\*         instructions == ThreadInstructions[t]
\*     IN
\*     IF currentIndex <= Len(instructions)
\*     THEN  /\ nextInstructions' = [nextInstructions EXCEPT ![t] = instructions[currentIndex]]
\*           /\ currentIndices' = [currentIndices EXCEPT ![t] = currentIndex + 1]
\*     ELSE  /\ UNCHANGED << nextInstructions, currentIndices >>


\* (* Define the actions *)
\* Step(tid, inst) == 
\*     /\ IF inst = "LockAcqInst" THEN AtomicExchange(TRUE, "LockAcqInst", TRUE, TRUE)
\*        ELSE IF inst = "Store" THEN TRUE
\*        ELSE IF inst = "LockRelInst" THEN AtomicExchange(FALSE, "LockRelInst", TRUE, FALSE)
\*        ELSE TRUE
\*     /\ F' = F \/ {tid}

Step(tid, inst) ==
    /\ MarkActive(tid)
    /\
        \/ /\ inst = "AtomicExchange"
           /\ AtomicExchange(tid)
        \/ /\ inst = "Store"
           /\ TRUE
        \/ /\ inst = "Terminate" \* if encounter terminate instruction, mark the thread as inactive and remove the thread
           /\ MarkInactive(tid)
           /\ RemoveThread(tid)




\* Next == 
\*     \E t \in Threads:
\*         LET currentIndex == currentIndices[t]
\*             instructions == ThreadInstructions[t]
\*             nextInst == IF currentIndex <= Len(instructions)
\*                         THEN instructions[currentIndex]
\*                         ELSE NULL
\*         IN
\*             /\ IF currentIndex <= Len(instructions)
\*                THEN  /\ nextInstructions' = [nextInstructions EXCEPT ![t] = nextInst] \* update the next instruction only for thread t
\*                      /\ currentIndices' = [currentIndices EXCEPT ![t] = currentIndex + 1] \* increment the program counter only for thread t
\*                ELSE  /\ UNCHANGED << nextInstructions, currentIndices >>
\*             /\ Step(t, nextInst)
    
 Next == 
     \E t \in Threads, inst \in Instructions: \* Non-deterministically choose a thread and an instruction
        /\ Step(t, inst)


EventuallyAcquire ==
    \A t \in activeThreads: <> (lockOwner = t)

(* Specification *)
Spec == 
    /\ Init
    /\ [][Next]_vars
    /\ EventuallyAcquire

(* Add fairness conditions if necessary *)
\* Fairness == 
\*     /\ WF_<<F, pc>>(Step)
\*     /\ SF_<<F, pc>>(Terminate)

====

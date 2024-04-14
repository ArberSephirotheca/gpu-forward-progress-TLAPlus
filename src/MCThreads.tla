---- MODULE MCThreads ----
LOCAL INSTANCE Integers
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences

VARIABLES checkLock, pc, terminated

(* Thread Configuration *)
InstructionSet == {"Load", "Store", "Terminate"}

ThreadInstructions == <<<< "Load", "Terminate">>, <<"Store", "Terminate">>>>

Threads == {1, 2}

LOCAL INSTANCE ThreadsConf

(* Thread variables and functions start here *)
threadVars == << checkLock, pc, terminated>>

InitThreadVars ==
    /\  pc = [t \in Threads |-> 1]
    /\  terminated = [t \in Threads |-> FALSE]

InitThreads == 
    /\  InitThreadVars
    /\  checkLock = FALSE

AtomicExchange(t, checkVal, jumpInst, doExch, exchVal) ==
    /\  LET newPc == IF checkLock = checkVal THEN jumpInst ELSE pc[t] + 1
            newCheckLock == IF doExch THEN exchVal ELSE checkLock
        IN
            /\ pc' = [pc EXCEPT ![t] = newPc]
            /\ checkLock' = newCheckLock


Load(t) == 
    /\  AtomicExchange(t, FALSE, pc[t], FALSE, FALSE)
    /\  UNCHANGED terminated

Store(t) == 
    /\  AtomicExchange(t, TRUE, pc[t] + 1, TRUE, TRUE)
    /\  UNCHANGED terminated

Terminate(t) ==
    /\ terminated' = [terminated EXCEPT ![t] = TRUE]
    /\ UNCHANGED <<pc, checkLock>>

Step(t) ==
    IF terminated[t] = FALSE THEN
        IF ThreadInstructions[t][pc[t]] = "Load" THEN
            Load(t)
        ELSE IF ThreadInstructions[t][pc[t]] = "Store" THEN
            Store(t)
        ELSE IF ThreadInstructions[t][pc[t]] = "Terminate" THEN
            Terminate(t)
        ELSE
            /\ UNCHANGED threadVars
    ELSE 
        /\ UNCHANGED threadVars

====
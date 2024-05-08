
CONSTANTS
    \* Number of philosophers
    NP
VARIABLES forks, hungry, pc, holder, self
Init == (* Global variables *)
        /\ forks = [ fork \in 1..NP |-> [
                        holder |-> IF fork = 2 THEN 1 ELSE fork,
                           clean |-> FALSE
                     ]
                   ]
        (* Process Philosopher *)
        /\ hungry = [self \in 1..NP |-> TRUE]
        /\ pc = [self \in ProcSet |-> "Loop"]


Loop(self) == ...

Think(self) == ...

Eat(self) == ...

Philosopher(self) == Loop(self) \/ Think(self) \/ Eat(self)

Next == (\E self \in 1..NP: Philosopher(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..NP : WF_vars(Philosopher(self))



TH
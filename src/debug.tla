------------------------------- MODULE debug -------------------------------
EXTENDS Naturals
VARIABLE count, terminated
vars == <<count, terminated>>
Init ==
/\ count = 0
/\ terminated = FALSE
Next ==
/\ count' = (count + 1) % 3
/\ UNCHANGED terminated
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
Liveness == <>(terminated)
=============================================================================
---- MODULE Dijkstra ----
\* 
\* Specification of Dijkstra's self-stabilizing protocol as described in
\* 
\* [1] Edsger W. Dijkstra. 1974. Self-stabilizing systems in spite of distributed control. 
\* Commun. ACM 17, 11 (Nov. 1974), 643–644. https://doi.org/10.1145/361179.361202. 
\* 
\* In particular we describe the "Solution with Four-state Machines" as described in the paper.
\* 
\* A version of this protocol used as a synthesis case study is also described in
\* [GasconTiwari] https://arxiv.org/abs/1407.5392 and also in
\* Automatic Completion of Distributed Protocols with Symmetry (CAV 2015, https://arxiv.org/abs/1505.04409)
\* 
\* See also model here: https://github.com/abhishekudupa/kinara/blob/6e465ac41fc995f0df726dc2c5b73e3ba4a7775b/test/mc/Dijkstra4.cpp
\* 

EXTENDS Integers, Sequences, TLC, FiniteSets

CONSTANTS N  \* Assuming N is the number of processes and N = 4

VARIABLES x, up

vars == <<x,up>>

BOTTOM == 1
TOP == N

\* Definition of initial states.
\* Can start in any possible state to check for self-stabilization.
Init ==
    /\ x \in [1..N -> BOOLEAN]
    /\ up \in [1..N -> BOOLEAN]
    /\ up[BOTTOM] = FALSE
    /\ up[TOP] = TRUE

MoveBottom(i) ==
    /\ i = BOTTOM
    \* 
    \* Dijsktra's precondition for P1 (bottom) in [1]
    \* /\ x[i] = x[i+1] /\ ~up[i+1]
    \* 
    \* CAV 2015 precondition for P1 (appears different than Dijkstra's original?).
    /\ x[i] = x[i+1] 
    /\ x' = [x EXCEPT ![i] = ~x[i]]
    /\ UNCHANGED up

\* 
\* Define the move for each middle machine
\* 
\* From CAV 2015:
\* 
\* "We attempted to synthesize the guards and updates for the middle two processes of 
\* a four process system P1, P2, P3, P4...
\* The guard is a function of xi−1, xi, xi+1, upi−1, upi, upi+1, 
\* and the updates of xi and upi are functions of xi and upi."
\* 
\* "We also constrain the completions of P2 and P3 to be identical."
\* 
MoveMidA(i) ==
    /\ i \notin {TOP, BOTTOM}
    \* PRE HOLE.
    /\ x[i] # x[i-1]
    \* POST HOLE.
    /\ x' = [x EXCEPT ![i] = ~x[i]]
    /\ up' = [up EXCEPT ![i] = TRUE]

MoveMidB(i) ==
    /\ i \notin {TOP, BOTTOM}
    \* PRE HOLE.
    /\ x[i] = x[i+1] /\ up[i] /\ ~up[i+1]
    \* POST HOLE.
    /\ up' = [up EXCEPT ![i] = FALSE]
    /\ UNCHANGED x

MoveTop(i) ==
    /\ i = TOP
    /\ x[i] # x[i-1]
    /\ x' = [x EXCEPT ![i] = ~x[i]]
    /\ UNCHANGED up    
 
-----------
\* 
\* Run with <tlc> -deadlock -config Dijkstra_GasconTiwari.cfg Dijkstra
\* 
MoveBottom_GasconTiwari(i) ==
    /\ i = BOTTOM
    /\ x[i] = x[i+1] /\ up[i+1]
    /\ x' = [x EXCEPT ![i] = ~x[i]]
    /\ UNCHANGED up

MoveMidA_GasconTiwari(i) ==
    /\ i \notin {TOP, BOTTOM}
    /\ x[i] # x[i-1]
    /\ x' = [x EXCEPT ![i] = ~x[i]]
    /\ up' = [up EXCEPT ![i] = FALSE]

MoveMidB_GasconTiwari(i) ==
    /\ i \notin {TOP, BOTTOM}
    /\ x[i] = x[i+1] /\ up[i+1]
    /\ up' = [up EXCEPT ![i] = TRUE]
    /\ UNCHANGED x
    
------------

\* Next state relation describing the system's transitions
Next ==
    \/ \E i \in 1..N : MoveBottom(i)
    \/ \E i \in 1..N : MoveMidA(i)
    \/ \E i \in 1..N : MoveMidB(i)
    \/ \E i \in 1..N : MoveTop(i)

Fairness ==
    /\ \A i \in 1..N : WF_vars(MoveBottom(i))
    /\ \A i \in 1..N : WF_vars(MoveMidA(i))
    /\ \A i \in 1..N : WF_vars(MoveMidB(i))
    /\ \A i \in 1..N : WF_vars(MoveTop(i))

\* Specification combining initial state and transition relation
Spec ==
    /\ Init
    /\ [][Next]_<<x, up>>
    /\ Fairness

EnabledRules ==
    { 
        <<"1",ENABLED MoveBottom(1)>>, 
        <<"2a",ENABLED MoveMidA(2)>>,
        <<"2b",ENABLED MoveMidB(2)>>, \* requirement that enabled action modifies state?
        <<"3a",ENABLED MoveMidA(3)>>,
        <<"3b",ENABLED MoveMidB(3)>>, \* requirement that enabled action modifies state.
        <<"4",ENABLED MoveTop(4)>>
    }

NumEnabledRules ==
    Cardinality({r \in EnabledRules : r[2]})

\* From CAV 2015:
\* "We followed the definition in [14] and defined a state as being legitimate 
\* if exactly one guarded command is enabled globally."
InLegitimateState ==
    /\ NumEnabledRules = 1

\* System should stabilize to a legitimate state
StabilizesToLegitimate ==
    <>[](InLegitimateState)

Alias == [
    x |-> x,
    up |-> up,
    enabledRules |-> EnabledRules,
    numEnabledRules |-> NumEnabledRules
]

=============================================================================
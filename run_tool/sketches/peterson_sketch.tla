---- MODULE peterson ----
EXTENDS TLC, Naturals, FiniteSets
\*
\* Specification of Peterson's algorithm in TLA+.
\*

(*
    Summary of the algorithm in pseudocode (i.e. PlusCal).

    variables flag = [i \in {0, 1} |-> FALSE],  turn = 0;
        \* Declares the global variables flag and turn and their initial values;
        \* flag is a 2-element array with initially flag[0] = flag[1] = FALSE.
        process (proc \in {0,1}) {
        \* Declares two processes with identifier self equal to 0 and 1.
        a1: while (TRUE) {
                skip ;  \* the noncritical section
        a2:  flag[self] := TRUE ;
        a3:  turn := 1 - self ;   
        a4:  await (flag[1-self] = FALSE) \/ (turn = self);
        cs:  skip ;  \* the critical section
        a5:  flag[self] := FALSE               }     }     }
*)
        
VARIABLE flag, turn

\* The program counter for each process.
VARIABLE pc

vars == << flag, turn, pc >>

\* The set of processes.
CONSTANT ProcSet

ASSUME Cardinality(ProcSet) = 2

\* Return the other process.
Other(p) == CHOOSE q \in ProcSet : q # p


\*
\* The transitions of the protocol.
\*


a1(self) ==
    /\ __a1(self)_g0__ \* gt: pc[self] = 1
    /\ pc' = __a1(self)_pc__ \* gt: [pc EXCEPT ![self] = 2]
    /\ flag' = __a1(self)_flag__ \* gt: flag
    /\ turn' = __a1(self)_turn__ \* gt: turn


a2(self) ==
    /\ __a2(self)_g0__ \* gt: pc[self] = 2
    /\ flag' = __a2(self)_flag__ \* gt: [flag EXCEPT ![self] = TRUE]
    /\ pc' = __a2(self)_pc__ \* gt: [pc EXCEPT ![self] = 3]
    /\ turn' = __a2(self)_turn__ \* gt: turn


a3(self, other) ==
    /\ __a3(self, other)_g0__ \* gt: pc[self] = 3
    /\ __a3(self, other)_g1__ \* gt: self # other
    /\ turn' = __a3(self, other)_turn__ \* gt: other
    /\ pc' = __a3(self, other)_pc__ \* gt: [pc EXCEPT ![self] = 4]
    /\ flag' = __a3(self, other)_flag__ \* gt: flag


a4(self, other) ==
    /\ __a4(self, other)_g0__ \* gt: self # other
    /\ __a4(self, other)_g1__ \* gt: pc[self] = 4
    /\ __a4(self, other)_g2__ \* gt: (flag[other] = FALSE) \/ (turn = self)
    /\ pc' = __a4(self, other)_pc__ \* gt: [pc EXCEPT ![self] = 0]
    /\ flag' = __a4(self, other)_flag__ \* gt: flag
    /\ turn' = __a4(self, other)_turn__ \* gt: turn


cs(self) ==
    /\ __cs(self)_g0__ \* gt: pc[self] = 0
    /\ pc' = __cs(self)_pc__ \* gt: [pc EXCEPT ![self] = 5]
    /\ flag' = __cs(self)_flag__ \* gt: flag
    /\ turn' = __cs(self)_turn__ \* gt: turn


a5(self) ==
    /\ __a5(self)_g0__ \* gt: pc[self] = 5
    /\ flag' = __a5(self)_flag__ \* gt: [flag EXCEPT ![self] = FALSE]
    /\ pc' = __a5(self)_pc__ \* gt: [pc EXCEPT ![self] = 1]
    /\ turn' = __a5(self)_turn__ \* gt: turn



Init == 
    /\ flag = [i \in ProcSet |-> FALSE]
    /\ turn \in ProcSet
    /\ pc = [self \in ProcSet |-> 1]

ParamNext1(self) == 
    \/ a1(self)
    \/ a2(self) 
    \/ cs(self) 
    \/ a5(self)

ParamNext2(self, other) ==
    \/ a3(self, other) 
    \/ a4(self, other)

Next == 
    \/ \E self \in ProcSet : ParamNext1(self)
    \/ \E self, other \in ProcSet : ParamNext2(self, other)

Spec == 
    /\ Init 
    /\ [][Next]_vars
    /\ \A self \in ProcSet : SF_vars(ParamNext1(self))
    /\ \A self,other \in ProcSet : SF_vars(ParamNext2(self, other))

\* The mutual exclusion property i.e. the processes cannot be 
\* inside the critical sectuion at the same time.
Mutex == \A p,q \in ProcSet : (p # q) => ~(pc[p] = 0 /\ pc[q] = 0)

Liveness == 
    /\ \A p \in ProcSet : []<>(pc[p] = 0)

\* Symmetry == Permutations(ProcSet)
====
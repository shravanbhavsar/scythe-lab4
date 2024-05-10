---- MODULE peterson ----
\* table: https://github.com/egolf-cs/tla-synthesis/blob/0575612955b0ad69cd051edb41bf8eeec87b0e9c/tool_and_experimentation/reports/README.md
\* configindex: 413
\* eid: 14.15.16.17

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
    /\ pc[self] = 1 \* gt: pc[self] = 1
    /\ pc' = [pc EXCEPT ![self] = 2] \* gt: [pc EXCEPT ![self] = 2]
    /\ flag' = flag \* gt: flag
    /\ turn' = turn \* gt: turn


a2(self) ==
    /\ pc[self] = 2 \* gt: pc[self] = 2
    /\ flag' = [flag EXCEPT ![self] = TRUE] \* gt: [flag EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = 3] \* gt: [pc EXCEPT ![self] = 3]
    /\ turn' = turn \* gt: turn


a3(self, other) ==
    /\ pc[self] = 3 \* gt: pc[self] = 3
    /\ self # other \* gt: self # other
    /\ turn' = other \* gt: other
    /\ pc' = [pc EXCEPT ![self] = 4] \* gt: [pc EXCEPT ![self] = 4]
    /\ flag' = flag \* gt: flag


a4(self, other) ==
    /\ flag[self] \* gt: self # other
    /\ (turn = self) \* gt: pc[self] = 4
    /\ (4 = pc[self]) \* gt: (flag[other] = FALSE) \/ (turn = self)
    /\ pc' = [pc EXCEPT ![self] = 0] \* gt: [pc EXCEPT ![self] = 0]
    /\ flag' = flag \* gt: flag
    /\ turn' = turn \* gt: turn


cs(self) ==
    /\ pc[self] = 0 \* gt: pc[self] = 0
    /\ pc' = [pc EXCEPT ![self] = 5] \* gt: [pc EXCEPT ![self] = 5]
    /\ flag' = flag \* gt: flag
    /\ turn' = turn \* gt: turn


a5(self) ==
    /\ pc[self] = 5 \* gt: pc[self] = 5
    /\ flag' = [flag EXCEPT ![self] = FALSE] \* gt: [flag EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = 1] \* gt: [pc EXCEPT ![self] = 1]
    /\ turn' = turn \* gt: turn



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
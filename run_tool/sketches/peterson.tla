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

\* <actions>

a1(self) == 
    /\ pc[self] = 1
    /\ pc' = [pc EXCEPT ![self] = 2]
    /\ flag' = flag
    /\ turn' = turn

\* A process sets its own flag to TRUE.
a2(self) == 
    /\ pc[self] = 2
    /\ flag' = [flag EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = 3]
    /\ turn' = turn


\* A process updates 'turn'.
a3(self, other) == 
    /\ pc[self] = 3
    /\ self # other
    /\ turn' = other
    /\ pc' = [pc EXCEPT ![self] = 4]
    /\ flag' = flag

\* A process enters the critical section.
a4(self, other) == 
    \* Removing the self # other condition from the guard of the action
    \* results in a "correct" protocol. However, that protocol would 
    \* have worse performance. When self = other, the flag[other] = FALSE
    \* condition is never met, and the process is forced to wait for the
    \* other process to set turn = self.
    /\ self # other
    /\ pc[self] = 4
    \* Replacing this disjunction with: pc[other] # 0 results in a correct
    \* protocol. Doing this would violate a modeling assumption: the processes
    \* are not allowed to know the program counter of the other process.
    \* Replacing it with turn = self results in a correct protocol. However,
    \* the performance of the protocol would be worse.
    /\ (flag[other] = FALSE) \/ (turn = self)
    /\ pc' = [pc EXCEPT ![self] = 0]
    /\ flag' = flag
    /\ turn' = turn

\* A process exits the critical section.
cs(self) == 
    /\ pc[self] = 0
    /\ pc' = [pc EXCEPT ![self] = 5]
    /\ flag' = flag
    /\ turn' = turn

\* A process resets its own flag to FALSE after it left the critical section.
a5(self) == 
    /\ pc[self] = 5
    \* If the process does not reset its flag, the protocol is still correct.
    \* However, the performance of the protocol would be worse, since the other
    \* process would have to wait for this process to set turn' = other.
    /\ flag' = [flag EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = 1]
    /\ turn' = turn

\* </actions>

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

\* <properties>
\* The mutual exclusion property i.e. the processes cannot be 
\* inside the critical sectuion at the same time.
Mutex == \A p,q \in ProcSet : (p # q) => ~(pc[p] = 0 /\ pc[q] = 0)

Liveness == 
    /\ \A p \in ProcSet : []<>(pc[p] = 0)
    /\ []<> (0 = 1)
\* </properties>

\* Symmetry == Permutations(ProcSet)
====
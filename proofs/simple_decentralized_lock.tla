---- MODULE simple_decentralized_lock ----
\* configindex: 486 

\* benchmark: ex-simple-decentralized-lock

EXTENDS TLC

CONSTANT Node

VARIABLE message
VARIABLE has_lock

vars == <<message, has_lock>>


Send(src, dst) ==
    /\ has_lock[src] \* gt: has_lock[src]
    /\ message' = {<<src, dst>>} \* gt: message \cup {<<src, dst>>}
    /\ has_lock' = [has_lock EXCEPT ![src] = FALSE] \* gt: [has_lock EXCEPT ![src] = FALSE]


Recv(src, dst) ==
    /\ (<<src, dst>> \in message) \* gt: <<src, dst>> \in message
    /\ message' = (message \ message) \* gt: message \ {<<src,dst>>}
    /\ has_lock' = [has_lock EXCEPT ![dst] = TRUE] \* gt: [has_lock EXCEPT ![dst] = TRUE]



NextParam(src, dst) == 
    \/ Send(src, dst)
    \/ Recv(src, dst)

Next ==
    \/ \E src,dst \in Node : NextParam(src, dst)

Init ==
    \E start \in Node :
        /\ message = {}
        /\ has_lock = [n \in Node |-> n = start]

Spec == 
    /\ Init 
    /\ [][Next]_vars 
    /\ \A src, dst \in Node : SF_vars(NextParam(src, dst))

\* Two nodes can't hold lock at once.
Safety == 
    /\ \A x,y \in Node : (has_lock[x] /\ has_lock[y]) => (x = y)


Temporal ==
    /\ \A x \in Node : <> has_lock[x]
    /\ [][\A x,y \in Node : (<<x,y>> \in message' => has_lock[x])]_vars
====
---- MODULE simple_decentralized_lock ----
\* benchmark: ex-simple-decentralized-lock

EXTENDS TLC

CONSTANT Node

VARIABLE message
VARIABLE has_lock

vars == <<message, has_lock>>


Send(src, dst) ==
    /\ __Send(src, dst)_g0__ \* gt: has_lock[src]
    /\ message' = __Send(src, dst)_message__ \* gt: message \cup {<<src, dst>>}
    /\ has_lock' = __Send(src, dst)_has_lock__ \* gt: [has_lock EXCEPT ![src] = FALSE]


Recv(src, dst) ==
    /\ __Recv(src, dst)_g0__ \* gt: <<src, dst>> \in message
    /\ message' = __Recv(src, dst)_message__ \* gt: message \ {<<src,dst>>}
    /\ has_lock' = __Recv(src, dst)_has_lock__ \* gt: [has_lock EXCEPT ![dst] = TRUE]



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
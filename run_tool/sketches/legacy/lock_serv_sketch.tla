---- MODULE lock_serv ----
EXTENDS TLC

CONSTANT Node

VARIABLE lock_msg
VARIABLE grant_msg
VARIABLE unlock_msg
VARIABLE holds_lock
VARIABLE server_holds_lock

vars == <<lock_msg, grant_msg, unlock_msg, holds_lock, server_holds_lock>>

\* Uncontrollable from the perspective of synthesis.
SendLock(n) == 
    /\ lock_msg' = lock_msg \cup {n}
    /\ UNCHANGED <<unlock_msg, grant_msg, holds_lock, server_holds_lock>>

RecvLock(n) == 
    /\ __RecvLock_g1__ \* gt: server_holds_lock
    /\ __RecvLock_g2__ \* gt: n \in lock_msg
    /\ server_holds_lock' = __RecvLock_server_holds_lock__ \* gt: FALSE
    /\ lock_msg' = __RecvLock_lock_msg__ \* gt: lock_msg \ {n}
    /\ grant_msg' = __RecvLock_grant_msg__ \* gt: grant_msg \cup {n}
    /\ UNCHANGED <<unlock_msg,holds_lock>>

RecvGrant(n) == 
    /\ __RecvGrant_g1__ \* gt: n \in grant_msg
    /\ grant_msg' = __RecvGrant_grant_msg__ \* gt: grant_msg \ {n}
    /\ holds_lock' = __RecvGrant_holds_lock__ \* gt: holds_lock \cup {n}
    /\ UNCHANGED <<lock_msg,unlock_msg,server_holds_lock>>

Unlock(n) == 
    /\ __Unlock_g1__ \* gt: n \in holds_lock
    /\ holds_lock' = __Unlock_holds_lock__ \* gt: holds_lock \ {n}
    /\ unlock_msg' = __Unlock_unlock_msg__ \* gt: unlock_msg \cup {n}
    /\ UNCHANGED <<lock_msg, grant_msg, server_holds_lock>>

RecvUnlock(n) == 
    /\ __RecvUnlock_g1__ \* gt: n \in unlock_msg
    /\ unlock_msg' = __RecvUnlock_unlock_msg__ \* gt: unlock_msg \ {n}
    /\ server_holds_lock' = __RecvUnlock_server_holds_lock__ \* gt: TRUE
    /\ UNCHANGED <<lock_msg, grant_msg, holds_lock>>

NextParam(n) == 
    \/ SendLock(n)
    \/ RecvLock(n)
    \/ RecvGrant(n)
    \/ Unlock(n)
    \/ RecvUnlock(n)

Next == \E n \in Node : NextParam(n)

Init == 
    /\ lock_msg = {}
    /\ unlock_msg = {}
    /\ grant_msg = {}
    /\ holds_lock = {}
    /\ server_holds_lock = TRUE

Spec == 
    /\ Init 
    /\ [][Next]_vars
    /\ \A n \in Node : SF_vars(NextParam(n))

\* No two clients think they hold the lock simultaneously.
Mutex == \A x,y \in Node : ((x \in holds_lock) /\ (y \in holds_lock)) => (x = y)

Liveness ==
    /\ \A n \in Node : [] (n \in lock_msg => <> (n \in holds_lock))
    /\ \A n \in Node : []<> (n \in lock_msg)
    /\ \A n \in Node : []<> (n \notin lock_msg)
====
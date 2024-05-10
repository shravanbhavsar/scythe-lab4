---- MODULE lock_serv ----
EXTENDS TLC

CONSTANT Node

VARIABLE lock_msg
VARIABLE grant_msg
VARIABLE unlock_msg
VARIABLE holds_lock
VARIABLE server_holds_lock

vars == <<lock_msg, grant_msg, unlock_msg, holds_lock, server_holds_lock>>

SendLock(n) == 
    /\ lock_msg' = lock_msg \cup {n}
    /\ UNCHANGED <<unlock_msg, grant_msg, holds_lock, server_holds_lock>>

RecvLock(n) == 
    /\ server_holds_lock
    /\ n \in lock_msg
    /\ server_holds_lock' = FALSE
    /\ lock_msg' = lock_msg \ {n}
    /\ grant_msg' = grant_msg \cup {n}
    /\ UNCHANGED <<unlock_msg,holds_lock>>

RecvGrant(n) == 
    /\ n \in grant_msg
    /\ grant_msg' = grant_msg \ {n}
    /\ holds_lock' = holds_lock \cup {n}
    /\ UNCHANGED <<lock_msg,unlock_msg,server_holds_lock>>

Unlock(n) == 
    /\ n \in holds_lock
    /\ holds_lock' = holds_lock \ {n}
    /\ unlock_msg' = unlock_msg \cup {n}
    /\ UNCHANGED <<lock_msg, grant_msg, server_holds_lock>>

RecvUnlock(n) == 
    /\ n \in unlock_msg
    /\ unlock_msg' = unlock_msg \ {n}
    /\ server_holds_lock' = TRUE
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
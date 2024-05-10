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
    /\ lock_msg' = __SendLock(n)_lock_msg__ \* gt: [lock_msg EXCEPT ![n] = TRUE]
    /\ grant_msg' = __SendLock(n)_grant_msg__ \* gt: grant_msg
    /\ holds_lock' = __SendLock(n)_holds_lock__ \* gt: holds_lock
    /\ unlock_msg' = __SendLock(n)_unlock_msg__ \* gt: unlock_msg
    /\ UNCHANGED server_holds_lock


RecvLock(n) ==
    /\ __RecvLock(n)_g0__ \* gt: server_holds_lock
    /\ __RecvLock(n)_g1__ \* gt: lock_msg[n]
    /\ server_holds_lock' = __RecvLock(n)_server_holds_lock__ \* gt: FALSE
    /\ lock_msg' = __RecvLock(n)_lock_msg__ \* gt: [lock_msg EXCEPT ![n] = FALSE]
    /\ grant_msg' = __RecvLock(n)_grant_msg__ \* gt: [grant_msg EXCEPT ![n] = TRUE]
    /\ unlock_msg' = __RecvLock(n)_unlock_msg__ \* gt: unlock_msg
    /\ UNCHANGED holds_lock


RecvGrant(n) ==
    /\ __RecvGrant(n)_g0__ \* gt: grant_msg[n]
    /\ grant_msg' = __RecvGrant(n)_grant_msg__ \* gt: [grant_msg EXCEPT ![n] = FALSE]
    /\ holds_lock' = __RecvGrant(n)_holds_lock__ \* gt: [holds_lock EXCEPT ![n] = TRUE]
    /\ lock_msg' = __RecvGrant(n)_lock_msg__ \* gt: lock_msg
    /\ unlock_msg' = __RecvGrant(n)_unlock_msg__ \* gt: unlock_msg
    /\ UNCHANGED server_holds_lock


Unlock(n) ==
    /\ __Unlock(n)_g0__ \* gt: holds_lock[n]
    /\ holds_lock' = __Unlock(n)_holds_lock__ \* gt: [holds_lock EXCEPT ![n] = FALSE]
    /\ unlock_msg' = __Unlock(n)_unlock_msg__ \* gt: [unlock_msg EXCEPT ![n] = TRUE]
    /\ lock_msg' = __Unlock(n)_lock_msg__ \* gt: lock_msg
    /\ grant_msg' = __Unlock(n)_grant_msg__ \* gt: grant_msg
    /\ UNCHANGED server_holds_lock


RecvUnlock(n) ==
    /\ __RecvUnlock(n)_g0__ \* gt: unlock_msg[n]
    /\ unlock_msg' = __RecvUnlock(n)_unlock_msg__ \* gt: [unlock_msg EXCEPT ![n] = FALSE]
    /\ server_holds_lock' = __RecvUnlock(n)_server_holds_lock__ \* gt: TRUE
    /\ lock_msg' = __RecvUnlock(n)_lock_msg__ \* gt: lock_msg
    /\ grant_msg' = __RecvUnlock(n)_grant_msg__ \* gt: grant_msg
    /\ UNCHANGED holds_lock



NextParam(n) == 
    \/ SendLock(n)
    \/ RecvLock(n)
    \/ RecvGrant(n)
    \/ Unlock(n)
    \/ RecvUnlock(n)

Next == \E n \in Node : NextParam(n)

Init == 
    /\ lock_msg = [n \in Node |-> FALSE]
    /\ unlock_msg = [n \in Node |-> FALSE]
    /\ grant_msg = [n \in Node |-> FALSE]
    /\ holds_lock = [n \in Node |-> FALSE]
    /\ server_holds_lock = TRUE

Spec == 
    /\ Init 
    /\ [][Next]_vars
    /\ \A n \in Node : SF_vars(NextParam(n))

\* No two clients think they hold the lock simultaneously.
Mutex == \A x,y \in Node : ((holds_lock[x]) /\ (holds_lock[y])) => (x = y)

Liveness == 
    /\ \A n \in Node : [] (lock_msg[n] => <> holds_lock[n])
    /\ \A n \in Node : []<> lock_msg[n]
    /\ \A n \in Node : []<> (~lock_msg[n])
====
---- MODULE lock_serv ----
EXTENDS TLC

CONSTANT Node

VARIABLE lock_msg
VARIABLE grant_msg
VARIABLE unlock_msg
VARIABLE holds_lock
VARIABLE server_holds_lock

vars == <<lock_msg, grant_msg, unlock_msg, holds_lock, server_holds_lock>>

\* <actions>

\* client action
SendLock(n) == 
    /\ lock_msg' = [lock_msg EXCEPT ![n] = TRUE]
    /\ grant_msg' = grant_msg
    /\ holds_lock' = holds_lock
    /\ unlock_msg' = unlock_msg
    /\ UNCHANGED server_holds_lock

\* server action
RecvLock(n) == 
    /\ server_holds_lock
    /\ lock_msg[n]
    /\ server_holds_lock' = FALSE
    /\ lock_msg' = [lock_msg EXCEPT ![n] = FALSE]
    /\ grant_msg' = [grant_msg EXCEPT ![n] = TRUE]
    /\ unlock_msg' = unlock_msg
    /\ UNCHANGED holds_lock

\* client action
\* RecvGrant(n) == 
\*     /\ grant_msg[n]
\*     /\ grant_msg' = [grant_msg EXCEPT ![n] = FALSE]
\*     /\ holds_lock' = [holds_lock EXCEPT ![n] = TRUE]
\*     /\ lock_msg' = lock_msg
\*     /\ unlock_msg' = unlock_msg
\*     /\ UNCHANGED server_holds_lock
RecvGrant(n) == 
    /\ ~grant_msg[n]
    /\ grant_msg' = grant_msg
    /\ holds_lock' = holds_lock
    /\ lock_msg' = [lock_msg EXCEPT ![n] = FALSE]
    /\ unlock_msg' = unlock_msg
    /\ UNCHANGED server_holds_lock

\* client action
Unlock(n) == 
    /\ holds_lock[n]
    /\ holds_lock' = [holds_lock EXCEPT ![n] = FALSE]
    /\ unlock_msg' = [unlock_msg EXCEPT ![n] = TRUE]
    /\ lock_msg' = lock_msg
    /\ grant_msg' = grant_msg
    /\ UNCHANGED server_holds_lock

\* server action
RecvUnlock(n) == 
    /\ unlock_msg[n]
    /\ unlock_msg' = [unlock_msg EXCEPT ![n] = FALSE]
    /\ server_holds_lock' = TRUE
    /\ lock_msg' = lock_msg
    /\ grant_msg' = grant_msg
    /\ UNCHANGED holds_lock

\* </actions>

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

\* <properties>
\* No two clients think they hold the lock simultaneously.
Mutex == \A x,y \in Node : ((holds_lock[x]) /\ (holds_lock[y])) => (x = y)

Liveness == 
    /\ \A n \in Node : [] (lock_msg[n] => <> holds_lock[n])
    /\ \A n \in Node : []<> lock_msg[n]
    /\ \A n \in Node : []<> (~lock_msg[n])
\* </properties>
====
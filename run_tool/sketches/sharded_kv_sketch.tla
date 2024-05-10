---- MODULE sharded_kv ----
EXTENDS TLC, Randomization

CONSTANT Key
CONSTANT Value
CONSTANT Node

CONSTANT Nil

\* The key-value store state on each node.
\* (Array (Tuple (Dom Node) (Dom Key)) (Dom Value))
VARIABLE table

\* The set of keys owned by each node.
\* (Array (Dom Node) (Set (Dom Key)))
VARIABLE owner

\* The set of active transfer messages.
\* (Set (Tuple (Dom Node) (Dom Key) (Dom Value)))
VARIABLE transfer_msg

\* environment / ghost variables
\* (Array (Dom Key) (Dom Value))
VARIABLE ghost_table
\* (Set (Alias Event)), 
\* where _Event := (Union (Alias Event1) (Alias Event2))
\* where _Event1 := (Tuple Int Key Value Int)
\* and _Event2 := (Tuple Int Ket Node Int)
VARIABLE event_queue
PUT == 0
GIVE == 1

vars == <<table, owner, transfer_msg, ghost_table, event_queue>>
ghost_vars == <<ghost_table>>
protocol_vars == <<table, owner, transfer_msg>>


Reshard(k,v,n_old,n_new) ==
    /\ __Reshard(k,v,n_old,n_new)_g0__ \* gt: table[<<n_old,k>>] = v
    /\ __Reshard(k,v,n_old,n_new)_g1__ \* gt: <<GIVE, k, n_old, n_new>> \in event_queue
    /\ event_queue' = __Reshard(k,v,n_old,n_new)_event_queue__ \* gt: event_queue \ {<<GIVE, k, n_old, n_new>>}
    /\ table' = __Reshard(k,v,n_old,n_new)_table__ \* gt: [table EXCEPT ![<<n_old,k>>] = Nil]
    /\ owner' = __Reshard(k,v,n_old,n_new)_owner__ \* gt: [owner EXCEPT ![n_old] = owner[n_old] \ {k}]
    /\ transfer_msg' = __Reshard(k,v,n_old,n_new)_transfer_msg__ \* gt: transfer_msg \cup {<<n_new,k,v>>}
    /\ UNCHANGED ghost_vars


RecvTransferMsg(n, k, v) ==
    /\ __RecvTransferMsg(n, k, v)_g0__ \* gt: <<n,k,v>> \in transfer_msg
    /\ transfer_msg' = __RecvTransferMsg(n, k, v)_transfer_msg__ \* gt: transfer_msg \ {<<n,k,v>>}
    /\ table' = __RecvTransferMsg(n, k, v)_table__ \* gt: [table EXCEPT ![<<n,k>>] = v]
    /\ owner' = __RecvTransferMsg(n, k, v)_owner__ \* gt: [owner EXCEPT ![n] = owner[n] \cup {k}]
    /\ event_queue' = __RecvTransferMsg(n, k, v)_event_queue__ \* gt: event_queue
    /\ UNCHANGED ghost_vars


Put(n, k, v) ==
    /\ __Put(n, k, v)_g0__ \* gt: k \in owner[n]
    /\ __Put(n, k, v)_g1__ \* gt: <<PUT, k, v, PUT>> \in event_queue
    /\ event_queue' = __Put(n, k, v)_event_queue__ \* gt: event_queue \ {<<PUT, k, v, PUT>>}
    /\ table' = __Put(n, k, v)_table__ \* gt: [table EXCEPT ![<<n,k>>] = v]
    /\ owner' = __Put(n, k, v)_owner__ \* gt: owner
    /\ transfer_msg' = __Put(n, k, v)_transfer_msg__ \* gt: transfer_msg
    /\ UNCHANGED ghost_vars



SchedulePut(k, v) ==
    /\ event_queue = {}
    /\ event_queue' = event_queue \cup {<<PUT, k, v, PUT>>}
    \* * * *
    /\ \E n \in Node : k \in owner[n]
    /\ ghost_table' = [ghost_table EXCEPT ![k] = v]
    /\ UNCHANGED protocol_vars

ScheduleGive(k, n_old, n_new) ==
    /\ event_queue = {}
    /\ event_queue' = event_queue \cup {<<GIVE, k, n_old, n_new>>}
    \* * * *
    /\ n_old # n_new
    /\ k \in owner[n_old]
    /\ ghost_table[k] # Nil
    /\ ghost_table' = ghost_table
    /\ UNCHANGED protocol_vars

ProtocolNext ==
    \/ \E k \in Key, v \in Value, n_old,n_new \in Node : 
        Reshard(k,v,n_old,n_new)
    \/ \E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v)
    \/ \E n \in Node, k \in Key, v \in Value : Put(n,k,v)

SchedulerNext ==
    \/ \E k \in Key, v \in Value : SchedulePut(k,v)
    \/ \E k \in Key, n_old,n_new \in Node : ScheduleGive(k,n_old,n_new)

Next == ProtocolNext \/ SchedulerNext

Init == 
    /\ table = [<<n,k>> \in Node \X Key  |-> Nil]
    \* Each node owns some subset of keys, and different nodes
    \* can't own the same key.
    /\ owner \in [Node -> SUBSET Key]
    /\ \A i,j \in Node : \A k \in Key : (k \in owner[i] /\ k \in owner[j]) => (i=j)
    /\ transfer_msg = {}
    \* No lost keys assumption: every key is owned by some node.
    /\ \A k \in Key : \E n \in Node : k \in owner[n]
    \* Initial ghost variables + event queue.
    /\ ghost_table = [k \in Key |-> Nil]
    /\ event_queue = {}

Spec == 
    /\ Init 
    /\ [][Next]_vars
    /\ SF_vars(Next)
    /\ \A n\in Node, k\in Key : SF_vars(\E v \in Value : RecvTransferMsg(n,k,v))


\* <properties>
\* Keys unique.
Safety == 
    /\ \A n1,n2 \in Node, k \in Key, v1,v2 \in Value : 
        (table[<<n1,k>>]=v1 /\ table[<<n2,k>>]=v2) => (n1=n2 /\ v1=v2)

Temporal ==
    /\ []<> (event_queue = {})
    /\ []<> (event_queue # {})
    /\ \A k \in Key, n_old, n_new \in Node : 
        [] (<<GIVE, k, n_old, n_new>> \in event_queue 
            => (<> (k \in owner[n_new])))
    /\ \A k \in Key : [] (<> \E n \in Node : (k \in owner[n]))
    /\ \A k \in Key : [] (ghost_table[k] # Nil =>
        <> \E n \in Node : ghost_table[k] = table[<<n,k>>])
\* </properties>

Symmetry == Permutations(Key) \cup Permutations(Value) \cup Permutations(Node)

====
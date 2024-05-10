---- MODULE sharded_kv ----
EXTENDS TLC, Randomization

CONSTANT Key
CONSTANT Value
CONSTANT Node

CONSTANT Nil
\* Need a non-Nil default
CONSTANT Def

\* The key-value store state on each node.
VARIABLE table

\* The set of keys owned by each node.
VARIABLE owner

\* The set of active transfer messages.
VARIABLE transfer_msg

vars == <<table,owner,transfer_msg>>

\* <actions>

Reshard(k,v,n_old,n_new) ==
    \* /\ FALSE \* Figure out why this is ok
    \* /\ k \in owner[n_new] \* Figure out why this is ok
    /\ table[<<n_old,k>>] = v
    \* /\ table' = [table EXCEPT ![n_old] = [table[n_old] EXCEPT ![k] = Nil]]
    /\ table' = [table EXCEPT ![<<n_old,k>>] = Nil]
    /\ owner' = [owner EXCEPT ![n_old] = owner[n_old] \ {k}]
    /\ transfer_msg' = transfer_msg \cup {<<n_new,k,v>>}

RecvTransferMsg(n, k, v) ==
    /\ <<n,k,v>> \in transfer_msg
    /\ transfer_msg' = transfer_msg \ {<<n,k,v>>}
    \* /\ table' = [table EXCEPT ![n] = [table[n] EXCEPT ![k] = v]]
    /\ table' = [table EXCEPT ![<<n,k>>] = v]
    \* Become the owner of this key.
    /\ owner' = [owner EXCEPT ![n] = owner[n] \cup {k}]

Put(n, k, v) == 
    /\ k \in owner[n]
    \* /\ table' = [table EXCEPT ![n] = [table[n] EXCEPT ![k] = v]]
    /\ table' = [table EXCEPT ![<<n,k>>] = v]
    /\ UNCHANGED <<owner, transfer_msg>>

\* </actions>

\* TODO: add a ghost table and a ghost owner variable. Then have a scheduler
\* that changes these things non-deterministically.

Next == 
    \/ \E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new)
    \/ \E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v)
    \/ \E n \in Node, k \in Key, v \in Value : Put(n,k,v)

Init == 
    \* /\ table = [n \in Node |-> [k \in Key |-> Nil]]
    \* Assume that owners write non-Nil Def to their keys.
    /\ transfer_msg = {}
    \* Each node owns some subset of keys, and different nodes
    \* can't own the same key.
    /\ owner \in [Node -> SUBSET Key]
    /\ table = [<<n,k>> \in Node \X Key |-> IF k \in owner[n] THEN Def ELSE Nil]
    /\ \A i,j \in Node : \A k \in Key : (k \in owner[i] /\ k \in owner[j]) => (i=j)
    \* No lost keys assumption: every key is owned by some node.
    /\ \A k \in Key : \E n \in Node : k \in owner[n]

Spec == 
    /\ Init 
    /\ [][Next]_vars
    /\ \A k \in Key : 
        SF_vars(\E n \in Node, v \in Value : RecvTransferMsg(n,k,v))
    /\ \A v \in Value : 
        SF_vars(\E n \in Node, k \in Key : Put(n,k,v))
    /\ \A n_old \in Node, k \in Key :
            SF_vars(\E n_new \in Node, v \in Value : 
                Reshard(k,v,n_old,n_new))

\* invariant [safety] (exists N,K,V. transfer_msg(N,K,V)) | (forall K. exists N. owner(N,K))
Safety == 
    /\ \A n1,n2 \in Node, k \in Key, v1,v2 \in Value : 
        (table[<<n1,k>>]=v1 /\ table[<<n2,k>>]=v2) => (n1=n2 /\ v1=v2)
    /\ \A n \in Node, k \in Key : k \in owner[n] => table[<<n,k>>] # Nil

Temporal == 
    /\ [] \A k \in Key : <>(\E n \in Node : k \in owner[n])
    \* The table isn't arbitarily frozen.
    /\ <> \E n \in Node, k \in Key, v \in Value \ {Def} : table[<<n,k>>] = v
    \* A node does not own a key indefinitely.
    /\ \A n \in Node, k \in Key : <> (k \notin owner[n])


Symmetry == Permutations(Key) \cup Permutations(Value) \cup Permutations(Node)


====
---- MODULE OUM ----
EXTENDS Naturals, Sequences, TLC, Paxos

CONSTANTS
  ClientRequest   \* abstract token for a client request

VARIABLES
  seqNo,           \* next sequence number to assign
  pending,         \* set of records [ req |-> ClientRequest, seq |-> seqNo ]
  delivered        \* map: Acceptor -> SUBSET of sequence numbers

================================================================================
InitOUM ==
  /\ seqNo     = 0
  /\ pending   = {} 
  /\ delivered = [ a \in Acceptor |-> {} ]

OUMSend(req) ==
  /\ seqNo'    = seqNo + 1
  /\ pending'  = pending \cup { [ req |-> req, seq |-> seqNo' ] }
  /\ UNCHANGED delivered

OUMDeliver ==
  ∃ r ∈ pending :
    LET s == r.seq IN
      ∃ S ∈ SUBSET Acceptor :
        /\ S ≠ {} 
        /\ delivered' =
             [ a ∈ Acceptor |-> 
                 IF a ∈ S 
                 THEN delivered[a] ∪ {s}
                 ELSE delivered[a]
             ]
        /\ pending' = pending \ {r}

NextOUM == OUMSend(ClientRequest) \/ OUMDeliver

SpecOUM == InitOUM /\ [][NextOUM]_(<<seqNo, pending, delivered>>)
====

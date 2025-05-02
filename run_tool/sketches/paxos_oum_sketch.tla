---- MODULE PaxosOUM_Holed ----
EXTENDS Integers, Sequences, TLC

CONSTANTS
    Value,         \* Domain of values Paxos may choose
    Acceptor,      \* Set of acceptor IDs
    Quorum,        \* Set of quorums: subsets of Acceptor
    ClientRequest, \* Token for an OUM request
    MaxSeq         \* Upper bound on sequence numbers for OUM

ASSUME
  /\ \A Q \in Quorum : Q \subseteq Acceptor
  /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 /= {}
  /\ MaxSeq \in Nat

VARIABLES
  maxBal,    \* Paxos: highest promised ballot per acceptor
  maxVBal,   \* Paxos: highest accepted ballot per acceptor
  maxVal,    \* Paxos: value accepted at that ballot
  msgs,      \* Paxos: all messages sent
  seqNo,     \* OUM: next sequence number to assign
  pending,   \* OUM: set of pending requests
  delivered  \* OUM: map Acceptor -> SUBSET Nat

vars == << maxBal, maxVBal, maxVal, msgs, seqNo, pending, delivered >>

(***************************************************************************)
(* Initialization                                                           *)
(***************************************************************************)
Init ==
  /\ maxBal    = [ a \in Acceptor |-> -1 ]
  /\ maxVBal   = [ a \in Acceptor |-> -1 ]
  /\ maxVal    = [ a \in Acceptor |-> CHOOSE v : v \notin Ballot ]
  /\ msgs      = {}
  /\ seqNo     = 0
  /\ pending   = {}
  /\ delivered = [ a \in Acceptor |-> {} ]

(***************************************************************************)
(* Paxos “holes”                                                            *)
(***************************************************************************)
Phase1a(b) ==
  /\ HOLE_Ph1a(b)
  /\ Send([ type  |-> "1a", bal |-> b ])
  /\ UNCHANGED vars

Phase1b(a) ==
  /\ HOLE_Ph1b(a)
  /\ Send([ type  |-> "1b",
            acc   |-> a,
            bal   |-> b,
            mbal  |-> mb,
            mval  |-> mv ])
  /\ UNCHANGED vars

Phase2a(b, v) ==
  /\ HOLE_Ph2a(b, v)
  /\ Send([ type  |-> "2a", bal |-> b, val |-> v ])
  /\ UNCHANGED vars

Phase2b(a) ==
  /\ HOLE_Ph2b(a)
  /\ Send([ type  |-> "2b",
            acc   |-> a,
            bal   |-> b,
            val   |-> v ])
  /\ UNCHANGED vars

(***************************************************************************)
(* Paxos send helper                                                        *)
(***************************************************************************)
Send(m) == msgs' = msgs \cup { m }

(***************************************************************************)
(* OUM definitions                                                          *)
(***************************************************************************)
OUMSend(req) ==
  /\ seqNo < MaxSeq
  /\ seqNo'   = seqNo + 1
  /\ pending' = pending \cup { [ req |-> req, seq |-> seqNo' ] }
  /\ UNCHANGED << maxBal, maxVBal, maxVal, msgs, delivered >>

OUMDeliver ==
  \E r \in pending :
    LET s == r.seq IN
      \E S \in SUBSET Acceptor :
        /\ S /= {}
        /\ delivered' = [ a \in Acceptor |-> 
             IF a \in S THEN delivered[a] \cup { s }
                        ELSE delivered[a] ]
        /\ pending'   = pending \ { r }
        /\ UNCHANGED << maxBal, maxVBal, maxVal, msgs, seqNo >>

OUMNext == OUMSend(ClientRequest) \/ OUMDeliver

(***************************************************************************)
(* Combined Next                                                             *)
(***************************************************************************)
Next ==
  \/ Phase1a(_)
  \/ Phase1b(_)
  \/ Phase2a(_, _)
  \/ Phase2b(_)
  \/ OUMNext

(***************************************************************************)
(* Specification                                                             *)
(***************************************************************************)
Spec == Init /\ [][ Next ]_vars

====  

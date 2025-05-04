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
  /\ Send([ type  |-> "1a", bal |-> b ])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

Phase1b(a) ==
  /\ \E m \in msgs :
    /\ m.type = "1a"
    /\ m.bal > maxBal[a]
    /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
    /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal,
             mbal |-> maxVBal[a], mval |-> maxVal[a]])
  /\ UNCHANGED <<maxVBal, maxVal>>

Phase2a(b, v) ==
  /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b
  /\ \E Q \in Quorum :
      LET Q1b == {m \in msgs : /\ m.type = "1b"
                               /\ m.acc \in Q
                               /\ m.bal = b}
          Q1bv == {m \in Q1b : m.mbal >= 0}
      IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
          /\ \/ Q1bv = {}
             \/ \E m \in Q1bv :
                /\ m.mval = v
                /\ \A mm \in Q1bv : m.mbal >= mm.mbal
  /\ Send([ type  |-> "2a", bal |-> b, val |-> v ])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

Phase2b(a) ==
   \E m \in msgs :
       /\ m.type = "2a"
       /\ __SafeAt__ \* gt: m.bal >= maxBal[a]
       /\ m.bal >= maxBal[a]
       /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
       /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
       /\ maxVal' = [maxVal EXCEPT ![a] = m.val]
       /\ Send([type |-> "2b", acc |-> a,
               bal |-> m.bal, val |-> m.val])
`
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

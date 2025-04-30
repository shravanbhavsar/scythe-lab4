---- MODULE OUM ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Acceptor, ClientRequest

VARIABLES seqNo, delivered, pending

InitOUM ==
  /\ seqNo    = 0
  /\ pending  = {}
  /\ delivered = [a \in Acceptor |-> {}]

\* Associate each multicast with next seqNo
OUMSend(req) ==
  /\ seqNo' = seqNo + 1
  /\ pending' = pending ∪ {[req |-> seqNo']}
  /\ UNCHANGED delivered

\* Deliver next sequence to a subset S of acceptors
OUMDeliver ==
  \E req \in DOMAIN pending :
    LET s == pending[req] IN
      /\ \* Choose any subset S (possibly all) to deliver
         \E S \subseteq Acceptor : 
           delivered' = [delivered EXCEPT ![a] = delivered[a] ∪ {s} 
                         FOR a \in S]
      /\ pending' = pending \ {req}

NextOUM == OUMSend(ClientRequest) ∨ OUMDeliver
SpecOUM == InitOUM /\ [][NextOUM]_(<<seqNo, pending, delivered>>)
====

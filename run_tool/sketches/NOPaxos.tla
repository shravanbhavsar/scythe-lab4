---- MODULE NOPaxos_Sketch ----
EXTENDS Paxos, OUM

VARIABLES maxBal, maxVBal, maxVal, msgs, seqNo, pending, delivered

Init == Paxos!Init /\ OUM!InitOUM

Phase1a(b) ==
  /\ HOLE_Ph1a(b)
  /\ Send([type |-> "1a", bal |-> b])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal, msgs, seqNo, pending, delivered>>

Phase2a(b, v) ==
  /\ ~(\E m \in msgs: m.type="2a" /\ m.bal=b)
  /\ HOLE_Safe(b, v, delivered)
  /\ Send([type |-> "2a", bal|-> b, val|-> v])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal, msgs, seqNo, pending, delivered>>

\* Phase1b, Phase2b unchanged from Paxos

Phase1b(a) == /\ \E m \in msgs : 
                  /\ m.type = "1a"
                  /\ m.bal > maxBal[a]
                  /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
                  /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal, 
                            mbal |-> maxVBal[a], mval |-> maxVal[a]])
              /\ UNCHANGED <<maxVBal, maxVal>>

Phase2b(a) == \E m \in msgs : /\ m.type = "2a"
                              /\ m.bal \geq maxBal[a]
                              /\ maxBal' = [maxBal EXCEPT ![a] = m.bal] 
                              /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal] 
                              /\ maxVal' = [maxVal EXCEPT ![a] = m.val]
                              /\ Send([type |-> "2b", acc |-> a,
                                       bal |-> m.bal, val |-> m.val]) 

Next == \/ \E b \in Ballot: Phase1a(b) ∨ \E v \in Value: Phase2a(b,v)
        \/ Paxos!Phase1b(a) \/ Paxos!Phase2b(a) 
        \/ OUM!NextOUM

InvSafety == Paxos!InvSafety

Spec == Init /\ [][Next]_<<maxBal,maxVBal,maxVal,msgs,seqNo,pending,delivered>>
====

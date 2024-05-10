---- MODULE consensus_epr_IndProofs ----
\* configindex: 624

EXTENDS consensus_epr

\* Original safety property.
SafetyCore ==
    /\ \A n1,n2 \in Node, v1,v2 \in Value : 
        (v1 \in decided[n1] /\ v2 \in decided[n2]) => (v1 = v2)

TypeOK == 
    /\ vote_request_msg \in SUBSET(Node \X Node)
    /\ voted \in [Node -> BOOLEAN]
    /\ vote_msg \in SUBSET(Node \X Node)
    /\ votes \in [Node -> SUBSET Node]
    /\ leader \in [Node -> BOOLEAN]
    /\ decided \in [Node -> SUBSET Value]

\* Inductive strengthening conjuncts
Inv119_1_0_def == \A VARI \in Node : \A VARJ \in Node : (<<VARJ,VARI>> \in vote_msg) \/ (~(VARJ \in votes[VARI]))
Inv152_1_1_def == \A VARI \in Node : \E QJ \in Quorum : \A VALI \in Value : (QJ \subseteq votes[VARI]) \/ (~(VALI \in decided[VARI]))
Inv693_1_2_def == \A VARI \in Node : \A VARJ \in Node : (voted[VARI]) \/ (~(<<VARI,VARJ>> \in vote_msg))
Inv164_1_3_def == \A VARI \in Node : \E QJ \in Quorum : (QJ \subseteq votes[VARI]) \/ (~(leader[VARI]))
Inv622_1_4_def == \A VARI \in Node : \A VALI \in Value : (leader[VARI]) \/ (~(VALI \in decided[VARI]))
Inv4302_2_0_def == \A VARI \in Node : \A VARJ \in Node : \A VARK \in Node : (VARI = VARK /\ votes = votes) \/ (~(<<VARJ,VARI>> \in vote_msg)) \/ (~(VARJ \in votes[VARK]))
Inv5288_2_0_def == \A VARI \in Node : \A VARJ \in Node : \A VARK \in Node : (VARJ = VARK /\ votes = votes) \/ (~(<<VARI,VARK>> \in vote_msg)) \/ (~(<<VARI,VARJ>> \in vote_msg))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ SafetyCore
  /\ Inv119_1_0_def
  /\ Inv152_1_1_def
  /\ Inv693_1_2_def
  /\ Inv164_1_3_def
  /\ Inv622_1_4_def
  /\ Inv4302_2_0_def
  /\ Inv5288_2_0_def
  

ASSUME QuorumsAreNodePowersets == Quorum \subseteq SUBSET Node
ASSUME EmptyNotInQuorums == {} \notin Quorum \* because quorums are majority sets
ASSUME QuorumsOverlap == \A Q1,Q2 \in Quorum : Q1 \cap Q2 # {}
ASSUME Fin == IsFiniteSet(Node)
ASSUME NodeNonEmpty == Node # {}
ASSUME QuorumsNonEmpty == Quorum # {}
ASSUME NodeQuorumType == Fin /\ NodeNonEmpty /\ QuorumsAreNodePowersets /\ EmptyNotInQuorums /\ QuorumsNonEmpty

\* TLAPS Proof skeleton.
THEOREM Init => IndAuto 
  <1> SUFFICES ASSUME Init
               PROVE  IndAuto
    OBVIOUS
  <1>1. TypeOK
    BY DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
    SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
  <1>2. SafetyCore
    BY DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
    SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
  <1>3. Inv119_1_0_def
    BY DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
    SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
  <1>4. Inv152_1_1_def
    BY Fin, NodeNonEmpty,QuorumsAreNodePowersets,NodeQuorumType DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def
  <1>5. Inv693_1_2_def
    BY DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def
  <1>6. Inv164_1_3_def
    BY Fin, NodeNonEmpty, QuorumsNonEmpty DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def
  <1>7. Inv622_1_4_def
    BY DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
    SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
  <1>8. Inv4302_2_0_def
    BY DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
    SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
  <1>9. Inv5288_2_0_def
    BY DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
    SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
  <1>10. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9 DEF IndAuto
  

THEOREM IndAuto /\ Next => IndAuto'
  <1> SUFFICES ASSUME IndAuto /\ Next
               PROVE  IndAuto'
    OBVIOUS
  <1>1. TypeOK'
    <2>0. CASE \E i,j \in Node : IgnoreRequestVote(i,j)
      BY <2>0 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      IgnoreRequestVote,SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>1. CASE \E i,j \in Node : SendRequestVote(i,j)
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>2. CASE \E i,j \in Node : SendVote(i,j)
      BY <2>2 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>3. CASE \E i,j \in Node : RecvVote(i,j)
      BY <2>3 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>4. CASE \E i \in Node, Q \in Quorum : BecomeLeader(i,Q)
      BY <2>4 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>5. CASE \E i,j \in Node, v \in Value : Decide(i,v)
      BY <2>5 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>6. QED
      BY <2>0, <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next, ProtocolNext, OtherNext
    
  <1>2. SafetyCore'
    <2>0. CASE \E i,j \in Node : IgnoreRequestVote(i,j)
      BY <2>0 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      IgnoreRequestVote,SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>1. CASE \E i,j \in Node : SendRequestVote(i,j)
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>2. CASE \E i,j \in Node : SendVote(i,j)
      BY <2>2 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>3. CASE \E i,j \in Node : RecvVote(i,j)
      BY <2>3 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>4. CASE \E i \in Node, Q \in Quorum : BecomeLeader(i,Q)
      BY <2>4 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>5. CASE \E i,j \in Node, v \in Value : Decide(i,v)
        <3>. PICK i \in Node, v \in Value : Decide(i,v) BY <2>5 DEF IndAuto,Next
        <3>. SUFFICES ASSUME NEW i2 \in Node,
                              NEW v2 \in Value,
                              v2 \in decided[i2]',
                              v2 # v 
                              PROVE FALSE
                              BY DEF IndAuto,Next,SafetyCore
        <3>3. leader[i] BY DEF IndAuto,Next,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,Decide
        <3>4. leader'[i] BY DEF IndAuto,Next,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,Decide
        <3>5. CASE i2 = i
            <4>1. v2 \in decided[i2] BY <3>5 DEF IndAuto,Next,Decide
            <4>2. decided[i2] = {} BY <3>5 DEF IndAuto,Next,Decide
            <4>3. QED BY <3>5,<4>2, <4>1
        <3>6. CASE i2 # i
            <4>. v2 \in decided[i2] BY DEF IndAuto,Next,Decide
            <4>. PICK Q2 \in Quorum : (Q2 \subseteq votes[i2]) BY DEF 
                IndAuto,TypeOK,Next,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def
            <4>. v \in decided'[i] BY DEF IndAuto, TypeOK,Decide, Next
            <4>. leader[i] BY DEF IndAuto, TypeOK,Decide, Next
            <4>. PICK Q \in Quorum : (Q \subseteq votes[i]) BY DEF 
             IndAuto,TypeOK,Next,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def
            <4>. PICK ix \in Node : ix \in (Q2 \cap Q) BY QuorumsOverlap DEF IndAuto, TypeOK, NodeQuorumType
            <4>. ix \in votes[i] OBVIOUS
            <4>. ix \in votes[i2] OBVIOUS
            <4>. <<ix,i>> \in vote_msg BY DEF IndAuto, Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def
            <4>. <<ix,i2>> \in vote_msg BY DEF IndAuto,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def
            <4>. <<ix,i>> \in vote_msg /\ <<ix,i2>> \in vote_msg /\ i # i2 BY <3>6
            <4>. voted[ix] BY DEF IndAuto,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def
            <4>. QED BY DEF IndAuto,TypeOK,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def
        <3>9. QED BY <3>5,<3>6

    <2>6. QED
      BY <2>0, <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next,ProtocolNext,OtherNext
      
  <1>3. Inv119_1_0_def'
    <2>0. CASE \E i,j \in Node : IgnoreRequestVote(i,j)
      BY <2>0 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      IgnoreRequestVote,SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>1. CASE \E i,j \in Node : SendRequestVote(i,j)
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>2. CASE \E i,j \in Node : SendVote(i,j)
      BY <2>2 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>3. CASE \E i,j \in Node : RecvVote(i,j)
      <3> SUFFICES ASSUME NEW VARI \in Node',
                          NEW VARJ \in Node'
                   PROVE  ((<<VARJ,VARI>> \in vote_msg) \/ (~(VARJ \in votes[VARI])))'
        BY DEF Inv119_1_0_def
      <3> QED
        BY <2>3,NodeQuorumType DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
        SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
      
    <2>4. CASE \E i \in Node, Q \in Quorum : BecomeLeader(i,Q)
      BY <2>4 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>5. CASE \E i,j \in Node, v \in Value : Decide(i,v)
      BY <2>5 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>6. QED
      BY <2>0,<2>1, <2>2, <2>3, <2>4, <2>5 DEF Next,ProtocolNext,OtherNext
    
  <1>4. Inv152_1_1_def'
    <2>0. CASE \E i,j \in Node : IgnoreRequestVote(i,j)
      BY <2>0 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      IgnoreRequestVote,SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>1. CASE \E i,j \in Node : SendRequestVote(i,j)
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>2. CASE \E i,j \in Node : SendVote(i,j)
      BY <2>2 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>3. CASE \E i,j \in Node : RecvVote(i,j)
      BY <2>3 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>4. CASE \E i \in Node, Q \in Quorum : BecomeLeader(i,Q)
      BY <2>4 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>5. CASE \E i,j \in Node, v \in Value : Decide(i,v)
      BY <2>5 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>6. QED
      BY <2>0,<2>1, <2>2, <2>3, <2>4, <2>5 DEF Next,ProtocolNext,OtherNext
    
  <1>5. Inv693_1_2_def'
    <2>1. CASE \E i,j \in Node : SendVote(i,j)
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      IgnoreRequestVote, SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide,ProtocolNext,OtherNext
    <2>2. CASE \E i,j \in Node : IgnoreRequestVote(i,j)
      BY <2>2 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      IgnoreRequestVote, SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide,ProtocolNext,OtherNext
    <2>3. CASE \E i,j \in Node : RecvVote(i,j)
      BY <2>3 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      IgnoreRequestVote, SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide,ProtocolNext,OtherNext
    <2>4. CASE \E i \in Node, Q \in Quorum : BecomeLeader(i,Q)
      BY <2>4 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      IgnoreRequestVote, SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide,ProtocolNext,OtherNext
    <2>5. CASE \E i,j \in Node, v \in Value : Decide(i,v)
      BY <2>5 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      IgnoreRequestVote, SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide,ProtocolNext,OtherNext
    <2>6. ASSUME NEW i \in Node,
                 NEW j \in Node,
                 SendRequestVote(i,j)
          PROVE  Inv693_1_2_def'
      BY <2>6 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      IgnoreRequestVote, SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide,ProtocolNext,OtherNext
    <2>7. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Next, OtherNext, ProtocolNext
    
  <1>6. Inv164_1_3_def'
    <2>0. CASE \E i,j \in Node : IgnoreRequestVote(i,j)
      BY <2>0 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      IgnoreRequestVote,SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>1. CASE \E i,j \in Node : SendRequestVote(i,j)
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>2. CASE \E i,j \in Node : SendVote(i,j)
      BY <2>2 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>3. CASE \E i,j \in Node : RecvVote(i,j)
      BY <2>3 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>4. CASE \E i \in Node, Q \in Quorum : BecomeLeader(i,Q)
      BY <2>4 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>5. CASE \E i,j \in Node, v \in Value : Decide(i,v)
      BY <2>5 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>6. QED
      BY <2>0, <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next,ProtocolNext,OtherNext
    
  <1>7. Inv622_1_4_def'
    <2>0. CASE \E i,j \in Node : IgnoreRequestVote(i,j)
      BY <2>0 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      IgnoreRequestVote,SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>1. CASE \E i,j \in Node : SendRequestVote(i,j)
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>2. CASE \E i,j \in Node : SendVote(i,j)
      BY <2>2 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>3. CASE \E i,j \in Node : RecvVote(i,j)
      BY <2>3 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>4. CASE \E i \in Node, Q \in Quorum : BecomeLeader(i,Q)
      BY <2>4 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>5. CASE \E i,j \in Node, v \in Value : Decide(i,v)
      BY <2>5 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>6. QED
      BY <2>0, <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next,ProtocolNext,OtherNext
    
  <1>8. Inv4302_2_0_def'
    <2>0. CASE \E i,j \in Node : IgnoreRequestVote(i,j)
      BY <2>0 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      IgnoreRequestVote,SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>1. CASE \E i,j \in Node : SendRequestVote(i,j)
      BY <2>1 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>2. CASE \E i,j \in Node : SendVote(i,j)
      BY <2>2 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>3. CASE \E i,j \in Node : RecvVote(i,j)
      <3> SUFFICES ASSUME NEW VARI \in Node',
                          NEW VARJ \in Node'
                   PROVE  (\A VARK \in Node : (VARI = VARK /\ votes = votes) \/ (~(<<VARJ,VARI>> \in vote_msg)) \/ (~(VARJ \in votes[VARK])))'
        BY DEF Inv4302_2_0_def
      <3> QED
        BY <2>3 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
  SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
      
    <2>4. CASE \E i \in Node, Q \in Quorum : BecomeLeader(i,Q)
      BY <2>4 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>5. CASE \E i,j \in Node, v \in Value : Decide(i,v)
      BY <2>5 DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
      SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide
    <2>6. QED
      BY <2>0, <2>1, <2>2, <2>3, <2>4, <2>5 DEF Next,ProtocolNext,OtherNext
    
  <1>9. Inv5288_2_0_def'
    BY DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv119_1_0_def,Inv152_1_1_def,Inv693_1_2_def,Inv164_1_3_def,Inv622_1_4_def,Inv4302_2_0_def,Inv5288_2_0_def,
    IgnoreRequestVote,SendRequestVote,SendVote,RecvVote,BecomeLeader,Decide,ProtocolNext,OtherNext
  <1>10. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9 DEF IndAuto



====
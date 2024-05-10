---- MODULE sharded_kv_IndProofs ----
\* configindex: 302
EXTENDS sharded_kv, FiniteSetTheorems

TypeOK ==
    /\ table \in [Node -> [Key -> Value \cup {Nil}]]
    /\ owner \in [Node -> SUBSET Key]
    /\ transfer_msg \in SUBSET (Node \times Key \times Value)


\* Inductive strengthening conjuncts
Inv238_1_0_def == \A NI \in Node : \A NJ \in Node : \A KI \in Key : \A VALI \in Value : ~(<<NI,KI,VALI>> \in transfer_msg) \/ (~(KI \in owner[NJ]))
Inv114_1_1_def == \A NJ \in Node : \A KI \in Key : (KI \in owner[NJ]) \/ ((table[NJ][KI] = Nil))
Inv1376_2_2_def == \A NI \in Node : \A NJ \in Node : \A KI \in Key : (NI = NJ /\ owner = owner) \/ (~(KI \in owner[NI])) \/ (~(KI \in owner[NJ]))
Inv1336_2_0_def == \A NI \in Node : \A NJ \in Node : \A KI \in Key : \A VALI \in Value : \A VALJ \in Value : (NI = NJ /\ owner = owner) \/ (~(<<NI,KI,VALJ>> \in transfer_msg) \/ (~(<<NJ,KI,VALI>> \in transfer_msg)))
Inv1476_2_1_def == \A NI \in Node : \A KI \in Key : \A VALI \in Value : \A VALJ \in Value : (VALI = VALJ /\ owner = owner) \/ (~(<<NI,KI,VALJ>> \in transfer_msg)) \/ (~(<<NI,KI,VALI>> \in transfer_msg))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ Safety
  /\ Inv238_1_0_def
  /\ Inv114_1_1_def
  /\ Inv1376_2_2_def
  /\ Inv1336_2_0_def
  /\ Inv1476_2_1_def

ASSUME Fin == IsFiniteSet(Node) /\ IsFiniteSet(Key) /\ IsFiniteSet(Value)
ASSUME NilType == Nil \notin Node /\ Nil \notin Key /\ Nil \notin Value
ASSUME NodeNonEmpty == Node # {}


\* TLAPS Proof skeleton.
THEOREM Init => IndAuto 
  <1> SUFFICES ASSUME Init
               PROVE  IndAuto
    OBVIOUS
  <1>1. TypeOK
    BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv238_1_0_def,Inv114_1_1_def,Inv1376_2_2_def,Inv1336_2_0_def,Inv1476_2_1_def
  <1>2. Safety
    BY Fin, NilType DEF TypeOK,Init,Next,IndAuto,Safety,Inv238_1_0_def,Inv114_1_1_def,Inv1376_2_2_def,Inv1336_2_0_def,Inv1476_2_1_def
  <1>3. Inv238_1_0_def
    BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv238_1_0_def,Inv114_1_1_def,Inv1376_2_2_def,Inv1336_2_0_def,Inv1476_2_1_def
  <1>4. Inv114_1_1_def
    BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv238_1_0_def,Inv114_1_1_def,Inv1376_2_2_def,Inv1336_2_0_def,Inv1476_2_1_def
  <1>5. Inv1376_2_2_def
    BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv238_1_0_def,Inv114_1_1_def,Inv1376_2_2_def,Inv1336_2_0_def,Inv1476_2_1_def
  <1>6. Inv1336_2_0_def
    BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv238_1_0_def,Inv114_1_1_def,Inv1376_2_2_def,Inv1336_2_0_def,Inv1476_2_1_def
  <1>7. Inv1476_2_1_def
    BY DEF TypeOK,Init,Next,IndAuto,Safety,Inv238_1_0_def,Inv114_1_1_def,Inv1376_2_2_def,Inv1336_2_0_def,Inv1476_2_1_def
  <1>8. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7 DEF IndAuto
 

THEOREM IndAuto /\ Next => IndAuto'
  <1> SUFFICES ASSUME IndAuto /\ Next
               PROVE  IndAuto'
    OBVIOUS
  <1>1. TypeOK'
    <2>1. CASE \E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new)
      BY <2>1, Fin, NilType DEF TypeOK,Init,Next,IndAuto,Safety,Inv238_1_0_def,Inv114_1_1_def,Inv1376_2_2_def,Inv1336_2_0_def,Inv1476_2_1_def,Reshard,RecvTransferMsg,Put
    <2>2. CASE \E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v)
      BY <2>2, Fin, NilType DEF TypeOK,Init,Next,IndAuto,Safety,Inv238_1_0_def,Inv114_1_1_def,Inv1376_2_2_def,Inv1336_2_0_def,Inv1476_2_1_def,Reshard,RecvTransferMsg,Put
    <2>3. CASE \E n \in Node, k \in Key, v \in Value : Put(n,k,v)
      BY <2>3, Fin, NilType DEF TypeOK,Init,Next,IndAuto,Safety,Inv238_1_0_def,Inv114_1_1_def,Inv1376_2_2_def,Inv1336_2_0_def,Inv1476_2_1_def,Reshard,RecvTransferMsg,Put
    <2>4. QED
      BY <2>1, <2>2, <2>3 DEF Next
    
  <1>2. Safety'
    <2>1. CASE \E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new)
      BY <2>1, Fin, NilType DEF TypeOK,Init,Next,IndAuto,Safety,Inv238_1_0_def,Inv114_1_1_def,Inv1376_2_2_def,Inv1336_2_0_def,Inv1476_2_1_def,Reshard,RecvTransferMsg,Put
    <2>2. CASE \E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v)
      BY <2>2, Fin, NilType DEF TypeOK,Init,Next,IndAuto,Safety,Inv238_1_0_def,Inv114_1_1_def,Inv1376_2_2_def,Inv1336_2_0_def,Inv1476_2_1_def,Reshard,RecvTransferMsg,Put
    <2>3. CASE \E n \in Node, k \in Key, v \in Value : Put(n,k,v)
      BY <2>3, Fin, NilType DEF TypeOK,Init,Next,IndAuto,Safety,Inv238_1_0_def,Inv114_1_1_def,Inv1376_2_2_def,Inv1336_2_0_def,Inv1476_2_1_def,Reshard,RecvTransferMsg,Put
    <2>4. QED
      BY <2>1, <2>2, <2>3 DEF Next
    
  <1>3. Inv238_1_0_def'
    <2>1. CASE \E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new)
      <3> SUFFICES ASSUME NEW NI \in Node',
                          NEW NJ \in Node',
                          NEW KI \in Key',
                          NEW VALI \in Value'
                   PROVE  (~(<<NI,KI,VALI>> \in transfer_msg) \/ (~(KI \in owner[NJ])))'
        BY DEF Inv238_1_0_def
      <3> QED
        BY <2>1, Fin, NilType DEF TypeOK,Init,Next,IndAuto,Safety,Inv238_1_0_def,Inv114_1_1_def,Inv1376_2_2_def,Inv1336_2_0_def,Inv1476_2_1_def,Reshard,RecvTransferMsg,Put
      
    <2>2. CASE \E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v)
      <3> SUFFICES ASSUME NEW NI \in Node',
                          NEW NJ \in Node',
                          NEW KI \in Key',
                          NEW VALI \in Value'
                   PROVE  (~(<<NI,KI,VALI>> \in transfer_msg) \/ (~(KI \in owner[NJ])))'
        BY DEF Inv238_1_0_def
      <3> QED
        BY <2>2, Fin, NilType DEF TypeOK,Init,Next,IndAuto,Safety,Inv238_1_0_def,Inv114_1_1_def,Inv1376_2_2_def,Inv1336_2_0_def,Inv1476_2_1_def,Reshard,RecvTransferMsg,Put
      
    <2>3. CASE \E n \in Node, k \in Key, v \in Value : Put(n,k,v)
      BY <2>3, Fin, NilType DEF TypeOK,Init,Next,IndAuto,Safety,Inv238_1_0_def,Inv114_1_1_def,Inv1376_2_2_def,Inv1336_2_0_def,Inv1476_2_1_def,Reshard,RecvTransferMsg,Put
    <2>4. QED
      BY <2>1, <2>2, <2>3 DEF Next
    
  <1>4. Inv114_1_1_def'
    <2>1. CASE \E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new)
      BY <2>1, Fin, NilType DEF TypeOK,Init,Next,IndAuto,Safety,Inv238_1_0_def,Inv114_1_1_def,Inv1376_2_2_def,Inv1336_2_0_def,Inv1476_2_1_def,Reshard,RecvTransferMsg,Put
    <2>2. CASE \E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v)
      BY <2>2, Fin, NilType DEF TypeOK,Init,Next,IndAuto,Safety,Inv238_1_0_def,Inv114_1_1_def,Inv1376_2_2_def,Inv1336_2_0_def,Inv1476_2_1_def,Reshard,RecvTransferMsg,Put
    <2>3. CASE \E n \in Node, k \in Key, v \in Value : Put(n,k,v)
      BY <2>3, Fin, NilType DEF TypeOK,Init,Next,IndAuto,Safety,Inv238_1_0_def,Inv114_1_1_def,Inv1376_2_2_def,Inv1336_2_0_def,Inv1476_2_1_def,Reshard,RecvTransferMsg,Put
    <2>4. QED
      BY <2>1, <2>2, <2>3 DEF Next
    
  <1>5. Inv1376_2_2_def'
    <2>1. CASE \E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new)
      BY <2>1, Fin, NilType DEF TypeOK,Init,Next,IndAuto,Safety,Inv238_1_0_def,Inv114_1_1_def,Inv1376_2_2_def,Inv1336_2_0_def,Inv1476_2_1_def,Reshard,RecvTransferMsg,Put
    <2>2. CASE \E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v)
      BY <2>2, Fin, NilType DEF TypeOK,Init,Next,IndAuto,Safety,Inv238_1_0_def,Inv114_1_1_def,Inv1376_2_2_def,Inv1336_2_0_def,Inv1476_2_1_def,Reshard,RecvTransferMsg,Put
    <2>3. CASE \E n \in Node, k \in Key, v \in Value : Put(n,k,v)
      BY <2>3, Fin, NilType DEF TypeOK,Init,Next,IndAuto,Safety,Inv238_1_0_def,Inv114_1_1_def,Inv1376_2_2_def,Inv1336_2_0_def,Inv1476_2_1_def,Reshard,RecvTransferMsg,Put
    <2>4. QED
      BY <2>1, <2>2, <2>3 DEF Next
    
  <1>6. Inv1336_2_0_def'
    <2>1. CASE \E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new)
      BY <2>1, Fin, NilType DEF TypeOK,Init,Next,IndAuto,Safety,Inv238_1_0_def,Inv114_1_1_def,Inv1376_2_2_def,Inv1336_2_0_def,Inv1476_2_1_def,Reshard,RecvTransferMsg,Put
    <2>2. CASE \E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v)
      BY <2>2, Fin, NilType DEF TypeOK,Init,Next,IndAuto,Safety,Inv238_1_0_def,Inv114_1_1_def,Inv1376_2_2_def,Inv1336_2_0_def,Inv1476_2_1_def,Reshard,RecvTransferMsg,Put
    <2>3. CASE \E n \in Node, k \in Key, v \in Value : Put(n,k,v)
      BY <2>3, Fin, NilType DEF TypeOK,Init,Next,IndAuto,Safety,Inv238_1_0_def,Inv114_1_1_def,Inv1376_2_2_def,Inv1336_2_0_def,Inv1476_2_1_def,Reshard,RecvTransferMsg,Put
    <2>4. QED
      BY <2>1, <2>2, <2>3 DEF Next
    
  <1>7. Inv1476_2_1_def'
    BY Fin, NilType DEF TypeOK,Init,Next,IndAuto,Safety,Inv238_1_0_def,Inv114_1_1_def,Inv1376_2_2_def,Inv1336_2_0_def,Inv1476_2_1_def,Reshard,RecvTransferMsg,Put
  <1>8. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7 DEF IndAuto
 
====

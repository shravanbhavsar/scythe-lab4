---- MODULE simple_decentralized_lock_IndProofs ----
\* configindex: 486
EXTENDS simple_decentralized_lock, FiniteSets, FiniteSetTheorems

\* benchmark: ex-simple-decentralized-lock

TypeOK == 
    /\ message \in SUBSET (Node \X Node)
    /\ has_lock \in [Node -> BOOLEAN]

SafetyCore == Safety

\* Inductive strengthening conjuncts
Inv474_1_0_def == \A VARS \in Node : \A VART \in Node : \A VARU \in Node : \A VARV \in Node : ~(<<VARS,VART>> \in message) \/ (~(has_lock[VARU]))


\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ SafetyCore
  /\ Inv474_1_0_def

  
ASSUME NodeFin == IsFiniteSet(Node)
USE DEF Safety


\*\* TLAPS Proof skeleton.
THEOREM Init => IndAuto 
BY DEF TypeOK,Init,Next,IndAuto,SafetyCore,Inv474_1_0_def
 
THEOREM IndAuto /\ Next => IndAuto'
  <1> SUFFICES ASSUME IndAuto /\ Next
               PROVE  IndAuto'
    OBVIOUS
  <1>1. TypeOK'
    <2>1. (message \in SUBSET (Node \X Node))'
      BY DEF TypeOK,Init,Next,IndAuto,NextParam,SafetyCore,Inv474_1_0_def,Send,Recv
    <2>2. (has_lock \in [Node -> BOOLEAN])'
      BY DEF TypeOK,Init,Next,IndAuto,NextParam,SafetyCore,Inv474_1_0_def,Send,Recv
    <2>3. QED
      BY <2>1, <2>2 DEF TypeOK
    
  <1>2. SafetyCore'
    BY DEF TypeOK,Init,Next,IndAuto,NextParam,SafetyCore,Inv474_1_0_def,Send,Recv
  <1>3. Inv474_1_0_def'
    BY DEF TypeOK,Init,Next,IndAuto,NextParam,SafetyCore,Inv474_1_0_def,Send,Recv
  <1>4. QED
    BY <1>1, <1>2, <1>3 DEF IndAuto
  
    

  


====
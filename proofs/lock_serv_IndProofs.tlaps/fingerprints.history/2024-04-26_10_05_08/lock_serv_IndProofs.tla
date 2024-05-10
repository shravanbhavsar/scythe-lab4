---- MODULE lock_serv_IndProofs ----
\* table: https://github.com/egolf-cs/tla-synthesis/blob/0575612955b0ad69cd051edb41bf8eeec87b0e9c/tool_and_experimentation/reports/README.md
\* configindex: 599
\* eid: 16.17.19.5.6.9.8.7
EXTENDS lock_serv

SafetyCore == Mutex

TypeOK == 
    /\ lock_msg \in [Node -> BOOLEAN]
    /\ grant_msg \in [Node -> BOOLEAN]
    /\ unlock_msg \in [Node -> BOOLEAN]
    /\ holds_lock \in [Node -> BOOLEAN]
    /\ server_holds_lock \in BOOLEAN

\* Inductive strengthening conjuncts
Inv151_1_0_def == \A VARI \in Node : \A VARJ \in Node : ~(grant_msg[VARI]) \/ (~(unlock_msg[VARJ]))
Inv162_1_1_def == \A VARI \in Node : ~(holds_lock[VARI]) \/ (~(server_holds_lock))
Inv146_1_2_def == \A VARI \in Node : \A VARJ \in Node : ~(grant_msg[VARI]) \/ (~(holds_lock[VARJ]))
Inv164_1_3_def == \A VARI \in Node : \A VARJ \in Node : ~(holds_lock[VARI]) \/ (~(unlock_msg[VARJ]))
Inv149_1_4_def == \A VARI \in Node : ~(grant_msg[VARI]) \/ (~(server_holds_lock))
Inv177_1_5_def == \A VARI \in Node : ~(server_holds_lock) \/ (~(unlock_msg[VARI]))
Inv96_2_6_def == \A VARI \in Node : \A VARJ \in Node : (VARI=VARJ) \/ (~(grant_msg[VARJ])) \/ (~(grant_msg[VARI]))
Inv128_2_0_def == \A VARI \in Node : \A VARJ \in Node : (VARI=VARJ) \/ (~(unlock_msg[VARI]) \/ (~(unlock_msg[VARJ])))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ SafetyCore
  /\ Inv151_1_0_def
  /\ Inv162_1_1_def
  /\ Inv146_1_2_def
  /\ Inv164_1_3_def
  /\ Inv149_1_4_def
  /\ Inv177_1_5_def
  /\ Inv96_2_6_def
  /\ Inv128_2_0_def

\* TLAPS Proof skeleton.
THEOREM Init => IndAuto 
 BY DEF TypeOK,Init,Next,IndAuto,SafetyCore,Mutex,Inv151_1_0_def,Inv162_1_1_def,Inv146_1_2_def,Inv164_1_3_def,Inv149_1_4_def,Inv177_1_5_def,Inv96_2_6_def,Inv128_2_0_def

THEOREM IndAuto /\ Next => IndAuto'
  <1> SUFFICES ASSUME IndAuto /\ Next
               PROVE  IndAuto'
    OBVIOUS
  <1>1. TypeOK'
    BY DEF TypeOK,Init,Next,NextParam,IndAuto,SafetyCore,Mutex,Inv151_1_0_def,Inv162_1_1_def,Inv146_1_2_def,Inv164_1_3_def,Inv149_1_4_def,Inv177_1_5_def,Inv96_2_6_def,Inv128_2_0_def,
    SendLock,RecvLock,RecvGrant,Unlock,RecvUnlock
  <1>2. SafetyCore'
    BY DEF TypeOK,Init,Next,NextParam,IndAuto,SafetyCore,Mutex,Inv151_1_0_def,Inv162_1_1_def,Inv146_1_2_def,Inv164_1_3_def,Inv149_1_4_def,Inv177_1_5_def,Inv96_2_6_def,Inv128_2_0_def,Mutex,
    SendLock,RecvLock,RecvGrant,Unlock,RecvUnlock
  <1>3. Inv151_1_0_def'
    BY DEF TypeOK,Init,Next,NextParam,IndAuto,SafetyCore,Mutex,Inv151_1_0_def,Inv162_1_1_def,Inv146_1_2_def,Inv164_1_3_def,Inv149_1_4_def,Inv177_1_5_def,Inv96_2_6_def,Inv128_2_0_def,
    SendLock,RecvLock,RecvGrant,Unlock,RecvUnlock
  <1>4. Inv162_1_1_def'
    BY DEF TypeOK,Init,Next,NextParam,IndAuto,SafetyCore,Mutex,Inv151_1_0_def,Inv162_1_1_def,Inv146_1_2_def,Inv164_1_3_def,Inv149_1_4_def,Inv177_1_5_def,Inv96_2_6_def,Inv128_2_0_def,
    SendLock,RecvLock,RecvGrant,Unlock,RecvUnlock
  <1>5. Inv146_1_2_def'
    BY DEF TypeOK,Init,Next,NextParam,IndAuto,SafetyCore,Mutex,Inv151_1_0_def,Inv162_1_1_def,Inv146_1_2_def,Inv164_1_3_def,Inv149_1_4_def,Inv177_1_5_def,Inv96_2_6_def,Inv128_2_0_def,
    SendLock,RecvLock,RecvGrant,Unlock,RecvUnlock
  <1>6. Inv164_1_3_def'
    BY DEF TypeOK,Init,Next,NextParam,IndAuto,SafetyCore,Mutex,Inv151_1_0_def,Inv162_1_1_def,Inv146_1_2_def,Inv164_1_3_def,Inv149_1_4_def,Inv177_1_5_def,Inv96_2_6_def,Inv128_2_0_def,
    SendLock,RecvLock,RecvGrant,Unlock,RecvUnlock
  <1>7. Inv149_1_4_def'
    BY DEF TypeOK,Init,Next,NextParam,IndAuto,SafetyCore,Mutex,Inv151_1_0_def,Inv162_1_1_def,Inv146_1_2_def,Inv164_1_3_def,Inv149_1_4_def,Inv177_1_5_def,Inv96_2_6_def,Inv128_2_0_def,
    SendLock,RecvLock,RecvGrant,Unlock,RecvUnlock
  <1>8. Inv177_1_5_def'
    BY DEF TypeOK,Init,Next,NextParam,IndAuto,SafetyCore,Mutex,Inv151_1_0_def,Inv162_1_1_def,Inv146_1_2_def,Inv164_1_3_def,Inv149_1_4_def,Inv177_1_5_def,Inv96_2_6_def,Inv128_2_0_def,
    SendLock,RecvLock,RecvGrant,Unlock,RecvUnlock
  <1>9. Inv96_2_6_def'
    BY DEF TypeOK,Init,Next,NextParam,IndAuto,SafetyCore,Mutex,Inv151_1_0_def,Inv162_1_1_def,Inv146_1_2_def,Inv164_1_3_def,Inv149_1_4_def,Inv177_1_5_def,Inv96_2_6_def,Inv128_2_0_def,
    SendLock,RecvLock,RecvGrant,Unlock,RecvUnlock
  <1>10. Inv128_2_0_def'
    BY DEF TypeOK,Init,Next,NextParam,IndAuto,SafetyCore,Mutex,Inv151_1_0_def,Inv162_1_1_def,Inv146_1_2_def,Inv164_1_3_def,Inv149_1_4_def,Inv177_1_5_def,Inv96_2_6_def,Inv128_2_0_def,
    SendLock,RecvLock,RecvGrant,Unlock,RecvUnlock
  <1>11. QED
    BY <1>1, <1>10, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9 DEF IndAuto


====
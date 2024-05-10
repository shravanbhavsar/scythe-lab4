---- MODULE two_phase_commit_IndProofs ----
\* benchmark: i4-two-phase-commit
\* configindex: 513
EXTENDS two_phase_commit

TypeOK ==
    /\ vote_yes \in SUBSET Node
    /\ vote_no \in SUBSET Node
    /\ alive \in SUBSET Node
    /\ go_commit \in SUBSET Node
    /\ go_abort \in SUBSET Node
    /\ decide_commit \in SUBSET Node
    /\ decide_abort \in SUBSET Node
    /\ abort_flag \in BOOLEAN 
    /\ compatible \in SUBSET Node 

SafetyCore == 
    /\ \A n,n2 \in Node : (n \in decide_commit) => (n2 \notin decide_abort) 


\* Inductive strengthening conjuncts
Inv913_1_0_def == \A VARI \in Node : \A VARJ \in Node : (go_abort = {}) \/ ((go_commit = {}))
Inv1214_1_1_def == \A VARI \in Node : \A VARJ \in Node : ~(VARI \in vote_no) \/ (~(VARI \in vote_yes))
Inv134_1_2_def == \A VARI \in Node : \A VARJ \in Node : (VARI \in compatible) \/ (~(VARI \in vote_yes))
Inv909_1_3_def == \A VARI \in Node : \A VARJ \in Node : (decide_commit = {}) \/ (~(go_commit = {}))
Inv877_1_4_def == \A VARI \in Node : \A VARJ \in Node : (decide_abort = {}) \/ (~(go_abort = {}))
Inv1107_1_0_def == \A VARI \in Node : \A VARJ \in Node : ~(VARI \in compatible) \/ (~(VARI \in vote_no))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ SafetyCore
  /\ Inv913_1_0_def
  /\ Inv1214_1_1_def
  /\ Inv134_1_2_def
  /\ Inv909_1_3_def
  /\ Inv877_1_4_def
  /\ Inv1107_1_0_def

\* TLAPS Proof skeleton.
THEOREM Init => IndAuto 
 BY DEF TypeOK,Init,Next,IndAuto,Safety,SafetyCore,Inv913_1_0_def,Inv1214_1_1_def,Inv134_1_2_def,Inv909_1_3_def,Inv877_1_4_def,Inv1107_1_0_def

THEOREM IndAuto /\ Next => IndAuto'
  <1> SUFFICES ASSUME IndAuto,
                      Next
               PROVE  IndAuto'
    OBVIOUS
  <1>1. CASE \E n \in Node : Vote1(n)
    BY <1>1 DEF Vote1,Vote2,Fail,Go1,Go2,Commit,Abort,TypeOK,Init,Next,OpNext,OtherNext,Termination,IndAuto,SafetyCore,Inv913_1_0_def,Inv1214_1_1_def,Inv134_1_2_def,Inv909_1_3_def,Inv877_1_4_def,Inv1107_1_0_def
  <1>2. CASE \E n \in Node : Vote2(n)
    BY <1>2 DEF Vote1,Vote2,Fail,Go1,Go2,Commit,Abort,TypeOK,Init,Next,OpNext,OtherNext,Termination,IndAuto,SafetyCore,Inv913_1_0_def,Inv1214_1_1_def,Inv134_1_2_def,Inv909_1_3_def,Inv877_1_4_def,Inv1107_1_0_def
  <1>3. CASE Go1
    BY <1>3 DEF Vote1,Vote2,Fail,Go1,Go2,Commit,Abort,TypeOK,Init,Next,OpNext,OtherNext,Termination,IndAuto,SafetyCore,Inv913_1_0_def,Inv1214_1_1_def,Inv134_1_2_def,Inv909_1_3_def,Inv877_1_4_def,Inv1107_1_0_def
  <1>4. CASE Go2
    BY <1>4 DEF Vote1,Vote2,Fail,Go1,Go2,Commit,Abort,TypeOK,Init,Next,OpNext,OtherNext,Termination,IndAuto,SafetyCore,Inv913_1_0_def,Inv1214_1_1_def,Inv134_1_2_def,Inv909_1_3_def,Inv877_1_4_def,Inv1107_1_0_def
  <1>5. CASE \E n \in Node : Commit(n)
    BY <1>5 DEF Vote1,Vote2,Fail,Go1,Go2,Commit,Abort,TypeOK,Init,Next,OpNext,OtherNext,Termination,IndAuto,SafetyCore,Inv913_1_0_def,Inv1214_1_1_def,Inv134_1_2_def,Inv909_1_3_def,Inv877_1_4_def,Inv1107_1_0_def
  <1>6. CASE \E n \in Node : Abort(n)
    BY <1>6 DEF Vote1,Vote2,Fail,Go1,Go2,Commit,Abort,TypeOK,Init,Next,OpNext,OtherNext,Termination,IndAuto,SafetyCore,Inv913_1_0_def,Inv1214_1_1_def,Inv134_1_2_def,Inv909_1_3_def,Inv877_1_4_def,Inv1107_1_0_def
  <1>7. CASE \E n \in Node : Fail(n)
    BY <1>7 DEF Vote1,Vote2,Fail,Go1,Go2,Commit,Abort,TypeOK,Init,Next,OpNext,OtherNext,Termination,IndAuto,SafetyCore,Inv913_1_0_def,Inv1214_1_1_def,Inv134_1_2_def,Inv909_1_3_def,Inv877_1_4_def,Inv1107_1_0_def
  <1>8. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7 DEF Next, OpNext, OtherNext
  
  
========================
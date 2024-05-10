---- MODULE peterson_IndProofs ----
\* table: https://github.com/egolf-cs/tla-synthesis/blob/0575612955b0ad69cd051edb41bf8eeec87b0e9c/tool_and_experimentation/reports/README.md
\* configindex: 413
\* eid: 14.15.16.17

EXTENDS peterson

TypeOK == 
    /\ flag \in [ProcSet -> {TRUE, FALSE}]
    /\ turn \in ProcSet
    \* /\ pc \in [ProcSet -> {"a1","a2","a3","a4","a5","cs"}]  
    /\ pc \in [ProcSet -> {0,1,2,3,4,5}]  

\*
\* Inductive strengthening assertions.
\*

C == \A self,other \in ProcSet : ((turn = self)) \/ (~((pc[self] = 0)))

\* Inductive invariant.
Ind == 
    /\ TypeOK
    /\ Mutex
    /\ C


\*
\* Proving the inductive invariant.
\*

\* Peterson's algorithm is only expected to work for exactly two processes.
ASSUME TwoProcAssump == ProcSet = {0,1}
USE TwoProcAssump
USE DEF Mutex


THEOREM Init => Ind BY DEF Init, Ind, TypeOK, Mutex, C, Other

\* Inductive step.
 THEOREM Ind /\ Next => Ind' 
   <1> SUFFICES ASSUME Ind /\ Next
                PROVE  Ind'
     OBVIOUS
   <1>1. TypeOK'
     BY DEF Init,Next,Ind,TypeOK,a1,a2,a3,a4,cs,a5,C,ParamNext1,ParamNext2
   <1>2. Mutex'
     <2>1. CASE \E self \in ProcSet : ParamNext1(self)
       <3> SUFFICES ASSUME NEW self \in ProcSet,
                           ParamNext1(self)
                    PROVE  Mutex'
         BY <2>1 
       <3>1. CASE a1(self)
         BY <3>1, <2>1 DEF Init,Next,Ind,TypeOK,a1,a2,a3,a4,cs,a5,C,ParamNext1,ParamNext2
       <3>2. CASE a2(self)
         BY <3>2, <2>1 DEF Init,Next,Ind,TypeOK,a1,a2,a3,a4,cs,a5,C,ParamNext1,ParamNext2
       <3>3. CASE cs(self)
         BY <3>3, <2>1 DEF Init,Next,Ind,TypeOK,a1,a2,a3,a4,cs,a5,C,ParamNext1,ParamNext2
       <3>4. CASE a5(self)
         BY <3>4, <2>1 DEF Init,Next,Ind,TypeOK,a1,a2,a3,a4,cs,a5,C,ParamNext1,ParamNext2
       <3>5. QED
         BY <2>1, <3>1, <3>2, <3>3, <3>4 DEF ParamNext1
       
     <2>2. CASE \E self, other \in ProcSet : ParamNext2(self, other)
       BY <2>2 DEF Init,Next,Ind,TypeOK,a1,a2,a3,a4,cs,a5,C,ParamNext1,ParamNext2
     <2>3. QED
       BY <2>1, <2>2 DEF Next
     
   <1>3. C'
     <2>1. ASSUME NEW self \in ProcSet,
                  a1(self)
           PROVE  C'
       BY <2>1 DEF Init,Next,Ind,TypeOK,a1,a2,a3,a4,cs,a5,C,ParamNext1,ParamNext2
     <2>2. ASSUME NEW self \in ProcSet,
                  a2(self)
           PROVE  C'
       BY <2>2 DEF Init,Next,Ind,TypeOK,a1,a2,a3,a4,cs,a5,C,ParamNext1,ParamNext2
     <2>3. ASSUME NEW self \in ProcSet,
                  cs(self)
           PROVE  C'
       BY <2>3 DEF Init,Next,Ind,TypeOK,a1,a2,a3,a4,cs,a5,C,ParamNext1,ParamNext2
     <2>4. ASSUME NEW self \in ProcSet,
                  a5(self)
           PROVE  C'
       BY <2>4 DEF Init,Next,Ind,TypeOK,a1,a2,a3,a4,cs,a5,C,ParamNext1,ParamNext2
     <2>5. ASSUME NEW self \in ProcSet,
                  NEW other \in ProcSet,
                  a3(self, other)
           PROVE  C'
       BY <2>5 DEF Init,Next,Ind,TypeOK,a1,a2,a3,a4,cs,a5,C,ParamNext1,ParamNext2
     <2>6. ASSUME NEW self \in ProcSet,
                  NEW other \in ProcSet,
                  a4(self, other)
           PROVE  C'
       BY <2>6 DEF Init,Next,Ind,TypeOK,a1,a2,a3,a4,cs,a5,C,ParamNext1,ParamNext2
     <2>7. QED
       BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Next, ParamNext1, ParamNext2
     
   <1>4. QED
     BY <1>1, <1>2, <1>3 DEF Ind
    

====
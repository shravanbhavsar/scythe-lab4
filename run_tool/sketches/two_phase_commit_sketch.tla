---- MODULE two_phase_commit ----
\* benchmark: i4-two-phase-commit

EXTENDS TLC

CONSTANT Node

VARIABLE vote_yes
VARIABLE vote_no
VARIABLE alive
VARIABLE go_commit
VARIABLE go_abort
VARIABLE decide_commit
VARIABLE decide_abort

VARIABLE abort_flag

\* This variable added to prevent cheesing
VARIABLE compatible

vars == <<vote_yes,vote_no,alive,go_commit,go_abort,decide_commit,decide_abort,abort_flag,compatible>>


Vote1(n) ==
    /\ __Vote1(n)_g0__ \* gt: n \in compatible
    /\ __Vote1(n)_g1__ \* gt: n \in alive
    /\ vote_yes' = __Vote1(n)_vote_yes__ \* gt: vote_yes \cup {n}
    /\ vote_no' = __Vote1(n)_vote_no__ \* gt: vote_no
    /\ decide_commit' = __Vote1(n)_decide_commit__ \* gt: decide_commit
    /\ decide_abort' = __Vote1(n)_decide_abort__ \* gt: decide_abort
    /\ UNCHANGED <<alive,go_commit,go_abort,abort_flag,compatible>>


Vote2(n) ==
    /\ __Vote2(n)_g0__ \* gt: n \notin compatible
    /\ __Vote2(n)_g1__ \* gt: n \in alive
    /\ vote_no' = __Vote2(n)_vote_no__ \* gt: vote_no \cup {n}
    /\ vote_yes' = __Vote2(n)_vote_yes__ \* gt: vote_yes
    /\ decide_commit' = __Vote2(n)_decide_commit__ \* gt: decide_commit
    /\ decide_abort' = __Vote2(n)_decide_abort__ \* gt: decide_abort
    /\ UNCHANGED <<alive,go_commit,go_abort,abort_flag,compatible>>


Go1 ==
    /\ __Go1_g0__ \* gt: Node \cap go_abort = {}
    /\ __Go1_g1__ \* gt: vote_yes = Node
    /\ go_commit' = __Go1_go_commit__ \* gt: Node
    /\ go_abort' = __Go1_go_abort__ \* gt: go_abort
    /\ abort_flag' = __Go1_abort_flag__ \* gt: abort_flag
    /\ UNCHANGED <<vote_yes,vote_no,alive,decide_commit,decide_abort,compatible>>


Go2 ==
    /\ __Go2_g0__ \* gt: Node \cap go_commit = {}
    /\ __Go2_g1__ \* gt: (Node \cap vote_no) \cup (Node \ alive) # {}
    /\ go_abort' = __Go2_go_abort__ \* gt: Node
    /\ abort_flag' = __Go2_abort_flag__ \* gt: TRUE
    /\ go_commit' = __Go2_go_commit__ \* gt: go_commit
    /\ UNCHANGED <<vote_yes,vote_no,alive,decide_commit,decide_abort,compatible>>


Commit(n) ==
    /\ __Commit(n)_g0__ \* gt: n \in alive
    /\ __Commit(n)_g1__ \* gt: n \in go_commit
    /\ decide_commit' = __Commit(n)_decide_commit__ \* gt: decide_commit \cup {n}
    /\ vote_no' = __Commit(n)_vote_no__ \* gt: vote_no
    /\ vote_yes' = __Commit(n)_vote_yes__ \* gt: vote_yes
    /\ decide_abort' = __Commit(n)_decide_abort__ \* gt: decide_abort
    /\ UNCHANGED <<alive,go_commit,go_abort,compatible,abort_flag>>


Abort(n) ==
    /\ __Abort(n)_g0__ \* gt: n \in alive
    /\ __Abort(n)_g1__ \* gt: n \in go_abort
    /\ decide_abort' = __Abort(n)_decide_abort__ \* gt: decide_abort \cup {n}
    /\ vote_no' = __Abort(n)_vote_no__ \* gt: vote_no
    /\ vote_yes' = __Abort(n)_vote_yes__ \* gt: vote_yes
    /\ decide_commit' = __Abort(n)_decide_commit__ \* gt: decide_commit
    /\ UNCHANGED <<alive,go_commit,go_abort,compatible,abort_flag>>



Fail(n) ==
    /\ n \in alive
    /\ alive' = alive \ {n}
    \* omitted: /\ abort_flag' = TRUE
    /\ UNCHANGED <<vote_yes,vote_no,go_commit,go_abort,decide_commit,decide_abort,compatible, abort_flag>>

termination == 
    \/ alive \in SUBSET decide_abort 
    \/ alive \in SUBSET decide_commit

Termination == termination /\ UNCHANGED vars

OpNext ==
    \/ \E n \in Node : Vote1(n)
    \/ \E n \in Node : Vote2(n)
    \/ Go1
    \/ Go2
    \/ \E n \in Node : Commit(n)
    \/ \E n \in Node : Abort(n)

OtherNext ==
    \/ Termination
    \/ \E n \in Node : Fail(n)

Next == OpNext \/ OtherNext

Init ==
    /\ compatible \in SUBSET Node 
    /\ vote_yes = {}
    /\ vote_no = {}
    /\ alive = Node
    /\ go_commit = {}
    /\ go_abort = {}
    /\ decide_commit = {}
    /\ decide_abort = {}
    /\ abort_flag = FALSE

Spec == Init /\ [][Next]_vars /\ SF_vars(OpNext)

Safety ==
    /\ \A n,n2 \in Node : (n \in decide_commit) => (n2 \notin decide_abort)
    \* The line below changes vote_yes -> compatible 
    /\ \A n,n2 \in Node : (n \in decide_commit) => (n2 \in compatible)
    /\ \A n,n2 \in Node : (n \in decide_abort) => abort_flag
    \* This safety property did not exist in the original benchmark
    /\ \A n \in Node : (n \in compatible) => (n \notin vote_no)

Temporal == 
    /\ <> termination
    /\ ([] (compatible = Node /\ alive = Node)) => (<> (decide_commit = Node))
    \* If the node is not alive, its state should not change
    /\ [][\A n \in Node : n \notin alive => 
        /\ (n \in decide_commit <=> n \in decide_commit')
        /\ (n \in decide_abort <=> n \in decide_abort')
        /\ (n \in vote_yes <=> n \in vote_yes')
        /\ (n \in vote_no <=> n \in vote_no')
        ]_vars

====
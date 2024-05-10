---- MODULE two_phase_commit2 ----
\* configindex: 303, 485


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
    /\ n \in compatible \* gt: n \in compatible
    /\ n \in alive \* gt: n \in alive
    /\ vote_yes' = vote_yes \cup {n} \* gt: vote_yes \cup {n}
    /\ vote_no' = vote_no \* gt: vote_no
    /\ decide_commit' = decide_commit \* gt: decide_commit
    /\ decide_abort' = decide_abort \* gt: decide_abort
    /\ UNCHANGED <<alive,go_commit,go_abort,abort_flag,compatible>>


Vote2(n) ==
    /\ n \notin compatible \* gt: n \notin compatible
    /\ n \in alive \* gt: n \in alive
    /\ vote_no' = vote_no \cup {n} \* gt: vote_no \cup {n}
    /\ vote_yes' = vote_yes \* gt: vote_yes
    /\ decide_commit' = decide_commit \* gt: decide_commit
    /\ decide_abort' = decide_abort \* gt: decide_abort
    /\ UNCHANGED <<alive,go_commit,go_abort,abort_flag,compatible>>


Go1 ==
    /\ Node \cap go_abort = {} \* gt: Node \cap go_abort = {}
    /\ vote_yes = Node \* gt: vote_yes = Node
    /\ go_commit' = Node \* gt: Node
    /\ go_abort' = go_abort \* gt: go_abort
    /\ abort_flag' = abort_flag \* gt: abort_flag
    /\ UNCHANGED <<vote_yes,vote_no,alive,decide_commit,decide_abort,compatible>>


Go2 ==
    /\ ({} = go_commit) \* gt: Node \cap go_commit = {}
    /\ ~ ((Node = (alive \ vote_no))) \* gt: (Node \cap vote_no) \cup (Node \ alive) # {}
    /\ go_abort' = Node \* gt: Node
    /\ abort_flag' = TRUE \* gt: TRUE
    /\ go_commit' = go_commit \* gt: go_commit
    /\ UNCHANGED <<vote_yes,vote_no,alive,decide_commit,decide_abort,compatible>>


Commit(n) ==
    /\ n \in alive \* gt: n \in alive
    /\ n \in go_commit \* gt: n \in go_commit
    /\ decide_commit' = decide_commit \cup {n} \* gt: decide_commit \cup {n}
    /\ vote_no' = vote_no \* gt: vote_no
    /\ vote_yes' = vote_yes \* gt: vote_yes
    /\ decide_abort' = decide_abort \* gt: decide_abort
    /\ UNCHANGED <<alive,go_commit,go_abort,compatible,abort_flag>>


Abort(n) ==
    /\ n \in alive \* gt: n \in alive
    /\ n \in go_abort \* gt: n \in go_abort
    /\ decide_abort' = decide_abort \cup {n} \* gt: decide_abort \cup {n}
    /\ vote_no' = vote_no \* gt: vote_no
    /\ vote_yes' = vote_yes \* gt: vote_yes
    /\ decide_commit' = decide_commit \* gt: decide_commit
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
    \* \/ Termination
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
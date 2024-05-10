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

\* <actions>


\* Some lines below are commented out. Lines preceded with "omitted" are from
\* the original (endive) benchmark and they are omitted because they are
\* redundant: including them does not affect correctness, nor performance. 

\* If a comment is preceded with "Alt2below", what follows is an alternative
\* expression found by the synthesis tool. These alternatives do not seem to be
\* caused by "cheesing": they are acceptable alternatives and in some cases they
\* are smaller expressions. 

\* Some of the "UNCHANGED" variables have been blown out to become x' = x. This
\* is because the synthesis tool should be able to fill these in as holes.
\* Variables following the "UNCHANGED" keyword are not meant to be written to by
\* the process that owns the action, so we would not expect the synthesis tool
\* to fill them in under realistic input conditions. E.g. neither the resource
\* managers nor the transaction manger should be able to change the set of nodes
\* that are alive---that is abstracted into the Fail action, which belongs to
\* the "environment."

Vote1(n) ==
    /\ n \in compatible
    /\ n \in alive
    \* omitted: /\ n \notin vote_no
    \* omitted: /\ n \notin decide_commit
    \* omitted: /\ n \notin decide_abort
    /\ vote_yes' = vote_yes \cup {n}
    /\ vote_no' = vote_no
    /\ decide_commit' = decide_commit
    /\ decide_abort' = decide_abort
    /\ UNCHANGED <<alive,go_commit,go_abort,abort_flag,compatible>>

Vote2(n) ==
    /\ n \notin compatible
    /\ n \in alive
    \* omitted: /\ n \notin vote_yes
    \* omitted: /\ n \notin decide_commit
    \* omitted: /\ n \notin decide_abort
    \* omitted: /\ abort_flag' = TRUE
    \* omitted: /\ decide_abort' = decide_abort \cup {n}
    /\ vote_no' = vote_no \cup {n}
    /\ vote_yes' = vote_yes
    /\ decide_commit' = decide_commit
    /\ decide_abort' = decide_abort
    /\ UNCHANGED <<alive,go_commit,go_abort,abort_flag,compatible>>

Go1 ==
    \* omitted: /\ Node \cap go_commit = {}
    \* Alt2below: /\ vote_yes = alive
    /\ Node \cap go_abort = {}
    /\ vote_yes = Node
    /\ go_commit' = Node
    /\ go_abort' = go_abort
    /\ abort_flag' = abort_flag
    /\ UNCHANGED <<vote_yes,vote_no,alive,decide_commit,decide_abort,compatible>>

Go2 ==
    \* Alt2below: /\ vote_yes = (vote_yes \ go_commit)
    /\ Node \cap go_commit = {}
    \* omitted: /\ Node \cap go_abort = {}
    \* Alt2below: /\ Node # (alive \ vote_no)
    /\ (Node \cap vote_no) \cup (Node \ alive) # {}
    /\ go_abort' = Node
    /\ abort_flag' = TRUE
    /\ go_commit' = go_commit
    /\ UNCHANGED <<vote_yes,vote_no,alive,decide_commit,decide_abort,compatible>>

Commit(n) ==
    /\ n \in alive
    /\ n \in go_commit
    /\ decide_commit' = decide_commit \cup {n}
    /\ vote_no' = vote_no
    /\ vote_yes' = vote_yes
    /\ decide_abort' = decide_abort
    /\ UNCHANGED <<alive,go_commit,go_abort,compatible,abort_flag>>

Abort(n) ==
    /\ n \in alive
    /\ n \in go_abort
    \* omitted (moved to Go2): /\ abort_flag' = TRUE
    /\ decide_abort' = decide_abort \cup {n}
    /\ vote_no' = vote_no
    /\ vote_yes' = vote_yes
    /\ decide_commit' = decide_commit
    /\ UNCHANGED <<alive,go_commit,go_abort,compatible,abort_flag>>

\* </actions>

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


\* <properties>
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
\* </properties>

====
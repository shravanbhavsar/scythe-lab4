---- MODULE full_2pc ----

EXTENDS TLC

CONSTANT Node

VARIABLE user_waiting
VARIABLE to_vote
VARIABLE frozen
VARIABLE voted_yes
VARIABLE voted_no
VARIABLE to_commit
VARIABLE to_abort
VARIABLE aborted
VARIABLE committed
VARIABLE decided
VARIABLE compatible
VARIABLE reset_flag

vars == <<
    \* read/write channels between transaction manager/database managers
    to_vote, to_commit, to_abort, 
    \* db manager read-only channels from transaction manager
    reset_flag, 
    \* transaction manager read-only channels from db managers
    voted_yes, voted_no,
    \* state variables for environment processes (user/databases)
    user_waiting, frozen, compatible,
    \* state variables for protocol process (db manager and tx manager)
    aborted, committed, decided>>


(***************************************************************************)
\* User Process (environment process)

\* These variables are uncontrollable by the user.
user_uncontrollable == <<to_vote, to_commit, to_abort, voted_yes, voted_no, 
    frozen, compatible, aborted, committed, decided, reset_flag>>

\* This is the user action that initiates a transaction.
SubmitTransaction ==
    \* /\ decided = __SubmitTransaction_decided__ \* gt: FALSE
    \* /\ user_waiting = __SubmitTransaction_user_waiting__ \* gt: FALSE
    /\ user_waiting = FALSE
    /\ decided = FALSE
    /\ user_waiting' = TRUE
    /\ UNCHANGED user_uncontrollable

\* This is a user action.
AcceptDecision ==
    /\ decided = TRUE
    /\ user_waiting = TRUE
    /\ user_waiting' = FALSE \* user has been notified of decision
    /\ UNCHANGED user_uncontrollable



(***************************************************************************)
\* Database Process (environment process)

\* These variables are uncontrollable by a database.
db_uncontrollable == <<user_waiting, to_vote, to_commit, to_abort, voted_yes, 
    voted_no, frozen, aborted, committed, decided, reset_flag>>

\* These are environment actions that manipulate the database state
\* therefore, they are "uncontrollable." This abstracts the concept
\* of a database being "compatible" with a given transaction.
MkCompatible(n) ==
    /\ n \notin frozen
    /\ compatible' = compatible \cup {n}
    /\ UNCHANGED db_uncontrollable
MkIncompatible(n) ==
    /\ n \notin frozen
    /\ compatible' = compatible \ {n}
    /\ UNCHANGED db_uncontrollable



(***************************************************************************)
\* Database Manager Process (protocol process)

\* These variables are uncontrollable by a database manager.
db_man_uncontrollable == <<user_waiting, compatible, decided, reset_flag>>

\* The database manager should not be able to read:
\* user_waiting, decided

\* This is a database manager action.
\* Strictly speaking, the database manager should not be able to
\* observe the user_waiting variable. We assume that the database
\* manager obtains this observation from the transaction manager.
ResetDatabaseManager(n) ==
    /\ reset_flag
    /\ n \notin to_abort \* and not pending abort
    /\ n \notin to_commit \* and not pending commit
    /\ frozen' = frozen \ {n}
    /\ aborted' = aborted \ {n}
    /\ committed' = committed \ {n}
    /\ voted_no' = voted_no \ {n}
    /\ voted_yes' = voted_yes \ {n}
    /\ UNCHANGED db_man_uncontrollable
    /\ UNCHANGED <<to_abort, to_commit, to_vote>>

\* This is a database manager action.
VoteYes(n) ==
    /\ n \in to_vote
    /\ n \in compatible
    /\ to_vote' = to_vote \ {n}
    /\ voted_yes' = voted_yes \cup {n}
    /\ frozen' = frozen \cup {n}
    /\ UNCHANGED db_man_uncontrollable
    /\ UNCHANGED <<aborted, committed, to_abort, to_commit, voted_no>>

\* This is a database manager action.
VoteNo(n) ==
    /\ n \in to_vote
    /\ n \notin compatible
    /\ to_vote' = to_vote \ {n}
    /\ voted_no' = voted_no \cup {n}
    /\ frozen' = frozen \cup {n}
    /\ UNCHANGED db_man_uncontrollable
    /\ UNCHANGED <<aborted, committed, to_abort, to_commit, voted_yes>>

\* This is a database manager action.
Commit(n) ==
    /\ n \in to_commit
    /\ to_commit' = to_commit \ {n}
    /\ committed' = committed \cup {n}
    /\ UNCHANGED db_man_uncontrollable
    /\ UNCHANGED <<aborted, frozen, to_abort, to_vote, voted_no, voted_yes>>

\* This is a database manager action.
Abort(n) ==
    /\ n \in to_abort
    /\ to_abort' = to_abort \ {n}
    /\ aborted' = aborted \cup {n}
    /\ UNCHANGED db_man_uncontrollable
    /\ UNCHANGED <<committed, frozen, to_commit, to_vote, voted_no, voted_yes>>



(***************************************************************************)
\* Transaction Manager Process (protocol process)

\* These variables are uncontrollable by a transaction manager.
tx_man_uncontrollable == <<voted_yes, voted_no, user_waiting, frozen, compatible, aborted, committed>>

\* This is a transaction manager action.
InitiateVote(n) ==
    /\ user_waiting = TRUE
    /\ n \notin to_vote
    /\ n \notin voted_yes
    /\ n \notin voted_no
    /\ to_vote' = to_vote \cup {n}
    /\ UNCHANGED tx_man_uncontrollable
    /\ UNCHANGED <<decided, to_abort, to_commit, reset_flag>>

\* This is a transaction manager action.
DecideCommit ==
    /\ decided = FALSE
    /\ voted_yes = Node
    /\ to_commit' = Node
    /\ decided' = TRUE
    /\ UNCHANGED tx_man_uncontrollable
    /\ UNCHANGED <<to_abort, to_vote, reset_flag>>

\* This is a transaction manager action.
DecideAbort ==
    /\ decided = FALSE
    /\ \A n \in Node : n \in voted_yes \/ n \in voted_no
    /\ \E n \in Node : n \in voted_no
    /\ to_abort' = Node
    /\ decided' = TRUE
    /\ UNCHANGED tx_man_uncontrollable
    /\ UNCHANGED <<to_commit, to_vote, reset_flag>>

SetResetFlag == 
    /\ decided
    /\ ~user_waiting
    /\ ~reset_flag
    /\ reset_flag' = TRUE
    /\ UNCHANGED tx_man_uncontrollable
    /\ UNCHANGED <<decided, to_vote, to_commit, to_abort>>

\* This is a transaction manager action.
ResetTransactionManager ==
    /\ decided
    /\ voted_no = {} \* These two guards assure that the database managers
    /\ voted_yes = {} \* have been reset.
    /\ decided' = FALSE
    /\ reset_flag' = FALSE
    /\ UNCHANGED tx_man_uncontrollable
    /\ UNCHANGED <<to_vote, to_commit, to_abort>>



(***************************************************************************)
\* Spec

Init == 
    /\ user_waiting = FALSE
    /\ to_vote = {}
    /\ frozen = {}
    /\ voted_yes = {}
    /\ voted_no = {}
    /\ to_commit = {}
    /\ to_abort = {}
    /\ aborted = {}
    /\ committed = {}
    /\ decided = FALSE
    /\ reset_flag = FALSE
    /\ compatible \in SUBSET Node

DBNext == 
    \/ \E n \in Node : MkCompatible(n)
    \/ \E n \in Node : MkIncompatible(n)

OthersNext == 
    \/ SubmitTransaction
    \/ \E n \in Node : InitiateVote(n)
    \/ \E n \in Node : VoteYes(n)
    \/ \E n \in Node : VoteNo(n)
    \/ DecideCommit
    \/ DecideAbort
    \/ \E n \in Node : Commit(n)
    \/ \E n \in Node : Abort(n)
    \/ AcceptDecision
    \/ \E n \in Node : ResetDatabaseManager(n)
    \/ SetResetFlag
    \/ ResetTransactionManager

Next == DBNext \/ OthersNext

Spec == 
    /\ Init 
    /\ [][Next]_vars
    \* We don't want to loop in DBNext forever
    \* Comment out for STUTTERING TEST
    /\ SF_vars(OthersNext)



(***************************************************************************)
\* Properties


\* <properties>
\* The safety property need only hold when the user is waiting for a decision
\* and the decision has been made. Note: the spec is now in terms of the db
\* state rather than the yes/no votes.
Safety ==
    (user_waiting /\ decided) =>
        /\ \A n,n2 \in Node : (n \in committed) => (n2 \notin aborted)
        /\ \A n,n2 \in Node : (n \in committed) => (n2 \in compatible)
        /\ \A n \in Node : 
            (n \in aborted => \E n2 \in Node : n2 \notin compatible)

Liveness == 
    \* Always eventually the user will submit a transaction.
    /\ []<> user_waiting
    \* Always eventually the user will receive a decision.
    /\ []<> ~user_waiting
    \* Don't let a db manager freeze their db forever.
    /\ \A n \in Node : []<> (n \notin frozen)
    \* If a decision is made, all nodes need to abort or commit
    \* This would allow the abort/commit to happen later on, so it isn't perfect
    \*  but it rules out some cheesing.
    /\ []((user_waiting /\ decided) =>
            \A n \in Node : <>(n \in aborted \/ n \in committed))
\* </properties>

Symmetry == Permutations(Node)

====
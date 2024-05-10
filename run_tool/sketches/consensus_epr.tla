---- MODULE consensus_epr ----
EXTENDS TLC, Naturals, FiniteSets, Sequences

CONSTANT
    Node,
    Quorum,
    Value


VARIABLE 
    vote_request_msg,
    voted,
    vote_msg,
    votes,
    leader,
    decided,
    req_history

vars == <<vote_request_msg,voted,vote_msg,votes,leader,decided,req_history>>

\* <actions>

\* This action is new. Processes may ignore votes if they have already voted
\* This was added for liveness.
\* src ignores a vote request from dst
IgnoreRequestVote(src, dst) ==
    \* /\ src \in voted
    /\ voted[src]
    /\ vote_request_msg' = vote_request_msg \ {<<dst,src>>}
    \* /\ vote_request_msg' = vote_request_msg
    /\ vote_msg' = vote_msg
    /\ voted' = voted
    /\ votes' = votes
    /\ decided' = decided
    /\ leader' = leader
    /\ UNCHANGED req_history

\* src sends a vote to dst
SendVote(src, dst) ==
    \* Use scheduling to fix (should not be able to arbitrarily block certain
    \* send events): /\ src = dst 
    \* /\ src \notin voted
    /\ ~voted[src]
    /\ <<dst, src>> \in vote_request_msg
    \* Added: the set minus for liveness
    /\ vote_request_msg' = vote_request_msg \ {<<dst,src>>}
    \* /\ vote_request_msg' = vote_request_msg
    /\ vote_msg' = vote_msg \cup {<<src, dst>>}
    \* /\ voted' = voted \cup {src}
    /\ voted' = [voted EXCEPT ![src] = TRUE]
    /\ votes' = votes
    /\ decided' = decided
    /\ leader' = leader
    /\ UNCHANGED req_history
    \* It's not clear why these exist---maybe the tuples should <<dst,src>>?
    \* omitted: /\ \/ vote_request_msg' = vote_request_msg \cup {<<src,dst>>}
    \* omitted:    \/ vote_request_msg' = vote_request_msg \ {<<src,dst>>}

\* n receives a vote from sender
RecvVote(n, sender) ==
    /\ <<sender, n>> \in vote_msg
    /\ votes' = [votes EXCEPT ![n] = (votes[n] \cup {sender})]
    \* /\ votes' = votes
    /\ voted' = voted
    /\ vote_msg' = vote_msg
    /\ leader' = leader
    /\ decided' = decided
    /\ vote_request_msg' = vote_request_msg
    /\ UNCHANGED req_history

\* n becomes leader with quorum Q
BecomeLeader(n, Q) ==
    \* Alt2below: /\ Q \ votes[n] = {}
    \* ViolatesModelingAssumptions: /\ leader = {}
    /\ Q \subseteq votes[n]
    \* /\ leader' = leader \cup {n}
    /\ leader' = [leader EXCEPT ![n] = TRUE]
    /\ votes' = votes
    /\ voted' = voted
    /\ vote_msg' = vote_msg
    /\ decided' = decided
    /\ vote_request_msg' = vote_request_msg
    /\ UNCHANGED req_history

\* n decides on value v
Decide(n, v) ==
    \* /\ n \in leader
    /\ leader[n]
    /\ decided[n] = {}
    /\ decided' = [decided EXCEPT ![n] = (decided[n] \cup {v})]
    /\ votes' = votes
    /\ voted' = voted
    /\ vote_msg' = vote_msg
    /\ leader' = leader
    /\ vote_request_msg' = vote_request_msg
    /\ UNCHANGED req_history

\* </actions>

\* We will not synthesize this action: we cannot control what vote requests
\* are sent.
\* src asks dst for a vote
SendRequestVote(src, dst) ==
    \* Processes will not request a vote from a process that they've already
    \* requested a vote from.
    /\ <<src,dst>> \notin req_history
    \* The guard is new: Processes will not request votes if a prior request
    \* is not acknowledged. 
    /\ \A dst2 \in Node : <<src,dst2>> \notin vote_request_msg
    /\ vote_request_msg' = vote_request_msg \cup {<<src, dst>>}
    /\ req_history' = req_history \cup {<<src,dst>>}
    /\ UNCHANGED <<voted,vote_msg,votes,leader,decided>>

Init == 
    /\ vote_request_msg = {}
    \* /\ voted = {}
    /\ voted = [i \in Node |-> FALSE]
    /\ vote_msg = {}
    /\ votes = [i \in Node |-> {}]
    \* /\ leader = {}
    /\ leader = [i \in Node |-> FALSE]
    /\ decided = [i \in Node |-> {}]
    /\ req_history = {}

\* SendVoteNext == \E i,j \in Node : SendVote(i,j)
\* IgnoreRequestVoteNext == \E i,j \in Node : IgnoreRequestVote(i,j)
\* RecvVoteNext == \E i,j \in Node : RecvVote(i,j)
\* BecomeLeaderNext == \E i \in Node, Q \in Quorum : BecomeLeader(i,Q)
\* DecideNext == \E i,j \in Node, v \in Value : Decide(i,v)

ProtocolNext ==
    \/ \E i,j \in Node : SendVote(i,j)
    \/ \E i,j \in Node : IgnoreRequestVote(i,j)
    \/ \E i,j \in Node : RecvVote(i,j)
    \/ \E i \in Node, Q \in Quorum : BecomeLeader(i,Q)
    \/ \E i,j \in Node, v \in Value : Decide(i,v)
\* ProtocolNext == 
\*     \/ SendVoteNext
\*     \/ IgnoreRequestVoteNext
\*     \/ RecvVoteNext
\*     \/ BecomeLeaderNext
\*     \/ DecideNext

OtherNext == \E i,j \in Node : SendRequestVote(i,j)

Next == ProtocolNext \/ OtherNext

Spec == 
    /\ Init 
    /\ [][Next]_vars 
    /\ SF_vars(ProtocolNext)
    \* /\ SF_vars(ProtocolNext)
    \* /\ SF_vars(SendVoteNext)
    \* /\ SF_vars(IgnoreRequestVoteNext)
    \* /\ \A i,j \in Node : SF_vars(RecvVote(i,j))
    \* /\ SF_vars(BecomeLeaderNext)
    \* /\ SF_vars(DecideNext)
    /\ WF_vars(OtherNext)


Symmetry == Permutations(Node) \cup Permutations(Value)

\* <properties>
Safety ==
    /\ \A n1,n2 \in Node, v1,v2 \in Value : 
        (v1 \in decided[n1] /\ v2 \in decided[n2]) => (v1 = v2)
    \* If someone voted for you, you must have requested their vote
    /\ \A dst,src \in Node : src \in votes[dst]
        => <<dst,src>> \in req_history

\* Everyone has voted, but no one received a quorum
SplitVote == 
    /\ \A n1 \in Node : \E n2 \in Node : n1 \in votes[n2]
    /\ \A n \in Node : votes[n] \notin Quorum

Liveness == 
    /\ <> (SplitVote \/ \E n \in Node : decided[n] # {})
    /\ <> \A n \in Node : voted[n]
    \* Vote requests are eventually acknowledged
    /\ []<> (vote_request_msg = {})
\* </properties>

====
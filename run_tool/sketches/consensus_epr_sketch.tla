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


IgnoreRequestVote(src, dst) ==
    /\ __IgnoreRequestVote(src, dst)_g0__ \* gt: voted[src]
    /\ vote_request_msg' = __IgnoreRequestVote(src, dst)_vote_request_msg__ \* gt: vote_request_msg \ {<<dst,src>>}
    /\ vote_msg' = __IgnoreRequestVote(src, dst)_vote_msg__ \* gt: vote_msg
    /\ voted' = __IgnoreRequestVote(src, dst)_voted__ \* gt: voted
    /\ votes' = __IgnoreRequestVote(src, dst)_votes__ \* gt: votes
    /\ decided' = __IgnoreRequestVote(src, dst)_decided__ \* gt: decided
    /\ leader' = __IgnoreRequestVote(src, dst)_leader__ \* gt: leader
    /\ UNCHANGED req_history


SendVote(src, dst) ==
    /\ __SendVote(src, dst)_g0__ \* gt: ~voted[src]
    /\ __SendVote(src, dst)_g1__ \* gt: <<dst, src>> \in vote_request_msg
    /\ vote_request_msg' = __SendVote(src, dst)_vote_request_msg__ \* gt: vote_request_msg \ {<<dst,src>>}
    /\ vote_msg' = __SendVote(src, dst)_vote_msg__ \* gt: vote_msg \cup {<<src, dst>>}
    /\ voted' = __SendVote(src, dst)_voted__ \* gt: [voted EXCEPT ![src] = TRUE]
    /\ votes' = __SendVote(src, dst)_votes__ \* gt: votes
    /\ decided' = __SendVote(src, dst)_decided__ \* gt: decided
    /\ leader' = __SendVote(src, dst)_leader__ \* gt: leader
    /\ UNCHANGED req_history


RecvVote(n, sender) ==
    /\ __RecvVote(n, sender)_g0__ \* gt: <<sender, n>> \in vote_msg
    /\ votes' = __RecvVote(n, sender)_votes__ \* gt: [votes EXCEPT ![n] = (votes[n] \cup {sender})]
    /\ voted' = __RecvVote(n, sender)_voted__ \* gt: voted
    /\ vote_msg' = __RecvVote(n, sender)_vote_msg__ \* gt: vote_msg
    /\ leader' = __RecvVote(n, sender)_leader__ \* gt: leader
    /\ decided' = __RecvVote(n, sender)_decided__ \* gt: decided
    /\ vote_request_msg' = __RecvVote(n, sender)_vote_request_msg__ \* gt: vote_request_msg
    /\ UNCHANGED req_history


BecomeLeader(n, Q) ==
    /\ __BecomeLeader(n, Q)_g0__ \* gt: Q \subseteq votes[n]
    /\ leader' = __BecomeLeader(n, Q)_leader__ \* gt: [leader EXCEPT ![n] = TRUE]
    /\ votes' = __BecomeLeader(n, Q)_votes__ \* gt: votes
    /\ voted' = __BecomeLeader(n, Q)_voted__ \* gt: voted
    /\ vote_msg' = __BecomeLeader(n, Q)_vote_msg__ \* gt: vote_msg
    /\ decided' = __BecomeLeader(n, Q)_decided__ \* gt: decided
    /\ vote_request_msg' = __BecomeLeader(n, Q)_vote_request_msg__ \* gt: vote_request_msg
    /\ UNCHANGED req_history


Decide(n, v) ==
    /\ __Decide(n, v)_g0__ \* gt: leader[n]
    /\ __Decide(n, v)_g1__ \* gt: decided[n] = {}
    /\ decided' = __Decide(n, v)_decided__ \* gt: [decided EXCEPT ![n] = (decided[n] \cup {v})]
    /\ votes' = __Decide(n, v)_votes__ \* gt: votes
    /\ voted' = __Decide(n, v)_voted__ \* gt: voted
    /\ vote_msg' = __Decide(n, v)_vote_msg__ \* gt: vote_msg
    /\ leader' = __Decide(n, v)_leader__ \* gt: leader
    /\ vote_request_msg' = __Decide(n, v)_vote_request_msg__ \* gt: vote_request_msg
    /\ UNCHANGED req_history



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

ProtocolNext ==
    \/ \E i,j \in Node : SendVote(i,j)
    \/ \E i,j \in Node : IgnoreRequestVote(i,j)
    \/ \E i,j \in Node : RecvVote(i,j)
    \/ \E i \in Node, Q \in Quorum : BecomeLeader(i,Q)
    \/ \E i,j \in Node, v \in Value : Decide(i,v)

OtherNext == \E i,j \in Node : SendRequestVote(i,j)

Next == ProtocolNext \/ OtherNext

Spec == 
    /\ Init 
    /\ [][Next]_vars 
    /\ SF_vars(ProtocolNext) 
    /\ WF_vars(OtherNext)


Symmetry == Permutations(Node) \cup Permutations(Value)

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

====
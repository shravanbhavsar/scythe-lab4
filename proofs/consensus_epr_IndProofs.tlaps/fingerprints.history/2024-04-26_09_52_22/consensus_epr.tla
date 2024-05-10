---- MODULE consensus_epr ----
\* table: https://github.com/egolf-cs/tla-synthesis/blob/0575612955b0ad69cd051edb41bf8eeec87b0e9c/tool_and_experimentation/reports/README.md
\* configindex: 624
\* eid: 2.6.5.3.0.4.8.9

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
    /\ voted[src] \* gt: voted[src]
    /\ vote_request_msg' = vote_request_msg \ {<<dst,src>>} \* gt: vote_request_msg \ {<<dst,src>>}
    /\ vote_msg' = vote_msg \* gt: vote_msg
    /\ voted' = voted \* gt: voted
    /\ votes' = votes \* gt: votes
    /\ decided' = decided \* gt: decided
    /\ leader' = leader \* gt: leader
    /\ UNCHANGED req_history


SendVote(src, dst) ==
    /\ ~voted[src] \* gt: ~voted[src]
    /\ <<dst, src>> \in vote_request_msg \* gt: <<dst, src>> \in vote_request_msg
    /\ vote_request_msg' = vote_request_msg \ {<<dst,src>>} \* gt: vote_request_msg \ {<<dst,src>>}
    /\ vote_msg' = vote_msg \cup {<<src, dst>>} \* gt: vote_msg \cup {<<src, dst>>}
    /\ voted' = [voted EXCEPT ![src] = TRUE] \* gt: [voted EXCEPT ![src] = TRUE]
    /\ votes' = votes \* gt: votes
    /\ decided' = decided \* gt: decided
    /\ leader' = leader \* gt: leader
    /\ UNCHANGED req_history


RecvVote(n, sender) ==
    /\ <<sender, n>> \in vote_msg \* gt: <<sender, n>> \in vote_msg
    /\ votes' = [votes EXCEPT ![n] = (votes[n] \cup {sender})] \* gt: [votes EXCEPT ![n] = (votes[n] \cup {sender})]
    /\ voted' = voted \* gt: voted
    /\ vote_msg' = vote_msg \* gt: vote_msg
    /\ leader' = leader \* gt: leader
    /\ decided' = decided \* gt: decided
    /\ vote_request_msg' = vote_request_msg \* gt: vote_request_msg
    /\ UNCHANGED req_history


BecomeLeader(n, Q) ==
    /\ Q \subseteq votes[n] \* gt: Q \subseteq votes[n]
    /\ leader' = [leader EXCEPT ![n] = TRUE] \* gt: [leader EXCEPT ![n] = TRUE]
    /\ votes' = votes \* gt: votes
    /\ voted' = voted \* gt: voted
    /\ vote_msg' = vote_msg \* gt: vote_msg
    /\ decided' = decided \* gt: decided
    /\ vote_request_msg' = vote_request_msg \* gt: vote_request_msg
    /\ UNCHANGED req_history


Decide(n, v) ==
    /\ leader[n] \* gt: leader[n]
    /\ ({} = decided[n]) \* gt: decided[n] = {}
    /\ decided' = [decided EXCEPT ![n] = (decided[n] \cup {v})] \* gt: [decided EXCEPT ![n] = (decided[n] \cup {v})]
    /\ votes' = votes \* gt: votes
    /\ voted' = voted \* gt: voted
    /\ vote_msg' = vote_msg \* gt: vote_msg
    /\ leader' = leader \* gt: leader
    /\ vote_request_msg' = vote_request_msg \* gt: vote_request_msg
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
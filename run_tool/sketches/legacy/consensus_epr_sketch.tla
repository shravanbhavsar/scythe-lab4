---- MODULE consensus_epr ----
EXTENDS TLC, Naturals, FiniteSets, Sequences

CONSTANT 
    \* @type: Set(Str);
    Node,
    \* @type: Set(Str);
    Quorum,
    \* @type: Set(Str);
    Value


VARIABLE 
    \* @type: Set(<<Str,Str>>);
    vote_request_msg,
    \* @type: Set(Str);
    voted,
    \* @type: Set(<<Str,Str>>)
    vote_msg,
    \* @type: Str -> Set(Str)
    votes,
    \* @type: Set(Str)
    leader,
    \* @type: Str -> Set(Str)
    decided

vars == <<vote_request_msg,voted,vote_msg,votes,leader,decided>>

SendRequestVote(src, dst) == 
    /\ vote_request_msg' = __u5__ \* gt: vote_request_msg \cup {<<src, dst>>}
    /\ UNCHANGED <<voted,vote_msg,votes,leader,decided>>

SendVote(src, dst) == 
    /\ __u1__ \* gt: ~ (src \in voted)
    /\ __u9__ \* gt: <<dst,src>> \in vote_request_msg
    /\ vote_msg' = __u4__ \* gt: vote_msg \cup {<<src,dst>>}
    /\ voted' = __u8__ \* gt: voted \cup {src}
    \* /\ \/ vote_request_msg' = vote_request_msg \cup {<<src,dst>>}
    \*    \/ vote_request_msg' = vote_request_msg \ {<<src,dst>>}
    /\ UNCHANGED <<votes, leader, decided, 
        vote_request_msg \* comment out if using \/ above
        >>

RecvVote(n, sender) == 
    /\ __u10__ \* gt: <<sender,n>> \in vote_msg
    /\ votes' = __u7__ \* gt: [votes EXCEPT ![n] = votes[n] \cup {sender}]
    /\ UNCHANGED <<vote_request_msg,voted,vote_msg,leader,decided>>

BecomeLeader(n, Q) == 
    /\ __u2__ \* gt: Q \subseteq votes[n]
    /\ leader' = __u6__ \* gt: leader \cup {n}
    /\ UNCHANGED <<vote_request_msg,voted,vote_msg,votes,decided>>

Decide(n, v) == 
    /\ n \in leader
    /\ decided[n] = {}
    /\ decided' = __u3__ \* gt: [decided EXCEPT ![n] = decided[n] \cup {v}]
    /\ UNCHANGED <<vote_request_msg,voted,vote_msg,votes,leader>>

Init == 
    /\ vote_request_msg = {}
    /\ voted = {}
    /\ vote_msg = {}
    /\ votes = [i \in Node |-> {}]
    /\ leader = {}
    /\ decided = [i \in Node |-> {}]

Next == 
    \/ \E i,j \in Node : SendRequestVote(i,j)
    \/ \E i,j \in Node : SendVote(i,j)
    \/ \E i,j \in Node : RecvVote(i,j)
    \/ \E i \in Node, Q \in Quorum : BecomeLeader(i,Q)
    \/ \E i,j \in Node, v \in Value : Decide(i,v)

Spec == Init /\ [][Next]_vars /\ SF_vars(Next)

Symmetry == Permutations(Node) \cup Permutations(Value)


Safety ==
    /\ \A n1,n2 \in Node, v1,v2 \in Value : 
        (v1 \in decided[n1] /\ v2 \in decided[n2]) => (v1 = v2)
    \* If someone voted for you, you must have requested their vote
    /\ \A dst,src \in Node : src \in votes[dst]
        => <<dst,src>> \in vote_request_msg

Liveness == 
    /\ <> (voted = Node)
    /\ [] (leader # {} => <> \E n \in Node : decided[n] # {})
    /\ \A n \in Node : \E n2 \in Node : <> (n \in votes[n2])
    /\ [] ((\E n \in Node : \E Q \in Quorum : Q \subseteq votes[n]) 
            => <> (leader # {})) 

\* Liveness == 
\*     \* /\ \E i,j \in Node : <> ENABLED <<SendRequestVote(i,j)>>_vars
\*     \* /\ \E i,j \in Node : <> ENABLED <<SendVote(i,j)>>_vars
\*     \* /\ \E i,j \in Node : <> ENABLED <<RecvVote(i,j)>>_vars
\*     /\ <> (
\*         \/ \E i \in Node, Q \in Quorum :  ENABLED <<BecomeLeader(i,Q)>>_vars
\*         \/ SplitVote)
\*     /\ (<> \E i \in Node, Q \in Quorum :  ENABLED <<BecomeLeader(i,Q)>>_vars) 
\*         => <> \E i,j \in Node, v \in Value : ENABLED <<Decide(i,v)>>_vars

====
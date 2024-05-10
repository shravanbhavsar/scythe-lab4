---- MODULE lamport_clocks ----
EXTENDS TLC, Naturals, FiniteSets, Sequences

\* A few auxiliary operators
InSequence(x, seq) == \E i \in 1..Len(seq) : seq[i] = x
InMap(x, map) == Len(map[x]) > 0
IndexBefore(e1, e2, seq) == 
    \A i \in 1..Len(seq) : seq[i] = e1
    /\ \A j \in 1..Len(seq) : seq[j] = e2 => i < j

\* The bounds for the number of processes and src-dst event ids
CONSTANT MaxProcId
CONSTANT MaxEventId
CONSTANT MaxTimestamp

\* Some "types" and constants that depend on the bounds above 
SEND == 0
RECV == 1
EventTypes == {SEND, RECV}
EventIds == 1..MaxEventId
Procs == 1..MaxProcId
Events == {<<T, eid, src, dst>> 
    : T \in EventTypes, eid \in EventIds, src \in Procs, dst \in Procs}
Timestamps == 1..MaxTimestamp

\* The "environment variables" necessary to write the safety property
VARIABLES event_log, lc
\* Auxiliary environment variables used only by the environment processes
VARIABLES used_ids
env_vars == <<event_log, lc, used_ids>>
\* Variables used to facilitate the communication between the environment and 
\* the protocol processes.
VARIABLES event_queue, to_recv, to_resolve


\* <SOLUTION>
\* This solution block consitutes a solution to the synthesis problem
\* Everything outside of this block constitutes the synthesis problem

\* This variable maps proc ids to their local clocks
VARIABLE proc_time
protocol_vars == <<proc_time>>
vars == <<proc_time, event_log, lc, event_queue, to_recv, to_resolve, used_ids>>

Send(send_timestamp, eid, src, dst) ==
    /\ Len(event_queue) > 0
    /\ Head(event_queue) = <<SEND, eid, src, dst>>
    /\ send_timestamp = proc_time[src] + 1
    /\ event_queue' = Tail(event_queue)
    /\ proc_time' = [proc_time EXCEPT ![src] = send_timestamp]
    /\ to_recv' = to_recv \cup {<<send_timestamp, eid, src, dst>>}
    /\ UNCHANGED to_resolve
    /\ UNCHANGED env_vars

Recv(send_timestamp, recv_timestamp, eid, src, dst) ==
    /\ Len(event_queue) > 0
    /\ Head(event_queue) = <<RECV, send_timestamp, eid, src, dst>>
    /\ recv_timestamp = 
        IF send_timestamp > proc_time[dst] 
        THEN send_timestamp + 1
        ELSE proc_time[dst] + 1
    /\ event_queue' = Tail(event_queue)
    /\ proc_time' = [proc_time EXCEPT ![dst] = recv_timestamp]
    /\ to_resolve' = to_resolve \cup {<<recv_timestamp, eid, src, dst>>}
    /\ UNCHANGED to_recv
    /\ UNCHANGED env_vars

\* <\SOLUTION>

\* The "environment" actions
\* These actions are uncontrollable and the protocol must cope with
\* whatever the environment does.
TriggerSend(eid, src, dst) ==
    /\ src # dst
    /\ eid \in EventIds \ used_ids
    /\ used_ids' = used_ids \cup {eid}
    \* /\ event_log' = Append(event_log, <<SEND, eid, src, dst>>)
    /\ event_log' = [event_log EXCEPT ![src] = 
        Append(event_log[src], <<SEND, eid, src, dst>>)]
    /\ event_queue' = Append(event_queue, <<SEND, eid, src, dst>>)
    /\ UNCHANGED <<lc, to_recv, to_resolve>>
    /\ UNCHANGED protocol_vars

TriggerRecv(send_timestamp, eid, src, dst) ==
    /\ send_timestamp \in Timestamps
    /\ <<send_timestamp, eid, src, dst>> \in to_recv
    /\ to_recv' = to_recv \ {<<send_timestamp, eid, src, dst>>}
    \* /\ event_log' = Append(event_log, <<RECV, eid, src, dst>>)
    /\ event_log' = [event_log EXCEPT ![dst] = 
        Append(event_log[dst], <<RECV, eid, src, dst>>)]
    /\ event_queue' = Append(
        event_queue, <<RECV, send_timestamp, eid, src, dst>>)
    /\ lc' = [lc EXCEPT ![<<SEND, eid, src, dst>>] = <<send_timestamp>>]
    /\ UNCHANGED <<used_ids, to_resolve>>
    /\ UNCHANGED protocol_vars

Resolve(recv_timestamp, eid, src, dst) ==
    /\ recv_timestamp \in Timestamps
    /\ <<recv_timestamp, eid, src, dst>> \in to_resolve
    /\ to_resolve' = to_resolve \ {<<recv_timestamp, eid, src, dst>>}
    /\ lc' = [lc EXCEPT ![<<RECV, eid, src, dst>>] = <<recv_timestamp>>]
    /\ UNCHANGED <<used_ids, event_log, event_queue, to_recv>>
    /\ UNCHANGED protocol_vars

\* The specification, bringing together both the protocol and the environment
Init == 
    /\ event_log = [p \in Procs |-> <<>>]
    /\ lc = [e \in Events |-> <<>>]
    /\ event_queue = <<>>
    /\ to_recv = {}
    /\ to_resolve = {}
    /\ used_ids = {}
    /\ proc_time = [p \in Procs |-> 1]

ProtocolNext == 
    \/ \E send_timestamp \in Timestamps, eid \in EventIds, src, dst \in Procs : 
        Send(send_timestamp, eid, src, dst)
    \/ \E send_timestamp, recv_timestamp \in Timestamps, 
            eid \in EventIds, 
            src, dst \in Procs : 
        Recv(send_timestamp, recv_timestamp, eid, src, dst)

EnvironmentNext ==
    \/ \E eid \in EventIds, src, dst \in Procs : TriggerSend(eid, src, dst)
    \/ \E send_timestamp \in Timestamps, 
            eid \in EventIds, 
            src, dst \in Procs : 
        TriggerRecv(send_timestamp, eid, src, dst)
    \/ \E recv_timestamp \in Timestamps, 
            eid \in EventIds, 
            src, dst \in Procs : 
        Resolve(recv_timestamp, eid, src, dst)

Finished == 
    /\ used_ids' = EventIds
    /\ UNCHANGED vars

Next == ProtocolNext \/ EnvironmentNext \/ Finished

Spec == 
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(ProtocolNext)
    /\ SF_vars(EnvironmentNext)


\* The auxiliary operators used to write the top-level safety property
\* Perhaps a bit verbose, but hopefully more readable
SendOfRecv(e1, e2) ==
    LET T1 == e1[1]
        T2 == e2[1] 
        eid1 == e1[2]
        eid2 == e2[2]
        src1 == e1[3]
        src2 == e2[3] 
        dst1 == e1[4]
        dst2 == e2[4]
    IN 
        /\ T1 = SEND 
        /\ T2 = RECV 
        /\ eid1 = eid2
        /\ src1 = src2 
        /\ dst1 = dst2

CoLocated(e1, e2) == 
    LET T1 == e1[1]
        T2 == e2[1] 
        src1 == e1[3]
        src2 == e2[3] 
        dst1 == e1[4]
        dst2 == e2[4]
    IN 
        \/ T1 = SEND /\ T2 = SEND /\ src1 = src2
        \/ T1 = RECV /\ T2 = RECV /\ dst1 = dst2
        \/ T1 = SEND /\ T2 = RECV /\ src1 = dst2
        \/ T1 = RECV /\ T2 = SEND /\ dst1 = src2

Happened(e1) ==
    LET T == e1[1]
        src == e1[3]
        dst == e1[4]
    IN
        \/ T = SEND /\ InSequence(e1, event_log[src]) 
        \/ T = RECV /\ InSequence(e1, event_log[dst])

Before(e1, e2) ==
    \/ SendOfRecv(e1, e2)
    \/ 
        /\ 
            \/ e1[1] = SEND /\ IndexBefore(e1, e2, event_log[e1[3]])
            \/ e1[1] = RECV /\ IndexBefore(e1, e2, event_log[e1[4]])
        /\ CoLocated(e1, e2)

HappenedBefore(e1, e2) == 
    /\ Happened(e1)
    /\ Happened(e2)
    /\ Before(e1, e2)

LogicClockBefore(e1, e2) == lc[e1][1] < lc[e2][1]

\* The top-level safety property
Safety == \A e1, e2 \in Events :
    (/\ InMap(e1, lc)
    /\ InMap(e2, lc)
    /\ HappenedBefore(e1, e2)
    ) => LogicClockBefore(e1, e2)

Liveness == \forall e \in Events : 
    [](Happened(e) => <>InMap(e, lc))

====
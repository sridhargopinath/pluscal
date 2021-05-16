--------------------- MODULE Mutex ------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, MaxClock

Pid == 1 .. N
ClockVal == 0 .. MaxClock+1
Message == [time: ClockVal, type: {"Request", "Release", "AckReq"}]

(*--algorithm LogicalClocks

variables
  channel = [source \in Pid |-> [destination \in Pid |-> <<>>]],
  crit = {}

define
  LogClockLt(reqs, p, q) ==
    \/ reqs[q] = 0
    \/ reqs[p] < reqs[q]
    \/ reqs[p] = reqs[q] /\ p < q

  ChanHead(dst, type) ==
    {src \in Pid: /\ Len(channel[src][dst]) > 0
                  /\ Head(channel[src][dst]).type = type
    }
   
  Max(a, b) == IF a <= b THEN b ELSE a
end define

macro Receive(type, clock, src, time) begin
  with s \in ChanHead(self, type) do
    src := s;
    time := Head(channel[src][self]).time;
    channel := [channel EXCEPT ![src][self] = Tail(channel[src][self])]
  end with
end macro

macro Broadcast(clock, msg) begin
  channel :=
    [channel EXCEPT ![self] =
      [dst \in Pid |->
        IF dst = self THEN channel[self][self]
                      ELSE Append(channel[self][dst], msg)]]
end macro

macro SendTo(clock, dst, msg) begin
  channel :=
    [channel EXCEPT ![self][dst] = Append(channel[self][dst], msg)]
end macro

macro EnterCritSec() begin
  crit := crit \union {self}
end macro

macro ExitCritSec() begin
  crit := crit \ {self}
end macro

process Proc \in Pid
variables
  clock = 1,
  acks = {},
  requests = [pid \in Pid |-> 0],
  time,
  src

begin
  loop: while TRUE do
     either
        when requests[self] = 0;
          Broadcast(clock, [time |-> clock, type |-> "Request"]);
          requests := [requests EXCEPT ![self] = clock];
          acks := {self}
     or
        Receive("AckReq", clock, src, time);
          clock := Max(clock, time);
          acks := acks \union {src}          
     or
        when /\ self \notin crit
             /\ acks = Pid
             /\ \A p \in Pid: p # self =>
                                  LogClockLt(requests, self, p);
          EnterCritSec();
     or
        when self \in crit;
          requests := [requests EXCEPT ![self] = 0];
          ExitCritSec();
          acks := {};
          Broadcast(clock, [time |-> clock, type |-> "Release"])

     or
        Receive("Request", clock, src, time);
          requests := [requests EXCEPT ![src] = time];
          clock := Max(clock, time);
      L2: SendTo(clock, src, [time |-> clock+1, type |-> "AckReq"])
     or
        Receive("Release", clock, src, time);
          clock := Max(clock, time);
          requests := [requests EXCEPT ![src] = 0];
     end either;
     tic: clock := clock + 1
   end while;
end process

end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "eb5ff142" /\ chksum(tla) = "bc5fba51")
CONSTANT defaultInitValue
VARIABLES channel, crit, pc

(* define statement *)
LogClockLt(reqs, p, q) ==
  \/ reqs[q] = 0
  \/ reqs[p] < reqs[q]
  \/ reqs[p] = reqs[q] /\ p < q

ChanHead(dst, type) ==
  {src \in Pid: /\ Len(channel[src][dst]) > 0
                /\ Head(channel[src][dst]).type = type
  }

Max(a, b) == IF a <= b THEN b ELSE a

VARIABLES clock, acks, requests, time, src

vars == << channel, crit, pc, clock, acks, requests, time, src >>

ProcSet == (Pid)

Init == (* Global variables *)
        /\ channel = [source \in Pid |-> [destination \in Pid |-> <<>>]]
        /\ crit = {}
        (* Process Proc *)
        /\ clock = [self \in Pid |-> 1]
        /\ acks = [self \in Pid |-> {}]
        /\ requests = [self \in Pid |-> [pid \in Pid |-> 0]]
        /\ time = [self \in Pid |-> defaultInitValue]
        /\ src = [self \in Pid |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "loop"]

loop(self) == /\ pc[self] = "loop"
              /\ \/ /\ requests[self][self] = 0
                    /\ channel' = [channel EXCEPT ![self] =
                                    [dst \in Pid |->
                                      IF dst = self THEN channel[self][self]
                                                    ELSE Append(channel[self][dst], ([time |-> clock[self], type |-> "Request"]))]]
                    /\ requests' = [requests EXCEPT ![self] = [requests[self] EXCEPT ![self] = clock[self]]]
                    /\ acks' = [acks EXCEPT ![self] = {self}]
                    /\ pc' = [pc EXCEPT ![self] = "tic"]
                    /\ UNCHANGED <<crit, clock, time, src>>
                 \/ /\ \E s \in ChanHead(self, "AckReq"):
                         /\ src' = [src EXCEPT ![self] = s]
                         /\ time' = [time EXCEPT ![self] = Head(channel[src'[self]][self]).time]
                         /\ channel' = [channel EXCEPT ![src'[self]][self] = Tail(channel[src'[self]][self])]
                    /\ clock' = [clock EXCEPT ![self] = Max(clock[self], time'[self])]
                    /\ acks' = [acks EXCEPT ![self] = acks[self] \union {src'[self]}]
                    /\ pc' = [pc EXCEPT ![self] = "tic"]
                    /\ UNCHANGED <<crit, requests>>
                 \/ /\ /\ self \notin crit
                       /\ acks[self] = Pid
                       /\ \A p \in Pid: p # self =>
                                            LogClockLt(requests[self], self, p)
                    /\ crit' = (crit \union {self})
                    /\ pc' = [pc EXCEPT ![self] = "tic"]
                    /\ UNCHANGED <<channel, clock, acks, requests, time, src>>
                 \/ /\ self \in crit
                    /\ requests' = [requests EXCEPT ![self] = [requests[self] EXCEPT ![self] = 0]]
                    /\ crit' = crit \ {self}
                    /\ acks' = [acks EXCEPT ![self] = {}]
                    /\ channel' = [channel EXCEPT ![self] =
                                    [dst \in Pid |->
                                      IF dst = self THEN channel[self][self]
                                                    ELSE Append(channel[self][dst], ([time |-> clock[self], type |-> "Release"]))]]
                    /\ pc' = [pc EXCEPT ![self] = "tic"]
                    /\ UNCHANGED <<clock, time, src>>
                 \/ /\ \E s \in ChanHead(self, "Request"):
                         /\ src' = [src EXCEPT ![self] = s]
                         /\ time' = [time EXCEPT ![self] = Head(channel[src'[self]][self]).time]
                         /\ channel' = [channel EXCEPT ![src'[self]][self] = Tail(channel[src'[self]][self])]
                    /\ requests' = [requests EXCEPT ![self] = [requests[self] EXCEPT ![src'[self]] = time'[self]]]
                    /\ clock' = [clock EXCEPT ![self] = Max(clock[self], time'[self])]
                    /\ pc' = [pc EXCEPT ![self] = "L2"]
                    /\ UNCHANGED <<crit, acks>>
                 \/ /\ \E s \in ChanHead(self, "Release"):
                         /\ src' = [src EXCEPT ![self] = s]
                         /\ time' = [time EXCEPT ![self] = Head(channel[src'[self]][self]).time]
                         /\ channel' = [channel EXCEPT ![src'[self]][self] = Tail(channel[src'[self]][self])]
                    /\ clock' = [clock EXCEPT ![self] = Max(clock[self], time'[self])]
                    /\ requests' = [requests EXCEPT ![self] = [requests[self] EXCEPT ![src'[self]] = 0]]
                    /\ pc' = [pc EXCEPT ![self] = "tic"]
                    /\ UNCHANGED <<crit, acks>>

tic(self) == /\ pc[self] = "tic"
             /\ clock' = [clock EXCEPT ![self] = clock[self] + 1]
             /\ pc' = [pc EXCEPT ![self] = "loop"]
             /\ UNCHANGED << channel, crit, acks, requests, time, src >>

L2(self) == /\ pc[self] = "L2"
            /\ channel' = [channel EXCEPT ![self][src[self]] = Append(channel[self][src[self]], ([time |-> clock[self]+1, type |-> "AckReq"]))]
            /\ pc' = [pc EXCEPT ![self] = "tic"]
            /\ UNCHANGED << crit, clock, acks, requests, time, src >>

Proc(self) == loop(self) \/ tic(self) \/ L2(self)

Next == (\E self \in Pid: Proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

View == <<channel, crit, clock, acks, requests, pc>>

MutualExclusion == Cardinality(crit) < 2

====

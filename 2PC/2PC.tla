-------------------------------- MODULE 2PC --------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANT RM,      \* The set of participating resource managers RM=1..3 
         RMMAYFAIL,
         BYZRM,
         TMMAYFAIL \* Whether TM may fail MAYFAIL=TRUE or FALSE

(***************************************************************************
--algorithm TransactionCommit {
  variable rmState = [rm \in RM |-> "working"],
           tmState = "init";
  define {
    canCommit ==    \A rmc \in RM: rmState[rmc] \in {"prepared"} 
                 \/ \E rm \in RM : rmState[rm] \in {"committed"} \* for when BTM takes over
    canAbort ==     \E rm \in RM : rmState[rm] \in {"aborted","failed"} 
                /\ ~\E rmc \in RM : rmState[rmc]= "committed"  \* inconsistent if commented
   }
  
  macro Prepare(p) {
    await rmState[p] = "working";
    rmState[p] := "prepared" ; }
   
  macro Decide(p) {
    either { await tmState="commit";
             rmState[p] := "committed";}
             \* if (BYZRM) either rmState[p] := "committed" or rmState[p] := "aborted";}
    or     { await rmState[p]="working" \/ tmState="abort";
             rmState[p] := "aborted";}  
   }
  
  macro Fail(p) {
    if (RMMAYFAIL) rmState[p] := "failed";
   }
  
  fair process (RManager \in RM) {
   RS: while (rmState[self] \in {"working", "prepared"}) { 
         either Prepare(self) or Decide(self) or Fail(self)}
   }
  
  fair process (TManager=0) {
 TS:either{ await canCommit;
        TC: tmState := "commit";
        F1: if (TMMAYFAIL) tmState := "hidden";} 
    
    or { await canAbort;
     TA: tmState := "abort";
     F2: if (TMMAYFAIL) tmState := "hidden";}  
   }
   
}
***************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "a382282b" /\ chksum(tla) = "a9646dee")
VARIABLES rmState, tmState, pc

(* define statement *)
canCommit ==    \A rmc \in RM: rmState[rmc] \in {"prepared"}
             \/ \E rm \in RM : rmState[rm] \in {"committed"}
canAbort ==     \E rm \in RM : rmState[rm] \in {"aborted","failed"}
            /\ ~\E rmc \in RM : rmState[rmc]= "committed"


vars == << rmState, tmState, pc >>

ProcSet == (RM) \cup {0}

Init == (* Global variables *)
        /\ rmState = [rm \in RM |-> "working"]
        /\ tmState = "init"
        /\ pc = [self \in ProcSet |-> CASE self \in RM -> "RS"
                                        [] self = 0 -> "TS"]

RS(self) == /\ pc[self] = "RS"
            /\ IF rmState[self] \in {"working", "prepared"}
                  THEN /\ \/ /\ rmState[self] = "working"
                             /\ rmState' = [rmState EXCEPT ![self] = "prepared"]
                          \/ /\ \/ /\ tmState="commit"
                                   /\ rmState' = [rmState EXCEPT ![self] = "committed"]
                                \/ /\ rmState[self]="working" \/ tmState="abort"
                                   /\ rmState' = [rmState EXCEPT ![self] = "aborted"]
                          \/ /\ IF RMMAYFAIL
                                   THEN /\ rmState' = [rmState EXCEPT ![self] = "failed"]
                                   ELSE /\ TRUE
                                        /\ UNCHANGED rmState
                       /\ pc' = [pc EXCEPT ![self] = "RS"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED rmState
            /\ UNCHANGED tmState

RManager(self) == RS(self)

TS == /\ pc[0] = "TS"
      /\ \/ /\ canCommit
            /\ pc' = [pc EXCEPT ![0] = "TC"]
         \/ /\ canAbort
            /\ pc' = [pc EXCEPT ![0] = "TA"]
      /\ UNCHANGED << rmState, tmState >>

TC == /\ pc[0] = "TC"
      /\ tmState' = "commit"
      /\ pc' = [pc EXCEPT ![0] = "F1"]
      /\ UNCHANGED rmState

F1 == /\ pc[0] = "F1"
      /\ IF TMMAYFAIL
            THEN /\ tmState' = "hidden"
            ELSE /\ TRUE
                 /\ UNCHANGED tmState
      /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ UNCHANGED rmState

TA == /\ pc[0] = "TA"
      /\ tmState' = "abort"
      /\ pc' = [pc EXCEPT ![0] = "F2"]
      /\ UNCHANGED rmState

F2 == /\ pc[0] = "F2"
      /\ IF TMMAYFAIL
            THEN /\ tmState' = "hidden"
            ELSE /\ TRUE
                 /\ UNCHANGED tmState
      /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ UNCHANGED rmState

TManager == TS \/ TC \/ F1 \/ TA \/ F2

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == TManager
           \/ (\E self \in RM: RManager(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in RM : WF_vars(RManager(self))
        /\ WF_vars(TManager)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Sat May 15 23:25:58 CDT 2021 by sridhar
\* Created Sat May 15 23:23:14 CDT 2021 by sridhar

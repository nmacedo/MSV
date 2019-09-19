------------------------------ MODULE Peterson ------------------------------

EXTENDS Naturals

VARIABLES turn, flag, pc

-----------------------------------------------------------------------------

vars == <<turn,flag,pc>>

TypeInv == /\ turn \in 0..1 (* turn is assigned to of the two processes *) 
           /\ flag \in [0..1 -> BOOLEAN] (* their intention to enter the critical zone *) 
           /\ pc \in [0..1 -> 0..5] (* the program counter of each process. *)
           
Init == /\ turn \in 0..1 (* it isn't relevant to which process the turn is initially assinged *)
        /\ flag = [p \in 0..1 |-> FALSE] (* initially set to false *)
        /\ pc = [p \in 0..1 |-> 0] (* start at the beginning of the algorithm *)
        
(* each predicate, parametrized by the process, denotes a step of the algorithm.
   the pre-condition is that the process is at the adequate point. *)
P0(p) == /\ pc[p] = 0         
         /\ flag' = [flag EXCEPT ![p] = TRUE]
         /\ pc' = [pc EXCEPT ![p] = 1]
         /\ UNCHANGED<<turn>>

P1(p) == /\ pc[p] = 1
         /\ turn' = 1 - p
         /\ pc' = [pc EXCEPT ![p] = 2]
         /\ UNCHANGED<<flag>>
         
P2(p) == /\ pc[p] = 2
         /\ pc' = [pc EXCEPT ![p] = IF flag[1-p] /\ turn = 1-p THEN pc[p]
                                                               ELSE 3]
         /\ UNCHANGED<<flag,turn>>

P3(p) == /\ pc[p] = 3
         /\ pc' = [pc EXCEPT ![p] = 4]
         /\ UNCHANGED<<flag,turn>>

P4(p) == /\ pc[p] = 4
         /\ pc' = [pc EXCEPT ![p] = 5]
         /\ flag' = [flag EXCEPT ![p] = FALSE]
         /\ UNCHANGED<<turn>>
         
P5(p) == /\ pc[p] = 5
         /\ pc' = [pc EXCEPT ![p] = 0]
         /\ UNCHANGED<<turn,flag>>

(* acting is performing one of the steps *)
Act(p) == P0(p) \/ P1(p) \/ P2(p) \/ P3(p) \/ P4(p) \/ P5(p)

(* the system evolves by having one of the proccesses act *)           
Next == Act(0) \/ Act(1)

(* initial, next and fairness conditions.
   there is justice towards both processes. *)
Spec == /\ Init 
        /\ [][Next]_vars
        /\ WF_vars(Act(0))
        /\ WF_vars(Act(1))
        
-----------------------------------------------------------------------------

(* aliases for program counters *)
CRITICAL(p) == pc[p] = 3
START(p) == pc[p] = 0

(* the two processes aren't at the critical section simultaneously *)
Safety == []~(CRITICAL(0) /\ CRITICAL(1))

(* both processes eventually reach the critical section *)
Liveness == ([] START(0) => <>CRITICAL(0)) /\ ([] START(1) => <>CRITICAL(1))

=============================================================================
\* Modification History
\* Last modified Wed Nov 04 16:05:12 WET 2015 by nmm
\* Created Thu Oct 29 09:03:34 WET 2015 by nmm

--------------------------------- MODULE Ring -------------------------------

EXTENDS Naturals, Integers

(* the maximum number of processes *)
CONSTANT N  

(* which should be a natural *)
ASSUME N \in Nat /\ N > 0

(* remainder variables of the model. *)
VARIABLES toSend, succ, elected

-----------------------------------------------------------------------------

vars == <<toSend,succ,elected>> 

(* definition of transitive closure as borrowed from the example packaged 
   with TLC *)
Support(R) == {r[1] : r \in R} \cup {r[2] : r \in R}

R ** T == LET SR == Support(R)
              ST == Support(T)
          IN  {<<r, t>> \in SR \X ST : 
                \E s \in SR \cap ST : (<<r, s>> \in R) /\ (<<s, t>> \in T)}
                    
RECURSIVE TC(_)
TC(R) == LET RR == R ** R
         IN IF RR \subseteq R THEN R ELSE TC(R \cup RR)                            

(* TC is only applicable to relations: converts a function into a relation *)
Rel(f) == { <<r,f[r]>> : r \in DOMAIN f }

(* the set of N processes *)
PROCESS == 0..(N - 1) 

(* the initial state of the problem *)
Init == /\ succ \in [PROCESS -> PROCESS] (* denotes the next process in the ring *)
        /\ \A p1,p2 \in PROCESS : <<p1,p2>> \in TC(Rel(succ)) (* succ must form a ring *)
        /\ toSend = [p \in PROCESS |-> p] (* initially only sends its own identifier *)
        /\ elected = {} (* initially no one is elected *)

(* the step that makes each process act.     
   at each step, the identifier in toSend is either discarded or sent to the succeeding process.
   if the receiver receives its own identifier, it is elected a leader.
   succ is never modified. *)
Act(p) == /\ p \in PROCESS
          /\ toSend' = [toSend EXCEPT ![succ[p]] = IF toSend[succ[p]] < toSend[p] THEN toSend[p] 
                                                                                  ELSE @] 
          /\ elected' = IF toSend[p] = succ[p] THEN elected \cup {succ[p]} 
                                               ELSE elected    
          /\ UNCHANGED <<succ>>

(* at each state, one of the processes acts *)
Next == \E p \in PROCESS : Act(p)

(* initial, next and fairness constraints.
   there is justice towards every process. *)
Spec == /\ Init 
        /\ [][Next]_vars
        /\ \A p \in PROCESS : WF_vars(Act(p))

-----------------------------------------------------------------------------

(* a process is eventually elected leader *)
Liveness == <>(elected /= {})

(* no two different processes are every elected leader *)
Safety == [](\A i1,i2 \in elected : i1 = i2)

=============================================================================

\* Modification History
\* Last modified Wed Nov 04 16:02:56 WET 2015 by nmm
\* Created Mon Feb 23 12:03:05 WET 2015 by nmm

------------------------------- MODULE Hotel_new_s5 -------------------------------
EXTENDS Naturals 
CONSTANT KEY, Room, Guest
ASSUME KEY \in Nat
VARIABLE current, last, occupant, gkeys
-----------------------------------------------------------------------------

Key == 0..KEY-1

keys == [r0 |-> {0}, r1 |-> {1,2,3}]

TypeInv == /\ current \in [Room -> Key]
           /\ \A r \in Room : current[r] \in keys[r]
           /\ last \in [Room -> Key]
           /\ occupant \in [Room -> SUBSET Guest]
           /\ gkeys \in [Guest -> SUBSET Key]
           
Init == /\ current \in [Room -> Key]
        /\ \A r \in Room : current[r] \in keys[r]
        /\ last = current
        /\ occupant = [r \in Room |-> {}]
        /\ gkeys = [g \in Guest |-> {}]

vs == <<current,last,occupant,gkeys>>
       
nextKey[k \in Key, ks \in SUBSET Key] == {x \in ks : x > k /\ (\A y \in ks : y > k => x <= y)} 

Entry(g,r,k) == /\ k \in gkeys[g]
                /\ (k = current[r] \/ {k} = nextKey[current[r],keys[r]])
                /\ current' = [current EXCEPT ![r] = k]
                /\ UNCHANGED<<last,occupant,gkeys>>
                
Checkout(g) == /\ \E r \in Room : g \in occupant[r]
               /\ occupant' = [r \in DOMAIN occupant |-> occupant[r] \ {g}]
               /\ UNCHANGED<<last,current,gkeys>>
                              
Checkin(g,r,k) == /\ occupant[r] = {}
                  /\ {k} = nextKey[last[r],keys[r]]
                  /\ occupant' = [occupant EXCEPT ![r] = {g}]
                  /\ gkeys' = [gkeys EXCEPT ![g] = @ \cup {k}]
                  /\ last' = [last EXCEPT ![r] = k]
                  /\ UNCHANGED<<current>>

PostCheckin(g,r,k) == /\ occupant[r] = {g}
                      /\ k \in gkeys[g]
                      /\ last[r] = k
                      /\ current[r] # k \* without this NoIntervenes causes an error if tested after Next
                 
Act == \E g \in Guest : Checkout(g) \/ \E r \in Room, k \in Key : Entry(g,r,k) \/ Checkin(g,r,k)

NoIntervenes == \A g \in Guest, k \in Key, r \in Room : PostCheckin(g,r,k) => Entry(g,r,k)

Spec == Init /\ [][Act /\ TypeInv /\ NoIntervenes]_vs

Spec2 == Init /\ [][Act]_vs

-----------------------------------------------------------------------------

NoBadEntries == 
  [][\A g \in Guest, r \in Room, k \in Key : Entry(g,r,k) /\ occupant[r] # {} => g \in occupant[r]]_vs

Sanity == 
  []~((\E r1,r2 \in Room : occupant[r1] # {} /\ occupant[r2] # {} /\ occupant[r1] # occupant[r2]))
  
=============================================================================
\* Modification History
\* Last modified Tue Jan 12 16:52:23 WET 2016 by nmm
\* Created Fri Feb 27 09:57:00 WET 2015 by nmm

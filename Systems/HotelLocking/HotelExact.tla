\* Author: Nuno Macedo

------------------------------- MODULE HotelExact -------------------------------
EXTENDS Naturals 
CONSTANT KEY, Room, Guest
ASSUME KEY \in Nat
VARIABLE keys, currentKey, lastKey, occupant, gkeys
-----------------------------------------------------------------------------

Key == 0..KEY-1

TypeInv == /\ keys \in [Room -> SUBSET Key]
           /\ currentKey \in [Room -> Key]
           /\ \A r \in Room : currentKey[r] \in keys[r]
           /\ \A r1,r2 \in Room : (keys[r1] \cap keys[r2]) # {} => r1 = r2
           /\ lastKey \in [Room -> Key]
           /\ occupant \in [Room -> SUBSET Guest]
           /\ gkeys \in [Guest -> SUBSET Key]
           
Init == /\ keys \in [Room -> SUBSET Key]
        /\ currentKey \in [Room -> Key]
        /\ \A r1,r2 \in Room : (keys[r1] \cap keys[r2]) # {} => r1 = r2
        /\ \A r \in Room : currentKey[r] \in keys[r]
        /\ lastKey = currentKey
        /\ occupant = [r \in Room |-> {}]
        /\ gkeys = [g \in Guest |-> {}]

vars == <<keys,currentKey,lastKey,occupant,gkeys>>
       
nextKey[k \in Key, ks \in SUBSET Key] == LET nexts == ks \ (0..k)
                                         IN {x \in nexts : \A y \in nexts : x <= y} 

Entry(g,r,k) == /\ (k = currentKey[r] \/ {k} = nextKey[currentKey[r],keys[r]])
                /\ k \in gkeys[g]
                /\ currentKey' = [currentKey EXCEPT ![r] = k]
                /\ UNCHANGED<<keys,lastKey,occupant,gkeys>>
                
Checkout(g) == /\ \E r \in Room : g \in occupant[r]
               /\ occupant' = [r \in DOMAIN occupant |-> occupant[r] \ {g}]
               /\ UNCHANGED<<keys,lastKey,currentKey,gkeys>>
                              
Checkin(g,r,k) == /\ occupant[r] = {}
                  /\ {k} = nextKey[lastKey[r],keys[r]]
                  /\ occupant' = [occupant EXCEPT ![r] = @ \cup {g}]
                  /\ gkeys' = [gkeys EXCEPT ![g] = @ \cup {k}]
                  /\ lastKey' = [lastKey EXCEPT ![r] = k]
                  /\ UNCHANGED<<keys,currentKey>>

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
\* Last modified Tue Mar 31 10:56:47 WEST 2015 by nmm
\* Created Fri Feb 27 09:57:00 WET 2015 by nmm
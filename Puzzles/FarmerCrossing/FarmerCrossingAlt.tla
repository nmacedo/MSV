\* Author: Nuno Macedo

-------------------------- MODULE FarmerCrossingAlt -------------------------

VARIABLE farmer, goose, wolf, beans

-----------------------------------------------------------------------------

vars == <<goose,beans,wolf,farmer>>

(* the farmer and the purchases are on one of the banks of the river *)
TypeInv == /\ farmer \in BOOLEAN
           /\ goose \in BOOLEAN
           /\ wolf \in BOOLEAN
           /\ beans \in BOOLEAN
           
(* the farmer and the purchases begin in the left bank of the river *)
Init == /\ farmer = FALSE
        /\ goose = FALSE
        /\ wolf = FALSE
        /\ beans = FALSE

(* the farmer may cross the river alone or with one of the purchases *)
GoAlone == /\ farmer' = ~ farmer
           /\ UNCHANGED<<wolf,goose,beans>>

GoBeans == /\ farmer = beans
           /\ farmer' = ~ farmer
           /\ beans' = ~ beans
           /\ UNCHANGED<<wolf,goose>>

GoGoose == /\ farmer = goose
           /\ farmer' = ~ farmer
           /\ goose' = ~ goose
           /\ UNCHANGED<<wolf,beans>>

GoWolf == /\ farmer = wolf
          /\ farmer' = ~ farmer
          /\ wolf' = ~ wolf
          /\ UNCHANGED<<goose,beans>>

(* dangerous situations will not be reached *)
\* This should work as an ACTION-CONSTRAINT but it doesn't
Danger == goose # farmer /\ (goose = wolf \/ goose = beans)

(* the state evolves by crossing *)
Next == \/ GoAlone \/ GoBeans 
        \/ GoGoose \/ GoWolf 
        

-----------------------------------------------------------------------------

(* defines the initial state and the actions assuming no dangerous situations
   will be reached, always under stuttering *)
Spec == Init /\ [][Next /\ ~Danger']_vars

Goal == []~(farmer /\ goose /\ wolf /\ beans)

=============================================================================
\* Modification History
\* Last modified Wed Oct 28 22:01:59 WET 2015 by nmm
\* Created Wed Oct 14 18:34:20 WEST 2015 by nmm

\* Author: Nuno Macedo

--------------------------- MODULE FarmerCrossing ---------------------------

VARIABLE farmer, goose, wolf, beans, eaten_goose, eaten_beans

-----------------------------------------------------------------------------

vars == <<goose,beans,wolf,farmer,eaten_goose,eaten_beans>>

(* the farmer and the purchases are on one of the banks of the river, and the 
   goose and the beans may or not have been eaten *)
TypeInv == /\ farmer \in BOOLEAN
           /\ goose \in BOOLEAN
           /\ wolf \in BOOLEAN
           /\ beans \in BOOLEAN
           /\ eaten_goose \in BOOLEAN
           /\ eaten_beans \in BOOLEAN
           
(* the farmer and the purchases begin in the left bank of the river and 
   everyone is alive *)
Init == /\ farmer = FALSE
        /\ goose = FALSE
        /\ wolf = FALSE
        /\ beans = FALSE
        /\ eaten_goose = FALSE
        /\ eaten_beans = FALSE

(* the farmer may cross the river alone or with one of the purchases *)
GoAlone == /\ farmer' = ~ farmer
           /\ UNCHANGED<<wolf,goose,beans,eaten_goose,eaten_beans>>

GoBeans == /\ farmer = beans
           /\ farmer' = ~ farmer
           /\ beans' = ~ beans
           /\ UNCHANGED<<wolf,goose,eaten_goose,eaten_beans>>

GoGoose == /\ farmer = goose
           /\ farmer' = ~ farmer
           /\ goose' = ~ goose
           /\ UNCHANGED<<wolf,beans,eaten_goose,eaten_beans>>

GoWolf == /\ farmer = wolf
          /\ farmer' = ~ farmer
          /\ wolf' = ~ wolf
          /\ UNCHANGED<<goose,beans,eaten_goose,eaten_beans>>

(* if the farmer does not avoid danger situations something may be eaten *)
EatGoose == /\ wolf = goose
            /\ eaten_goose = FALSE
            /\ wolf = ~farmer
            /\ eaten_goose' = TRUE
            /\ UNCHANGED<<goose,beans,wolf,farmer,eaten_beans>>

EatBeans == /\ beans = goose
            /\ eaten_beans = FALSE
            /\ goose = ~farmer
            /\ eaten_beans' = TRUE
            /\ UNCHANGED<<goose,beans,wolf,farmer,eaten_goose>>

(* if there is anything that can be eaten, it will *)
\* This should work as an ACTION-CONSTRAINT but it doesn't
ForceEat == (ENABLED EatBeans \/ ENABLED EatGoose) => (EatGoose \/ EatBeans)

(* the state evolves by crossing and eating *)
Next == \/ GoAlone \/ GoBeans 
        \/ GoGoose \/ GoWolf 
        \/ EatGoose \/ EatBeans
        
-----------------------------------------------------------------------------

(* defines the initial state and the actions forcing eating, always under 
   stuttering *)
Spec == Init /\ [][Next /\ ForceEat]_vars

Goal == []~(farmer /\ goose /\ wolf /\ beans /\ ~eaten_beans /\ ~eaten_goose)

=============================================================================
\* Modification History
\* Last modified Wed Oct 28 22:02:36 WET 2015 by nmm
\* Created Wed Oct 14 18:34:20 WEST 2015 by nmm

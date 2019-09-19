\* Author: Nuno Macedo

----------------------------- MODULE HeavyChair -----------------------------

EXTENDS Naturals

VARIABLES pos_x, pos_y, dir
CONSTANTS N

-----------------------------------------------------------------------------

(* the size of the board is a natural, and should be at least 2x2 for the 
   chair to move *)
ASSUME N \in Nat /\ N > 0

(* the initial position is in the middle of the board *)
pos_init == N \div 2

(* the chair is within the size board and there are 4 directions (not 
   relevant which) *)
TypeInv == /\ pos_x \in 0 .. N
           /\ pos_y \in 0 .. N
           /\ dir \in 0 .. 3
           
(* the initial position is in the middle of the board pointing 0 *)
Init == /\ pos_x = pos_init
        /\ pos_y = pos_init
        /\ dir = 0
        
(* the 8 operations rotate the chair on one of the legs either in clockwise
   or anti-clockwise direction *)
Rot_TL_Cw == /\ pos_x' = pos_x - 1
             /\ dir' = (dir + 1) % 4
             /\ UNCHANGED<<pos_y>>

Rot_TL_Aw == /\ pos_y' = pos_y + 1
             /\ dir' = (dir - 1) % 4
             /\ UNCHANGED<<pos_x>>

Rot_TR_Cw == /\ pos_y' = pos_y + 1
             /\ dir' = (dir + 1) % 4
             /\ UNCHANGED<<pos_x>>

Rot_TR_Aw == /\ pos_x' = pos_x + 1
             /\ dir' = (dir - 1) % 4
             /\ UNCHANGED<<pos_y>>

Rot_BL_Cw == /\ pos_y' = pos_y - 1
             /\ dir' = (dir + 1) % 4
             /\ UNCHANGED<<pos_x>>

Rot_BL_Aw == /\ pos_x' = pos_x - 1
             /\ dir' = (dir - 1) % 4
             /\ UNCHANGED<<pos_y>>

Rot_BR_Cw == /\ pos_x' = pos_x + 1
             /\ dir' = (dir + 1) % 4
             /\ UNCHANGED<<pos_y>>

Rot_BR_Aw == /\ pos_y' = pos_y - 1
             /\ dir' = (dir - 1) % 4
             /\ UNCHANGED<<pos_x>>

(* the state evolves by applying rotations *)
Next == \/ Rot_TL_Cw \/ Rot_TL_Aw 
        \/ Rot_TR_Cw \/ Rot_TR_Aw
        \/ Rot_BL_Cw \/ Rot_BL_Aw
        \/ Rot_BR_Cw \/ Rot_BR_Aw

(* do not allow the position of the chair in the next state to fall 
   outside the board *)
\* This should work as an ACTION-CONSTRAINT but it doesn't
Bounded == 0 <= pos_x' /\ pos_x' <= N /\ 0 <= pos_y' /\ pos_y' <= N

-----------------------------------------------------------------------------
             
(* defines the initial state and the bounded actions, always under stuttering *)
Spec == Init /\ [][Next /\ Bounded]_<<pos_x,pos_y,dir>>

(* the goal of the puzzle: move the chair to the adjacent position and preserve
   the direction *)
Goal == []~(pos_x = pos_init /\ pos_y = pos_init + 1 /\ dir = 0)

(* sanity check, see the chair actually moving *)
SanityCheck == []~(pos_x = pos_init + 1 /\ pos_y = pos_init + 1 /\ dir = 0)

=============================================================================
\* Modification History
\* Last modified Wed Oct 28 21:34:50 WET 2015 by nmm
\* Created Tue Oct 20 15:27:59 WEST 2015 by nmm

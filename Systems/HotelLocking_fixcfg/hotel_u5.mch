MACHINE hotel
/** author: Nuno Macedo, 2016 */

SETS
  GUEST_ = {g1,g2,g3,g4};
  ROOM_ = {r1,r2,r3,r4}

DEFINITIONS
  /** Universal quantifications can only be used in atomic propositions, so calls to operations must be expanded. */
  ASSERT_LTL_BAD  == "G (
			(([Entry(g1,r1,1)] & {occupant(r1) /= {}}) => {g1 : occupant(r1)}) &
			(([Entry(g1,r1,2)] & {occupant(r1) /= {}}) => {g1 : occupant(r1)}) &
			(([Entry(g1,r1,3)] & {occupant(r1) /= {}}) => {g1 : occupant(r1)}) &
			(([Entry(g1,r1,4)] & {occupant(r1) /= {}}) => {g1 : occupant(r1)}) &
			(([Entry(g1,r2,1)] & {occupant(r2) /= {}}) => {g1 : occupant(r2)}) &
			(([Entry(g1,r2,2)] & {occupant(r2) /= {}}) => {g1 : occupant(r2)}) &
			(([Entry(g1,r2,3)] & {occupant(r2) /= {}}) => {g1 : occupant(r2)}) &
			(([Entry(g1,r2,4)] & {occupant(r2) /= {}}) => {g1 : occupant(r2)}) &
			(([Entry(g1,r3,1)] & {occupant(r3) /= {}}) => {g1 : occupant(r3)}) &
			(([Entry(g1,r3,2)] & {occupant(r3) /= {}}) => {g1 : occupant(r3)}) &
			(([Entry(g1,r3,3)] & {occupant(r3) /= {}}) => {g1 : occupant(r3)}) &
			(([Entry(g1,r3,4)] & {occupant(r3) /= {}}) => {g1 : occupant(r3)}) &
			(([Entry(g1,r4,1)] & {occupant(r4) /= {}}) => {g1 : occupant(r4)}) &
			(([Entry(g1,r4,2)] & {occupant(r4) /= {}}) => {g1 : occupant(r4)}) &
			(([Entry(g1,r4,3)] & {occupant(r4) /= {}}) => {g1 : occupant(r4)}) &
			(([Entry(g1,r4,4)] & {occupant(r4) /= {}}) => {g1 : occupant(r4)}) &
		
			(([Entry(g2,r1,1)] & {occupant(r1) /= {}}) => {g2 : occupant(r1)}) &
			(([Entry(g2,r1,2)] & {occupant(r1) /= {}}) => {g2 : occupant(r1)}) &
			(([Entry(g2,r1,3)] & {occupant(r1) /= {}}) => {g2 : occupant(r1)}) &
			(([Entry(g2,r1,4)] & {occupant(r1) /= {}}) => {g2 : occupant(r1)}) &
			(([Entry(g2,r2,1)] & {occupant(r2) /= {}}) => {g2 : occupant(r2)}) &
			(([Entry(g2,r2,2)] & {occupant(r2) /= {}}) => {g2 : occupant(r2)}) &
			(([Entry(g2,r2,3)] & {occupant(r2) /= {}}) => {g2 : occupant(r2)}) &
			(([Entry(g2,r2,4)] & {occupant(r2) /= {}}) => {g2 : occupant(r2)}) &
			(([Entry(g2,r3,1)] & {occupant(r3) /= {}}) => {g2 : occupant(r3)}) &
			(([Entry(g2,r3,2)] & {occupant(r3) /= {}}) => {g2 : occupant(r3)}) &
			(([Entry(g2,r3,3)] & {occupant(r3) /= {}}) => {g2 : occupant(r3)}) &
			(([Entry(g2,r3,4)] & {occupant(r3) /= {}}) => {g2 : occupant(r3)}) &
			(([Entry(g2,r4,1)] & {occupant(r4) /= {}}) => {g2 : occupant(r4)}) &
			(([Entry(g2,r4,2)] & {occupant(r4) /= {}}) => {g2 : occupant(r4)}) &
			(([Entry(g2,r4,3)] & {occupant(r4) /= {}}) => {g2 : occupant(r4)}) &
			(([Entry(g2,r4,4)] & {occupant(r4) /= {}}) => {g2 : occupant(r4)}) &

			(([Entry(g3,r1,1)] & {occupant(r1) /= {}}) => {g3 : occupant(r1)}) &
			(([Entry(g3,r1,2)] & {occupant(r1) /= {}}) => {g3 : occupant(r1)}) &
			(([Entry(g3,r1,3)] & {occupant(r1) /= {}}) => {g3 : occupant(r1)}) &
			(([Entry(g3,r1,4)] & {occupant(r1) /= {}}) => {g3 : occupant(r1)}) &
			(([Entry(g3,r2,1)] & {occupant(r2) /= {}}) => {g3 : occupant(r2)}) &
			(([Entry(g3,r2,2)] & {occupant(r2) /= {}}) => {g3 : occupant(r2)}) &
			(([Entry(g3,r2,3)] & {occupant(r2) /= {}}) => {g3 : occupant(r2)}) &
			(([Entry(g3,r2,4)] & {occupant(r2) /= {}}) => {g3 : occupant(r2)}) &
			(([Entry(g3,r3,1)] & {occupant(r3) /= {}}) => {g3 : occupant(r3)}) &
			(([Entry(g3,r3,2)] & {occupant(r3) /= {}}) => {g3 : occupant(r3)}) &
			(([Entry(g3,r3,3)] & {occupant(r3) /= {}}) => {g3 : occupant(r3)}) &
			(([Entry(g3,r3,4)] & {occupant(r3) /= {}}) => {g3 : occupant(r3)}) &
			(([Entry(g3,r4,1)] & {occupant(r4) /= {}}) => {g3 : occupant(r4)}) &
			(([Entry(g3,r4,2)] & {occupant(r4) /= {}}) => {g3 : occupant(r4)}) &
			(([Entry(g3,r4,3)] & {occupant(r4) /= {}}) => {g3 : occupant(r4)}) &
			(([Entry(g3,r4,4)] & {occupant(r4) /= {}}) => {g3 : occupant(r4)}) &


			(([Entry(g4,r1,1)] & {occupant(r1) /= {}}) => {g4 : occupant(r1)}) &
			(([Entry(g4,r1,2)] & {occupant(r1) /= {}}) => {g4 : occupant(r1)}) &
			(([Entry(g4,r1,3)] & {occupant(r1) /= {}}) => {g4 : occupant(r1)}) &
			(([Entry(g4,r1,4)] & {occupant(r1) /= {}}) => {g4 : occupant(r1)}) &
			(([Entry(g4,r2,1)] & {occupant(r2) /= {}}) => {g4 : occupant(r2)}) &
			(([Entry(g4,r2,2)] & {occupant(r2) /= {}}) => {g4 : occupant(r2)}) &
			(([Entry(g4,r2,3)] & {occupant(r2) /= {}}) => {g4 : occupant(r2)}) &
			(([Entry(g4,r2,4)] & {occupant(r2) /= {}}) => {g4 : occupant(r2)}) &
			(([Entry(g4,r3,1)] & {occupant(r3) /= {}}) => {g4 : occupant(r3)}) &
			(([Entry(g4,r3,2)] & {occupant(r3) /= {}}) => {g4 : occupant(r3)}) &
			(([Entry(g4,r3,3)] & {occupant(r3) /= {}}) => {g4 : occupant(r3)}) &
			(([Entry(g4,r3,4)] & {occupant(r3) /= {}}) => {g4 : occupant(r3)}) &
			(([Entry(g4,r4,1)] & {occupant(r4) /= {}}) => {g4 : occupant(r4)}) &
			(([Entry(g4,r4,2)] & {occupant(r4) /= {}}) => {g4 : occupant(r4)}) &
			(([Entry(g4,r4,3)] & {occupant(r4) /= {}}) => {g4 : occupant(r4)}) &
			(([Entry(g4,r4,4)] & {occupant(r4) /= {}}) => {g4 : occupant(r4)}) )";

  ASSERT_LTL_GOOD  == "G ( 
  		([CheckIn(g1,r1)] => X ([Entry(g1,r1,1)] or [Entry(g1,r1,2)] or [Entry(g1,r1,3)] or [Entry(g1,r1,4)])) &
  		([CheckIn(g1,r2)] => X ([Entry(g1,r2,1)] or [Entry(g1,r2,2)] or [Entry(g1,r2,3)] or [Entry(g1,r2,4)])) &
  		([CheckIn(g1,r3)] => X ([Entry(g1,r3,1)] or [Entry(g1,r3,2)] or [Entry(g1,r3,3)] or [Entry(g1,r3,4)])) &
  		([CheckIn(g1,r4)] => X ([Entry(g1,r4,1)] or [Entry(g1,r4,2)] or [Entry(g1,r4,3)] or [Entry(g1,r4,4)])) &

		([CheckIn(g2,r1)] => X ([Entry(g2,r1,1)] or [Entry(g2,r1,2)] or [Entry(g2,r1,3)] or [Entry(g2,r1,4)])) &
  		([CheckIn(g2,r2)] => X ([Entry(g2,r2,1)] or [Entry(g2,r2,2)] or [Entry(g2,r2,3)] or [Entry(g2,r2,4)])) &
  		([CheckIn(g2,r3)] => X ([Entry(g2,r3,1)] or [Entry(g2,r3,2)] or [Entry(g2,r3,3)] or [Entry(g2,r3,4)])) &
  		([CheckIn(g2,r4)] => X ([Entry(g2,r4,1)] or [Entry(g2,r4,2)] or [Entry(g2,r4,3)] or [Entry(g2,r4,4)])) &

  		([CheckIn(g3,r1)] => X ([Entry(g3,r1,1)] or [Entry(g3,r1,2)] or [Entry(g3,r1,3)] or [Entry(g3,r1,4)])) &
  		([CheckIn(g3,r2)] => X ([Entry(g3,r2,1)] or [Entry(g3,r2,2)] or [Entry(g3,r2,3)] or [Entry(g3,r2,4)])) &
  		([CheckIn(g3,r3)] => X ([Entry(g3,r3,1)] or [Entry(g3,r3,2)] or [Entry(g3,r3,3)] or [Entry(g3,r3,4)])) &
  		([CheckIn(g3,r4)] => X ([Entry(g3,r4,1)] or [Entry(g3,r4,2)] or [Entry(g3,r4,3)] or [Entry(g3,r4,4)])) &

  		([CheckIn(g4,r1)] => X ([Entry(g4,r1,1)] or [Entry(g4,r1,2)] or [Entry(g4,r1,3)] or [Entry(g4,r1,4)])) &
  		([CheckIn(g4,r2)] => X ([Entry(g4,r2,1)] or [Entry(g4,r2,2)] or [Entry(g4,r2,3)] or [Entry(g4,r2,4)])) &
  		([CheckIn(g4,r3)] => X ([Entry(g4,r3,1)] or [Entry(g4,r3,2)] or [Entry(g4,r3,3)] or [Entry(g4,r3,4)])) &
  		([CheckIn(g4,r4)] => X ([Entry(g4,r4,1)] or [Entry(g4,r4,2)] or [Entry(g4,r4,3)] or [Entry(g4,r4,4)])) 		

  		) => G (
			(([Entry(g1,r1,1)] & {occupant(r1) /= {}}) => {g1 : occupant(r1)}) &
			(([Entry(g1,r1,2)] & {occupant(r1) /= {}}) => {g1 : occupant(r1)}) &
			(([Entry(g1,r1,3)] & {occupant(r1) /= {}}) => {g1 : occupant(r1)}) &
			(([Entry(g1,r1,4)] & {occupant(r1) /= {}}) => {g1 : occupant(r1)}) &
			(([Entry(g1,r2,1)] & {occupant(r2) /= {}}) => {g1 : occupant(r2)}) &
			(([Entry(g1,r2,2)] & {occupant(r2) /= {}}) => {g1 : occupant(r2)}) &
			(([Entry(g1,r2,3)] & {occupant(r2) /= {}}) => {g1 : occupant(r2)}) &
			(([Entry(g1,r2,4)] & {occupant(r2) /= {}}) => {g1 : occupant(r2)}) &
			(([Entry(g1,r3,1)] & {occupant(r3) /= {}}) => {g1 : occupant(r3)}) &
			(([Entry(g1,r3,2)] & {occupant(r3) /= {}}) => {g1 : occupant(r3)}) &
			(([Entry(g1,r3,3)] & {occupant(r3) /= {}}) => {g1 : occupant(r3)}) &
			(([Entry(g1,r3,4)] & {occupant(r3) /= {}}) => {g1 : occupant(r3)}) &
			(([Entry(g1,r4,1)] & {occupant(r4) /= {}}) => {g1 : occupant(r4)}) &
			(([Entry(g1,r4,2)] & {occupant(r4) /= {}}) => {g1 : occupant(r4)}) &
			(([Entry(g1,r4,3)] & {occupant(r4) /= {}}) => {g1 : occupant(r4)}) &
			(([Entry(g1,r4,4)] & {occupant(r4) /= {}}) => {g1 : occupant(r4)}) &
		
			(([Entry(g2,r1,1)] & {occupant(r1) /= {}}) => {g2 : occupant(r1)}) &
			(([Entry(g2,r1,2)] & {occupant(r1) /= {}}) => {g2 : occupant(r1)}) &
			(([Entry(g2,r1,3)] & {occupant(r1) /= {}}) => {g2 : occupant(r1)}) &
			(([Entry(g2,r1,4)] & {occupant(r1) /= {}}) => {g2 : occupant(r1)}) &
			(([Entry(g2,r2,1)] & {occupant(r2) /= {}}) => {g2 : occupant(r2)}) &
			(([Entry(g2,r2,2)] & {occupant(r2) /= {}}) => {g2 : occupant(r2)}) &
			(([Entry(g2,r2,3)] & {occupant(r2) /= {}}) => {g2 : occupant(r2)}) &
			(([Entry(g2,r2,4)] & {occupant(r2) /= {}}) => {g2 : occupant(r2)}) &
			(([Entry(g2,r3,1)] & {occupant(r3) /= {}}) => {g2 : occupant(r3)}) &
			(([Entry(g2,r3,2)] & {occupant(r3) /= {}}) => {g2 : occupant(r3)}) &
			(([Entry(g2,r3,3)] & {occupant(r3) /= {}}) => {g2 : occupant(r3)}) &
			(([Entry(g2,r3,4)] & {occupant(r3) /= {}}) => {g2 : occupant(r3)}) &
			(([Entry(g2,r4,1)] & {occupant(r4) /= {}}) => {g2 : occupant(r4)}) &
			(([Entry(g2,r4,2)] & {occupant(r4) /= {}}) => {g2 : occupant(r4)}) &
			(([Entry(g2,r4,3)] & {occupant(r4) /= {}}) => {g2 : occupant(r4)}) &
			(([Entry(g2,r4,4)] & {occupant(r4) /= {}}) => {g2 : occupant(r4)}) &

			(([Entry(g3,r1,1)] & {occupant(r1) /= {}}) => {g3 : occupant(r1)}) &
			(([Entry(g3,r1,2)] & {occupant(r1) /= {}}) => {g3 : occupant(r1)}) &
			(([Entry(g3,r1,3)] & {occupant(r1) /= {}}) => {g3 : occupant(r1)}) &
			(([Entry(g3,r1,4)] & {occupant(r1) /= {}}) => {g3 : occupant(r1)}) &
			(([Entry(g3,r2,1)] & {occupant(r2) /= {}}) => {g3 : occupant(r2)}) &
			(([Entry(g3,r2,2)] & {occupant(r2) /= {}}) => {g3 : occupant(r2)}) &
			(([Entry(g3,r2,3)] & {occupant(r2) /= {}}) => {g3 : occupant(r2)}) &
			(([Entry(g3,r2,4)] & {occupant(r2) /= {}}) => {g3 : occupant(r2)}) &
			(([Entry(g3,r3,1)] & {occupant(r3) /= {}}) => {g3 : occupant(r3)}) &
			(([Entry(g3,r3,2)] & {occupant(r3) /= {}}) => {g3 : occupant(r3)}) &
			(([Entry(g3,r3,3)] & {occupant(r3) /= {}}) => {g3 : occupant(r3)}) &
			(([Entry(g3,r3,4)] & {occupant(r3) /= {}}) => {g3 : occupant(r3)}) &
			(([Entry(g3,r4,1)] & {occupant(r4) /= {}}) => {g3 : occupant(r4)}) &
			(([Entry(g3,r4,2)] & {occupant(r4) /= {}}) => {g3 : occupant(r4)}) &
			(([Entry(g3,r4,3)] & {occupant(r4) /= {}}) => {g3 : occupant(r4)}) &
			(([Entry(g3,r4,4)] & {occupant(r4) /= {}}) => {g3 : occupant(r4)}) &


			(([Entry(g4,r1,1)] & {occupant(r1) /= {}}) => {g4 : occupant(r1)}) &
			(([Entry(g4,r1,2)] & {occupant(r1) /= {}}) => {g4 : occupant(r1)}) &
			(([Entry(g4,r1,3)] & {occupant(r1) /= {}}) => {g4 : occupant(r1)}) &
			(([Entry(g4,r1,4)] & {occupant(r1) /= {}}) => {g4 : occupant(r1)}) &
			(([Entry(g4,r2,1)] & {occupant(r2) /= {}}) => {g4 : occupant(r2)}) &
			(([Entry(g4,r2,2)] & {occupant(r2) /= {}}) => {g4 : occupant(r2)}) &
			(([Entry(g4,r2,3)] & {occupant(r2) /= {}}) => {g4 : occupant(r2)}) &
			(([Entry(g4,r2,4)] & {occupant(r2) /= {}}) => {g4 : occupant(r2)}) &
			(([Entry(g4,r3,1)] & {occupant(r3) /= {}}) => {g4 : occupant(r3)}) &
			(([Entry(g4,r3,2)] & {occupant(r3) /= {}}) => {g4 : occupant(r3)}) &
			(([Entry(g4,r3,3)] & {occupant(r3) /= {}}) => {g4 : occupant(r3)}) &
			(([Entry(g4,r3,4)] & {occupant(r3) /= {}}) => {g4 : occupant(r3)}) &
			(([Entry(g4,r4,1)] & {occupant(r4) /= {}}) => {g4 : occupant(r4)}) &
			(([Entry(g4,r4,2)] & {occupant(r4) /= {}}) => {g4 : occupant(r4)}) &
			(([Entry(g4,r4,3)] & {occupant(r4) /= {}}) => {g4 : occupant(r4)}) &
			(([Entry(g4,r4,4)] & {occupant(r4) /= {}}) => {g4 : occupant(r4)}) )";

  KEY == {1,2,3,4};
  keys == {r1 |-> 1, r1 |-> 2, r1 |-> 3, r1 |-> 4};
  GUEST == {g1};
  ROOM == {r1};


PROPERTIES
  GUEST : POW1(GUEST_) & ROOM : POW1(ROOM_) &
  keys : ROOM <-> KEY 

VARIABLES
  occupant, current, prev, g_keys

INVARIANT
  g_keys : GUEST --> POW(KEY) &
  current : ROOM >-> KEY &
  !r.(r:ROOM => current(r) : keys[{r}]) &
  prev : ROOM >-> KEY &
  !r.(r:ROOM => prev(r) : keys[{r}]) &
  occupant : ROOM_ --> POW(GUEST) 


INITIALISATION 
    current := %s.(s:ROOM | min(keys[{s}])) ;
    prev := current ||
    g_keys := %s.(s:GUEST | {}) || 
    occupant :=  %s.(s:ROOM_ | {}) 



  
OPERATIONS
  CheckIn(g,r) =
    PRE g:GUEST & r:ROOM & 
	occupant(r) = {} &
	{k | k:keys[{r}] & k > prev(r)} /= {} THEN
    LET k BE k = min(keys[{r}]-(0..prev(r))) IN
      g_keys(g) := g_keys(g) \/ {k} ||
      prev(r) := k ||
      occupant(r) := occupant(r) \/ {g}
    END END;

  CheckOut(g) =
    PRE g:GUEST & #r.(r:ROOM & g : occupant(r)) THEN
    occupant := %s.(s:dom(occupant) | occupant(s) - {g})
    END;

  Entry(g,r,k) =
    PRE g:GUEST & r:ROOM & 
	k:g_keys(g) & 
	(k = current(r) or k : (keys[{r}]-(0..current(r)))) &
	g : occupant(r)    THEN
    current(r) := k
    END


END






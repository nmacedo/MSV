MACHINE hotel
/** author: Nuno Macedo, 2016 */

SETS
  GUEST_ = {g1,g2,g3};
  ROOM_ = {r1,r2,r3}

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
			(([Entry(g3,r3,4)] & {occupant(r3) /= {}}) => {g3 : occupant(r3)}) )";

  ASSERT_LTL_GOOD  == "G ( 
  		([CheckIn(g1,r1)] => X ([Entry(g1,r1,1)] or [Entry(g1,r1,2)] or [Entry(g1,r1,3)] or [Entry(g1,r1,4)])) &
  		([CheckIn(g1,r2)] => X ([Entry(g1,r2,1)] or [Entry(g1,r2,2)] or [Entry(g1,r2,3)] or [Entry(g1,r2,4)])) &
  		([CheckIn(g1,r3)] => X ([Entry(g1,r3,1)] or [Entry(g1,r3,2)] or [Entry(g1,r3,3)] or [Entry(g1,r3,4)])) &

		([CheckIn(g2,r1)] => X ([Entry(g2,r1,1)] or [Entry(g2,r1,2)] or [Entry(g2,r1,3)] or [Entry(g2,r1,4)])) &
  		([CheckIn(g2,r2)] => X ([Entry(g2,r2,1)] or [Entry(g2,r2,2)] or [Entry(g2,r2,3)] or [Entry(g2,r2,4)])) &
  		([CheckIn(g2,r3)] => X ([Entry(g2,r3,1)] or [Entry(g2,r3,2)] or [Entry(g2,r3,3)] or [Entry(g2,r3,4)])) &

  		([CheckIn(g3,r1)] => X ([Entry(g3,r1,1)] or [Entry(g3,r1,2)] or [Entry(g3,r1,3)] or [Entry(g3,r1,4)])) &
  		([CheckIn(g3,r2)] => X ([Entry(g3,r2,1)] or [Entry(g3,r2,2)] or [Entry(g3,r2,3)] or [Entry(g3,r2,4)])) &
  		([CheckIn(g3,r3)] => X ([Entry(g3,r3,1)] or [Entry(g3,r3,2)] or [Entry(g3,r3,3)] or [Entry(g3,r3,4)])) 

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
			(([Entry(g3,r3,4)] & {occupant(r3) /= {}}) => {g3 : occupant(r3)}) )";


  KEY == {1,2,3,4};


VARIABLES
  occupant, current, prev, g_keys, keys, ROOM, GUEST

INVARIANT
  GUEST : POW1(GUEST_) & ROOM : POW1(ROOM_) &
  keys : ROOM <-> KEY &
  !r.(r:ROOM => keys[{r}] /= {}) &
  !r1,r2.(r1:ROOM & r2:ROOM & keys[{r1}] /\ keys[{r2}] /= {} => r1 = r2) &
  g_keys : GUEST --> POW(KEY) &
  current : ROOM >-> KEY &
  !r.(r:ROOM => current(r) : keys[{r}]) &
  prev : ROOM >-> KEY &
  !r.(r:ROOM => prev(r) : keys[{r}]) &
  occupant : ROOM_ --> POW(GUEST) 

INITIALISATION 
	ANY gs,rs,ks WHERE
	gs : POW1(GUEST_) & rs : POW1(ROOM_) &
  	ks : rs <-> KEY &
  	!r.(r:rs => ks[{r}] /= {}) &  	
  	!r1,r2.(r1:rs & r2:rs & ks[{r1}] /\ ks[{r2}] /= {} => r1 = r2)
  	THEN
  	GUEST := gs || ROOM := rs || keys := ks;
	current := %s.(s:ROOM | min(keys[{s}])) ;
    prev := current ||
    g_keys := %s.(s:GUEST | {}) || 
    occupant :=  %s.(s:ROOM_ | {}) 
    END

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
	(k = current(r) or k : (keys[{r}]-(0..current(r)))) THEN
    current(r) := k
    END


END



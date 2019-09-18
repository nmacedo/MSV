module hotel

open util/ordering[Time] as to
open util/ordering[Key] as ko

sig Time {}

sig Key {}

-- a room has a pool of keys assigned and records the last valid key at each instant
sig Room {
	keys: set Key,
	currentKey: keys one -> Time
}

-- each key belongs to at most one room
fact DisjointKeySets {
	keys in Room lone -> Key
}

-- a guest possesses a set of keys at each instant
sig Guest {
	keys: Key -> Time
}

-- the front desk registers the last issued key for a room and its occupants, in each instant
one sig FrontDesk {
	lastKey: (Room -> lone Key) -> Time,
	occupant: (Room -> Guest) -> Time
}

-- the next key is the minimal key according to the total order
fun nextKey [k: Key, ks: set Key]: set Key {
	min [k.nexts & ks]
}

-- in the initial state guests have no keys, rooms are empty and the room key is 
-- synchronized with the front desk
pred Init [t: Time] {
	no Guest.keys.t
	no FrontDesk.occupant.t
	all r: Room | FrontDesk.lastKey.t[r] = r.currentKey.t 
}

pred Entry [t, t': Time, g: Guest, r: Room, k: Key] {
	k in g.keys.t
	k = r.currentKey.t or k = nextKey[r.currentKey.t, r.keys]
	r.currentKey.t' = k
	all r: Room - r | r.currentKey.t = r.currentKey.t'
	all g: Guest | g.keys.t = g.keys.t'
	FrontDesk.lastKey.t = FrontDesk.lastKey.t'
	FrontDesk.occupant.t = FrontDesk.occupant.t' 
}

pred Checkout [t, t': Time, g: Guest] {
	some FrontDesk.occupant.t.g
	FrontDesk.occupant.t' = FrontDesk.occupant.t - Room -> g
	FrontDesk.lastKey.t = FrontDesk.lastKey.t'
	all r: Room | r.currentKey.t = r.currentKey.t'
	all g: Guest | g.keys.t = g.keys.t' 
}

pred Checkin [t, t': Time, g: Guest, r: Room, k: Key] {
	g.keys.t' = g.keys.t + k
	no FrontDesk.occupant.t[r]
	FrontDesk.occupant.t' = FrontDesk.occupant.t + r -> g
	FrontDesk.lastKey.t' = FrontDesk.lastKey.t ++ r -> k
	k = nextKey[FrontDesk.lastKey.t[r], r.keys]
	all r: Room | r.currentKey.t = r.currentKey.t'
	all g: Guest - g | g.keys.t = g.keys.t' 
}

pred NoIntervening {
	all t: Time, t': t.next, t'': t'.next, g: Guest, r: Room, k: Key |
		Checkin[t, t', g, r, k] implies (Entry[t', t'', g, r, k] or no t'') 
}

fact Traces {
	Init[first]
	all t: Time, t' : t.next | some g: Guest, r: Room, k: Key |
		Entry[t, t', g, r, k] or Checkin[t, t', g, r, k] or Checkout[t, t', g] 
}

pred NoBadEntry {
	all t: Time, t': t.next, r: Room, g: Guest, k: Key |
		(Entry[t, t', g, r, k] and some FrontDesk.occupant.t[r]) implies g in FrontDesk.occupant.t[r] 
}

assert BadSafety {
	NoBadEntry
}

assert GoodSafety {
	NoIntervening => NoBadEntry
}

// Hotel (1) scenario
check BadSafety for 4 but 10 Time, exactly 4 Guest, exactly 4 Room
// Hotel (2) scenario
check GoodSafety for 4 but 10 Time, exactly 4 Guest, exactly 4 Room


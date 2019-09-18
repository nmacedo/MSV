module hotel

open util/ordering[Key] as ko

sig Key {}

-- a room has a pool of keys assigned and records the last valid key at each instant
sig Room {
	keys: set Key,
	currentKey: one keys
}

-- each key belongs to at most one room
fact DisjointKeySets {
	keys in Room lone -> Key
}

-- a guest possesses a set of keys at each instant
sig Guest {
	keys: set Key
}

-- the front desk registers the last issued key for a room and its occupants, in each instant
one sig FrontDesk {
	lastKey: Room -> lone Key,
	occupant: Room -> Guest
}

-- in the initial state guests have no keys, rooms are empty and the room key is 
-- synchronized with the front desk
pred Init {
	no Guest.keys
	no FrontDesk.occupant
	all r: Room | FrontDesk.lastKey[r] = r.currentKey.
}

fact Traces {
	Init
}

run { } for 3 but exactly 3 Room, exactly 3 Guest, exactly 6 Key

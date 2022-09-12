/**
An very simplified version of the Hybrid ERTMS/ETCS Level 3 Concept (HL3).

@author: Rui Couto, Nuno Macedo
**/
open util/ordering[State]
open util/ordering[VSS]

sig TTD {}
sig VSS {
	ttd : one TTD
}
sig State {}
sig Train {
	vss : VSS one -> State
}

fact {
	all t:TTD, v1,v2:ttd.t | v1.nexts & v2.prevs in ttd.t 
}

run { some Train } for 5 but 2 Train

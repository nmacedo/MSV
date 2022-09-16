/*
 * HSM2NHSM transformation (with transitive closure)
 *
 * Model for the synchronization of hierarchical and non-hierarchical state machines, as
 * defined in the hsm2nhsm_closure.qvtr QVT-R bidirectional transformation.
 *
 * This version relies on a transformation defined with transitive closure over the state
 * hierarchy; an alternative version uses recursion.
 *
 * Used as running example in
 * [1] N. Macedo and A. Cunha. Least-change bidirectional model transformation with QVT-R and ATL. SoSyM 2016
 * 
 * author: N. Macedo, 10/2012
 */
module HSM2NHSM_recursive

open HSM [Source]
open NHSM [Target]
open util/integer

abstract sig Model {}

abstract sig Source extends Model {
   M2M_HM : Target -> HSM/SMachine -> NHSM/SMachine,
   M2M_NM : Target -> HSM/SMachine -> NHSM/SMachine,
   S2S_HM : Target -> HSM/State -> NHSM/State,
   S2S_NM : Target -> HSM/State -> NHSM/State,
}
abstract sig Target extends Model {}

pred Top_M2M_HM [hm:Source,nm:Target] {
	all sm:SMachine_.hm | some tm:SMachine_.nm | sm.name.hm = tm.name.nm
}

pred Top_M2M_NM [hm:Source,nm:Target] {
	all tm:SMachine_.nm | some sm:SMachine_.hm | sm.name.hm = tm.name.nm
}

pred Top_S2S_HM [hm:Source,nm:Target] {
	all sm:SMachine_.hm, tm:SMachine_.nm | sm->tm in M2M_HM[hm,nm] =>
		all s : sm.states.hm | no s.container.hm => some t : tm.states.nm | s.name.hm = t.name.nm
}

pred Top_S2S_NM [hm:Source,nm:Target] {
	all sm:SMachine_.hm, tm:SMachine_.nm | sm->tm in M2M_NM[hm,nm] =>
		all t : tm.states.nm | some s : sm.states.hm | 
			 no s.container.hm && s.name.hm = t.name.nm
}

pred Top_T2T_HM [hm:Source,nm:Target] {
	all s:Transition_.hm | some t:Transition_.nm | 
		some s1,t1 : State_.hm | 
			no s1.container.hm && s1 in (s.source.hm).*(container.hm) &&
			s1 -> t.source.nm in S2S_HM[hm,nm] && 
			no t1.container.hm && t1 in (s.target.hm).*(container.hm) &&
			t1 -> t.target.nm in S2S_HM[hm,nm]
}

pred Top_T2T_NM [hm:Source,nm:Target] {
	all t:Transition_.nm | some s:Transition_.hm | 
		some s1,t1 : State_.hm | 
			no s1.container.hm && s1 in (s.source.hm).*(container.hm) &&
			s1 -> t.source.nm in S2S_NM[hm,nm] && 
			no t1.container.hm && t1 in (s.target.hm).*(container.hm) &&
			t1 -> t.target.nm in S2S_NM[hm,nm]
}

pred Sub_M2M_HM [hm:Source,nm:Target] {
	M2M_HM = hm -> nm -> { sm : SMachine_.hm, tm: SMachine_.nm | sm.name.hm = tm.name.nm }
}

pred Sub_M2M_NM [hm:Source,nm:Target] {
	M2M_NM = hm -> nm -> { sm : SMachine_.hm, tm: SMachine_.nm | sm.name.hm = tm.name.nm }
}

pred Sub_S2S_HM [hm:Source,nm:Target] {
	S2S_HM = hm -> nm -> { s:State_.hm,t:State_.nm | 
		all sm : SMachine_.hm, tm : SMachine_.nm | 
			sm->tm in M2M_HM[hm,nm] => ((s in sm.states.hm && no s.container.hm) =>
				(t in tm.states.nm && s.name.hm = t.name.nm)) }
	}

pred Sub_S2S_NM [hm:Source,nm:Target] {
	S2S_NM = hm -> nm -> { s:State_.hm,t:State_.nm | 
		all sm : SMachine_.hm, tm : SMachine_.nm | 
			sm->tm in M2M_NM[hm,nm] => (t in tm.states.nm =>
				(s in sm.states.hm && no s.container.hm && s.name.hm = t.name.nm)) }
	}

pred HSM2NHSM [hm:Source,nm:Target] {
	Top_M2M_HM[hm,nm] && Top_M2M_NM[hm,nm]
	Top_S2S_HM[hm,nm] && Top_S2S_NM[hm,nm]
	Top_T2T_HM[hm,nm] && Top_T2T_NM[hm,nm]
	Sub_M2M_HM[hm,nm] && Sub_M2M_NM[hm,nm]
	Sub_S2S_HM[hm,nm] && Sub_S2S_NM[hm,nm]
}


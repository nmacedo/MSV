/*
 * A formalization of a an ORCID-based synchronization framework 
 * for PTCRIS, as described in https://github.com/fccn/PTCRISync/wiki.
 * 
 * author: A. Cunha, N. Macedo, 12/2015 
 */

open util/ordering[ORCID]
open util/ordering[PTCris]
open util/ordering[Work]

sig Key, Putcode, UID, Metadata {}
sig Invalid in Metadata {}

enum Source {PTCRIS,User,Scopus}

// abstracted to ease the definition of comparison predicates
abstract sig Output {
	uids : UID -> Repository
} 

// abstracted to ease the definition of comparison predicates
abstract sig Repository {
	outputs : set Output
}

/*====================ORCID=====================*/
sig Work extends Output {
	putcode : one Putcode,
	source : one Source,
	metadata : one Metadata
} 

sig Group extends Output {
	works: set Work
} { 
	// the UIDs of a group are those of its works
	all r : ORCID | uids.r = works.@uids.r
}

// Defines similar Works that are considered grouped.
fun similar[r: ORCID] : Work -> Work {
	*{w1,w2 : r.groups.works | some w1.uids.r & w2.uids.r} 
}

// Groups are built by similarity.
fact grouping {
	all o : ORCID, w: o.groups.works | 
		one o.groups&works.w && w.(similar[o]) = (o.groups&works.w).works
}

sig ORCID extends Repository {
	groups : set Group
} {
	// the outputs of an ORCID repository are its groups
	outputs = groups
}

// The putcode uniquely identifies a Work.
fact ORCID1 {
	all o : ORCID | no disj w1,w2 : o.groups.works |
		w1.putcode = w2.putcode
}

// There cannot be two works with the same source with shared uids.
fact ORCID2 {
	all o : ORCID | all disj w1,w2 : o.groups.works |
		w1.source = w2.source implies no (w1.uids.o & w2.uids.o)
}

// Defines indentical Works.
pred identical[w,w':Work,o,o':ORCID] {
	w.metadata = w'.metadata && w.uids.o = w'.uids.o' && w.source = w'.source
}

// Preferred works are defined by an internal order over them.
fun preferred[g:Group] : Work {
	min[g.works]
}

// Calculates the preferred works of an ORCID repository.
fun _preferred[] : ORCID -> Work {
	{o:ORCID, w : o.groups.works | some g : o.groups | w = preferred[g] }
}

// Calculates all the works of an ORCID repository.
fun _works[] : ORCID -> Work {
	{o:ORCID, w : Work | w in o.groups.works }
}

/*====================PTCRIS=====================*/
sig Production extends Output {
	key : one Key,
	metadata : one Metadata
}

abstract sig Notification extends Output {
	key : one Key
}

sig Creation, Warning extends Notification {
	metadata : one Metadata
}
sig Modification extends Notification {}

sig PTCris extends Repository {
	productions : set Production,
 	exported : set productions,
	notifications : set Notification
} { 
	// the outputs of an ORCID repository are its groups
	outputs = productions
}

// The key attribute uniquely identifies a Production.
fact PTCRIS1 {
	all p : PTCris | no disj p1,p2 : p.productions |
		p1.key = p2.key
}

// If a Production is selected to be exported then it must have some uids.
fact PTCRIS2 {
	all p : PTCris | all e : p.exported |
		some e.uids.p
}

// If two productions share uids at most one of them can be selected to be exported.
fact PTCRIS3 {
	all p : PTCris | all disj p1,p2 : p.productions |
		some p1.uids.p & p2.uids.p => p1 not in p.exported or p2 not in p.exported
}

// The key attribute uniquely identifies a Creation.
fact PTCRIS4 {
	all p : PTCris | no disj n1,n2 : p.notifications&Creation |
		n1.key = n2.key
}

// The key of a Creation must not be the key of an existing Production.
fact PTCRIS5 {
	all p : PTCris | all n : p.notifications&Creation |
		n.key not in p.productions.key
}

// The key of a Modification must be the key of an existing Production.
fact PTCRIS6 {
	all p : PTCris | all n : p.notifications&Modification |
		n.key in p.productions.key
}

// In a Modification notification the set of uids must be non empty.
fact PTCRIS7 {
	all p : PTCris | all n : p.notifications&Modification |
		some n.uids.p
}

// Defines indentical Productions.
pred identical[p,p':Production,c,c':PTCris] {
	p.metadata = p'.metadata && p.uids.c = p'.uids.c'
}

// Defines indentical Modification notifications.
pred identical[p,p':Modification,c,c':PTCris] {
	p.uids.c = p'.uids.c'
}

// Defines indentical Creation notifications.
pred identical[p,p':Creation,c,c':PTCris] {
	p.metadata = p'.metadata && p.uids.c = p'.uids.c'
}

fun identical_creations[p : PTCris] : Creation -> Creation {
	{n1,n2 : p.notifications&Creation | identical[n1,n2,p,p] }
}

// Relates Modification notifications with the corresponding Production.
fun modifies[p:PTCris,n:Modification] : Production {
	(p.productions)&Production<:key.(n.key)
}

// A modifies relation useful for visualizing.
fun _modifies[] : Repository -> Modification -> Production {
	{p:PTCris, n:p.notifications&Modification,p:modifies[p,n]}
}

// A unifying UIDs relationship, useful for visualizing.
fun _uids[] : Repository -> Output -> UID {
	{r:Repository,n:r.notifications&Creation, u:n.uids.r | no none } + 
	{r:Repository,n:r.groups.works, u:n.uids.r | no none } + 
	{r:Repository,n:r.productions, u:n.uids.r | no none } + 
	{r:Repository,n:r.groups, u:n.uids.r | no none } + 
	{r:Repository,n:r.notifications&Modification, u:n.uids.r | u not in (Production<:key.(n.key)).uids.r }
}

/*====================ORCID-PTCRIS Consistency=====================*/
// Every UID at ORCID is known to the PTCRIS (either as a production or in a notification).
/*pred IMPORTED_general [p:PTCris, o:ORCID] {
  	o.groups.works.uids.o in p.productions.uids.p+p.notifications.uids.p
}*/

pred IMPORTED [p:PTCris, o:ORCID] {
 	// IMPORTED1: For every Work ORCID there exists an artifact in PTCRIS (either a Production or a 
	// Notification) that contains all uids of its similar works.
   all g : o.groups | 
		some p1 : p.productions+p.notifications | g.uids.o in p1.uids.p
  	// IMPORTED2: Every Notification contains exactly  the uids of a group of similar works.
  	all n : p.notifications | 
		some g : o.groups | g.uids.o = n.uids.p
  	// IMPORTED3:  The metadata of every Creation notification is computed using extract over the 
	// group of similar works from which its uids were aggregated.
	all n : (p.notifications&Creation) | 
		some g : o.groups | g.uids.o = n.uids.p && n.metadata = preferred[g].metadata
  	// IMPORTED4: A Creation notification must have a non-empty set of uids that are not shared
	// with any productions nor other notifications.
	all n : (p.notifications&Creation) | 
		some n.uids.p && (no p1: p.productions+p.notifications-n | some n.uids.p & p1.uids.p) 
  	// IMPORTED5: A Modification notification must share uids with the associated Production.
   all n : p.notifications&Modification | 
		some n.uids.p & modifies[p,n].uids.p && n.uids.p not in modifies[p,n].uids.p
	// IMPORTED6: If there is a UID affected by a modification, then every production with that UID is
	//  affected by exactly one modification.
  	all g : o.groups, p1 : p.productions | some g.uids.o & p1.uids.p && g.uids.o not in p1.uids.p => 
		one n : p.notifications&Modification | n.key = p1.key && n.uids.p = g.uids.o
}

/*assert IMPORTED_refines {
	all p: PTCris, o: ORCID |
		IMPORTED[p,o] => IMPORTED_general[p,o]
}

check IMPORTED_refines for 7 but 1 ORCID, 1 PTCris

pred EXPORTED_general [p:PTCris, o:ORCID] {
	all e : p.exported | some w : o.groups.works | e.uids.p = w.uids.o && e.metadata = w.metadata && w.source = PTCRIS
}*/

pred EXPORTED [p:PTCris, o:ORCID] {
	//EXPORTED1: For every exported Production, a Work must exist in ORCID with the same uids, 
	// the same metadata, and whose source is the PTCRIS service.
	all e : p.exported | one w : o.groups.works | e.uids.p = w.uids.o && e.metadata = w.metadata && w.source = PTCRIS
	// EXPORTED2 For every Work whose source is the PTCRIS service, a Production must exist in 
	// PTCRIS with the same uids, the same metadata, and that is selected as exported.	
	all w : o.groups.works | w.source = PTCRIS => some e : p.exported | e.uids.p = w.uids.o && e.metadata = w.metadata
}

/*assert EXPORTED_refines {
	all p: PTCris, o: ORCID |
		EXPORTED[p,o] => EXPORTED_general[p,o]
}

check EXPORTED_refines for 7 but 1 ORCID, 1 PTCris*/

// SYNCED repositories are both EXPORTED- and IMPORTED-consistency.
pred SYNCED [p:PTCris, o:ORCID] { 
	EXPORTED[p,o] && IMPORTED[p,o]
}

/*====================ORCID-PTCRIS Sync=====================*/
// PTCRIS synchronizer may not modify productions nor the exported set.
// Thus, may change notifications.
pred frame[p,p':PTCris] {
	p'.exported = p.exported
	p'.productions= p.productions
	all p1 : p.productions | p1.uids.p' = p1.uids.p
}

// ORCID synchronizer may not modify works from other sources.
// Thus, works from PTCRIS source.
pred frame[o,o':ORCID] {
	o'.groups.works - source.PTCRIS = o.groups.works - source.PTCRIS
	all x : o'.groups.works - source.PTCRIS | x.uids.o = x.uids.o'
	all w : o.groups.works&source.PTCRIS, w' : o'.groups.works&source.PTCRIS |
		w.putcode = w'.putcode => w = w'
	all w : o.groups.works&source.PTCRIS, w' : o'.groups.works&source.PTCRIS |
		some w.uids.o & w'.uids.o' <=> w = w' // force updates!
	all w : _preferred[o'] | w = min[o'.similar[w]&o.groups.works] or no o'.similar[w]&o.groups.works
}

// IMPORT restores IMPORTED-consistency by updating the PTCRIS within the frames.
pred IMPORT [o:ORCID,p,p':PTCris] {
	frame[p,p']
	IMPORTED[p',o]
}

// EXPORT restores EXPORTED-consistency by updating the ORCID within the frames.
pred EXPORT [o,o':ORCID,p:PTCris] {
	frame[o,o']	   
	EXPORTED[p,o']
	// EXPORTED3: If a preferred ORCID Work existed in the pre-state, it was already preferred.
	all e : p.exported | (one w : o.groups.works | e.uids.p = w.uids.o && e.metadata = w.metadata && w.source = PTCRIS) =>
		one w : o.groups.works&o'.groups.works | e.uids.p = w.uids.o' && e.metadata = w.metadata && w.source = PTCRIS
}

// SYNC restores IMPORTED- and EXPORTED-consistency by applying EXPORT followed by IMPORT.
pred SYNC[p,p':PTCris,o,o':ORCID] {
	EXPORT[o,o',p] && IMPORT[o',p,p'] 
}

/*====================Properties=====================*/
// ORCID states are similar modulo preferred works and putcodes
// (in practice, due to the frames, only the PTCRIS works should have putcodes changed)
pred same_orcid[o,o':ORCID] {
	all w1 : o.groups.works | some w2 : o'.groups.works | identical[w1,w2,o,o'] && w1.putcode = w2.putcode
	all w2 : o'.groups.works | some w1 : o.groups.works | identical[w1,w2,o,o'] && w1.putcode = w2.putcode
	
	// Preferred must be preserved (only for hippo, for determinism may change due to deletions)
	all w1 : _preferred[o] | some w2: _preferred[o'] | identical[w1,w2,o,o'] && w1.putcode = w2.putcode
	all w1 : _preferred[o'] | some w2: _preferred[o] | identical[w1,w2,o',o] && w1.putcode = w2.putcode
} 

pred same_orcid_mod[o,o':ORCID] {
	all w1 : o.groups.works | some w2 : o'.groups.works | identical[w1,w2,o,o'] 
	all w2 : o'.groups.works | some w1 : o.groups.works | identical[w1,w2,o,o'] 
	
	// Preferred must be preserved (only for hippo, for determinism may change due to deletions)
	all w1 : _preferred[o] | some w2: _preferred[o'] | identical[w1,w2,o,o'] 
	all w1 : _preferred[o'] | some w2: _preferred[o] | identical[w1,w2,o',o] 
} 

// PTCRIS states are similar modulo creation keys
pred same_ptcris[p,p':PTCris] {
	all p1 : p.productions | some p2 : p'.productions | p1.key = p2.key and identical[p1,p2,p,p']
	all p2 : p'.productions | some p1 : p.productions | p1.key = p2.key and identical[p1,p2,p,p']

	p.exported.key = p'.exported.key

	all n1 : p.notifications&Modification | some n2 : p'.notifications&Modification | n1.key = n2.key and identical[n1,n2,p,p']
	all n2 : p'.notifications&Modification | some n1 : p.notifications&Modification | n1.key = n2.key and identical[n1,n2,p,p']

	all n1 : p.notifications&Creation | some n2 : p'.notifications&Creation | identical[n1,n2,p,p'] && #n1.(identical_creations[p])=#n2.(identical_creations[p'])
	all n1 : p'.notifications&Creation | some n2 : p.notifications&Creation | identical[n1,n2,p',p] && #n1.(identical_creations[p'])=#n2.(identical_creations[p])
} 

pred same_ptcris_mod[p,p':PTCris] {
	all p1 : p.productions | some p2 : p'.productions | p1.key = p2.key and identical[p1,p2,p,p']
	all p2 : p'.productions | some p1 : p.productions | p1.key = p2.key and identical[p1,p2,p,p']

	p.exported.key = p'.exported.key

	all n1 : p.notifications&Modification | some n2 : p'.notifications&Modification | n1.key = n2.key and identical[n1,n2,p,p']
	all n2 : p'.notifications&Modification | some n1 : p.notifications&Modification | n1.key = n2.key and identical[n1,n2,p,p']

	all n1 : p.notifications&Creation | some n2 : p'.notifications&Creation | identical[n1,n2,p,p'] && #n1.(identical_creations[p])=#n2.(identical_creations[p'])
	all n1 : p'.notifications&Creation | some n2 : p.notifications&Creation | identical[n1,n2,p',p] && #n1.(identical_creations[p])=#n2.(identical_creations[p'])
} 
/*
// IMPORT procedure is hippocratic for EXPORTED- and IMPORTED-consistent states.
check hippocratic_import {
	all o:ORCID,p:PTCris,p':p.next | SYNCED[p,o] && IMPORT[o,p,p'] implies 
		same_ptcris[p,p']
} for 8 but 1 ORCID, 2 PTCris, 5 Work, 5 Production, 4 Notification, 3 Group

// EXPORT procedure is hippocratic for EXPORTED- and IMPORTED-consistent states.
check hippocratic_export {
	all o:ORCID,o':o.next,p:PTCris | SYNCED[p,o] && EXPORT[o,o',p] implies 
		same_orcid[o,o']
} for 7 but 2 ORCID, 1 PTCris, 6 Work, 5 Production, 3 Notification, 3 Group
// 7 but 2 ORCID, 1 PTCris, 6 Work, 5 Production, 3 Notification, 3 Group, 1945818ms

// SYNC procedure is hippocratic for EXPORTED- and IMPORTED-consistent states.
check hippocratic_sync {
	all o:ORCID,o':o.next,p:PTCris,p':p.next | SYNCED[p,o] && SYNC[p,p',o,o'] implies 
		(same_orcid[o,o'] && same_ptcris[p,p'])
} for 8 but 2 ORCID, 2 PTCris, 6 Work, 6 Production, 3 Notification, 3 Group

// IMPORT procedure is deterministic for EXPORTED-consistent and IMPORTED-inconsistent states.
check deterministic_import {
	all o:ORCID,p:PTCris,p':p.next,p'':p.next.next | not SYNCED[p,o] && IMPORT[o,p,p'] && IMPORT[o,p,p''] implies 
		same_ptcris[p',p'']
} for 7 but 1 ORCID, 3 PTCris, 5 Work, 4 Production, 3 Notification, 3 Group
// 7 but 1 ORCID, 3 PTCris, 5 Work, 4 Production, 3 Notification, 3 Group, 210071ms

// EXPORT procedure is deterministic for EXPORT-inconsistent and IMPORT-consistent states.
check deterministic_export {
	all o:ORCID,o':o.next,o'':o.next.next,p:PTCris| not SYNCED[p,o] && EXPORT[o,o',p] && EXPORT[o,o'',p] implies 
		same_orcid_mod[o',o'']
} for 7 but 3 ORCID, 1 PTCris, 5 Work, 4 Production, 3 Notification, 3 Group
// 7 but 3 ORCID, 1 PTCris, 5 Work, 4 Production, 3 Notification, 3 Group, 1868728ms

// SYNC procedure is deterministic for EXPORT-inconsistent and IMPORT-consistent states.
check deterministic_export {
	all o:ORCID,o':o.next,o'':o.next.next,p:PTCris,p':p.next,p'':p'.next | not SYNCED[p,o] && SYNC[p,p',o,o'] && SYNC[p,p'',o,o''] implies 
		(same_orcid[o',o''] && same_ptcris[p',p''])
} for 8 but 3 ORCID, 3 PTCris, 6 Work, 6 Production, 4 Notification, 4 Group

// IMPORT can never fix EXPORTED-consistency.
check import_scope {
	all o:ORCID,p:PTCris,p':p.next | IMPORTED[p,o] && not EXPORTED[p,o] && IMPORT[o,p,p'] implies not SYNCED[p',o]
} for 4 but 1 ORCID, 2 PTCris, 8 Output

// EXPORT can never fix IMPORTED-consistency.
check export_scope {
	all o:ORCID,o':o.next,p:PTCris| not IMPORTED[p,o] && EXPORTED[p,o] && EXPORT[o,o',p] implies not SYNCED[p,o']
} for 4 but 2 ORCID, 1 PTCris, 8 Output

// IMPORT never breaks EXPORTED-consistency.
check import_correct {
	all o:ORCID,p:PTCris,p':p.next | not IMPORTED[p,o] && EXPORTED[p,o] && IMPORT[o,p,p'] implies SYNCED[p',o]
} for 4 but 1 ORCID, 2 PTCris, 8 Output

// EXPORT may break IMPORTED-consistency.
check export_incorrect {
	all o:ORCID,o':o.next,p:PTCris|  no p.notifications && IMPORTED[p,o] && not EXPORTED[p,o] && EXPORT[o,o',p] implies SYNCED[p,o']
} for 1 but 2 ORCID, 1 PTCris, 3 Output

// EXPORT followed by IMPORT always converges into IMPORTED- and EXPORTED-consistency.
check export_import_correct {
	all o:ORCID,o':o.next,p:PTCris,p':p.next | IMPORTED[p,o] && not EXPORTED[p,o] && EXPORT[o,o',p] && IMPORT[o',p,p'] implies SYNCED[p',o']
} for 4 but 2 ORCID, 2 PTCris, 8 Output

// SYNC always fixes IMPORTED- and EXPORTED-consistency.
check export_import_correct {
	all o:ORCID,o':o.next,p:PTCris,p':p.next | not SYNCED[p,o] && SYNC[p,p',o,o'] implies SYNCED[p',o']
} for 4 but 2 ORCID, 2 PTCRIS, 8 Output
*/
/*====================Scenarios=====================*/
one sig Putcode0, Putcode1, Putcode2, Putcode3,Putcode4 extends Putcode {}
one sig Metadata0, Metadata1,Metadata2,Metadata3 extends Metadata {}
one sig Key0, Key1,Key2 extends Key {}
one sig DOI1, DOI2, EID0, EID1, DOI0, Handle1, Handle0 extends UID {}
one sig Work0, Work1, Work2, Work3,Work4 extends Work{}
one sig Production0, Production1, Production2 extends Production{}
one sig Group0, Group1, Group2,Group3,Group4 extends Group {}

// S1: This scenario depicts the introduction of group of works in the ORCID profile 
// without any productions with shared UIDs in the PTCRIS profile
pred IMPORTED_S1_pre[p:PTCris,o:ORCID] {
	no p.productions
	no p.notifications
	no o.groups.works
}

pred IMPORTED_S1[p:PTCris,o:ORCID] {
	no p.productions
	no p.notifications
	o.groups.works = Work0+Work1
	Work0.uids.o = DOI0+EID0 && Work0.metadata = Metadata0 && Work0.putcode = Putcode0 && Work0.source = Scopus &&
	Work1.uids.o = DOI0+Handle1 && Work1.metadata = Metadata1 && Work1.putcode = Putcode1 && Work1.source = User &&
	Work0 in _preferred[o]
}

run IMPORTED_S1 {some o:ORCID,o':o.next,p:PTCris,p':p.next | 
  IMPORTED_S1_pre[p,o] && IMPORTED_S1[p,o'] &&  EXPORTED[p,o'] && not IMPORTED[p,o'] && IMPORT[o',p,p'] } for 16 but 2 ORCID, 2 PTCris, 3 Work

pred IMPORTED_S2_pre[p:PTCris,o:ORCID] {
	p.productions = Production0
	Production0.key = Key2 && Production0.metadata = Metadata0 && Production0.uids.p = DOI0+EID0+Handle1
	no p.notifications
	o.groups.works = Work0+Work1
	Work0.uids.o = DOI0+EID0 && Work0.metadata = Metadata0 && Work0.putcode = Putcode0 && Work0.source = Scopus &&
	Work1.uids.o = DOI0+Handle1 && Work1.metadata = Metadata1 && Work1.putcode = Putcode1 && Work1.source = User &&
	Work0 in _preferred[o]
	o.groups = Group0
}

pred IMPORTED_S2[p:PTCris,o:ORCID] {
	p.productions = Production0
	Production0.key = Key2 && Production0.metadata = Metadata0 && Production0.uids.p = DOI0+EID0+Handle1
	no p.notifications
	o.groups.works = Work0+Work1+Work2
	Work0.uids.o = DOI0+EID0 && Work0.metadata = Metadata0 && Work0.putcode = Putcode0 && Work0.source = Scopus &&
	Work1.uids.o = DOI0+Handle1 && Work1.metadata = Metadata1 && Work1.putcode = Putcode1 && Work1.source = User &&
	Work2.uids.o = DOI1+Handle1 && Work2.metadata = Metadata1 && Work2.putcode = Putcode2 && Work2.source = Scopus &&
	Work0 in _preferred[o]
		o.groups = Group1
}

run IMPORTED_S2 {some o:ORCID,o':o.next,p:PTCris,p':p.next | 
  IMPORTED_S2_pre[p,o] && IMPORTED_S2[p,o'] && EXPORTED[p,o'] && not IMPORTED[p,o'] && IMPORT[o',p,p'] } for 20 but 2 ORCID, 2 PTCris, 3 Work

pred IMPORTED_S3_pre[p:PTCris,o:ORCID] {
	p.productions = Production0
	Production0.key = Key2 && Production0.metadata = Metadata0 && Production0.uids.p = DOI0+EID0+Handle1+DOI1
	no p.notifications
	o.groups.works = Work0+Work1+Work2
	Work0.uids.o = DOI0+EID0 && Work0.metadata = Metadata0 && Work0.putcode = Putcode0 && Work0.source = Scopus &&
	Work1.uids.o = DOI0+Handle1 && Work1.metadata = Metadata1 && Work1.putcode = Putcode1 && Work1.source = User &&
	Work2.uids.o = DOI1+Handle1 && Work2.metadata = Metadata1 && Work2.putcode = Putcode2 && Work2.source = Scopus &&
	Work0 in _preferred[o]
		o.groups = Group1
}

pred IMPORTED_S3[p:PTCris,o:ORCID] {
	p.productions = Production0
	Production0.key = Key2 && Production0.metadata = Metadata0 && Production0.uids.p = DOI0+EID0+Handle1+DOI1
	no p.notifications
	o.groups.works = Work0+Work1+Work2+Work3
	Work0.uids.o = DOI0+EID0 && Work0.metadata = Metadata0 && Work0.putcode = Putcode0 && Work0.source = Scopus &&
	Work1.uids.o = DOI0+Handle1 && Work1.metadata = Metadata1 && Work1.putcode = Putcode1 && Work1.source = User &&
	Work2.uids.o = DOI1+Handle1 && Work2.metadata = Metadata1 && Work2.putcode = Putcode2 && Work2.source = Scopus &&
	Work3.uids.o = DOI1 && Work3.metadata = Metadata1 && Work3.putcode = Putcode3 && Work3.source = User &&
	Work0 in _preferred[o]
		o.groups = Group2
}

run IMPORTED_S3 {some o:ORCID,o':o.next,p:PTCris,p':p.next | 
  IMPORTED_S3_pre[p,o] && IMPORTED_S3[p,o'] && EXPORTED[p,o'] && IMPORTED[p,o'] && IMPORT[o',p,p'] } for 20 but 2 ORCID, 2 PTCris, 4 Work


pred IMPORTED_S4_pre[p:PTCris,o:ORCID] {
	p.productions = Production0
	Production0.key = Key2 && Production0.metadata = Metadata0 && Production0.uids.p = DOI0+EID0+Handle1+DOI1
	no p.notifications
	o.groups.works = Work0+Work1+Work2+Work3
	Work0.uids.o = DOI0+EID0 && Work0.metadata = Metadata0 && Work0.putcode = Putcode0 && Work0.source = Scopus &&
	Work1.uids.o = DOI0+Handle1 && Work1.metadata = Metadata1 && Work1.putcode = Putcode1 && Work1.source = User &&
	Work2.uids.o = DOI1+Handle1 && Work2.metadata = Metadata1 && Work2.putcode = Putcode2 && Work2.source = Scopus &&
	Work3.uids.o = DOI1 && Work3.metadata = Metadata1 && Work3.putcode = Putcode3 && Work3.source = User &&
	Work0 in _preferred[o]
		o.groups = Group2
}

pred IMPORTED_S4[p:PTCris,o:ORCID] {
	p.productions = Production0
	Production0.key = Key2 && Production0.metadata = Metadata0 && Production0.uids.p = DOI0+EID0+Handle1+DOI1
	no p.notifications
	o.groups.works = Work0+Work1+Work3
	Work0.uids.o = DOI0+EID0 && Work0.metadata = Metadata0 && Work0.putcode = Putcode0 && Work0.source = Scopus &&
	Work1.uids.o = DOI0+Handle1 && Work1.metadata = Metadata1 && Work1.putcode = Putcode1 && Work1.source = User &&
	Work3.uids.o = DOI1 && Work3.metadata = Metadata1 && Work3.putcode = Putcode3 && Work3.source = User &&
	Work0 in _preferred[o]
		o.groups = Group3 + Group4
}

run IMPORTED_S4 {some o:ORCID,o':o.next,p:PTCris,p':p.next | 
  IMPORTED_S4_pre[p,o] && IMPORTED_S4[p,o'] && EXPORTED[p,o'] && IMPORTED[p,o'] && IMPORT[o',p,p'] } for 22 but 2 ORCID, 2 PTCris, 4 Work


pred IMPORTED_S5_pre[p:PTCris,o:ORCID] {
	p.productions = Production0
//	Production0.key = Key2 && Production0.metadata = Metadata0 && Production0.uids.p = DOI1+EID1+DOI0+Handle1
	no p.notifications
	o.groups.works = Work0+Work1+Work3
	Work0.uids.o = DOI0+EID0 && Work0.metadata = Metadata0 && Work0.putcode = Putcode0 && Work0.source = Scopus &&
	Work1.uids.o = DOI0+Handle1 && Work1.metadata = Metadata1 && Work1.putcode = Putcode1 && Work1.source = User &&
	Work3.uids.o = DOI1 && Work3.metadata = Metadata1 && Work3.putcode = Putcode3 && Work3.source = User &&
	Work0 in _preferred[o]
	o.groups = Group3 + Group4
}

pred IMPORTED_S5[p:PTCris,o:ORCID] {
	p.productions = Production0
	Production0.key = Key2 && Production0.metadata = Metadata0 && Production0.uids.p = DOI0+EID0+Handle1
	no p.notifications
	o.groups.works = Work0+Work1+Work3
	Work0.uids.o = DOI0+EID0 && Work0.metadata = Metadata0 && Work0.putcode = Putcode0 && Work0.source = Scopus &&
	Work1.uids.o = DOI0+Handle1 && Work1.metadata = Metadata1 && Work1.putcode = Putcode1 && Work1.source = User &&
	Work3.uids.o = DOI1 && Work3.metadata = Metadata1 && Work3.putcode = Putcode3 && Work3.source = User &&
	Work0 in _preferred[o]
}

run IMPORTED_S5 {some o:ORCID,o':o.next,p:PTCris,p':p.next | 
  IMPORTED_S5_pre[p,o] && IMPORTED_S5[p,o'] && EXPORTED[p,o'] && not IMPORTED[p,o'] && IMPORT[o',p,p'] } for 20 but 2 ORCID, 2 PTCris, 3 Work

pred IMPORTED_S6_pre[p:PTCris,o:ORCID] {
	p.productions = Production0+Production1
	Production0.key = Key2 && Production0.metadata = Metadata0 && Production0.uids.p = EID0+DOI0+Handle1
	Production1.key = Key1 && Production1.metadata = Metadata1 && Production1.uids.p = DOI1
	no p.notifications
	o.groups.works = Work0+Work1+Work3
	Work0.uids.o = DOI0+EID0 && Work0.metadata = Metadata0 && Work0.putcode = Putcode0 && Work0.source = Scopus &&
	Work1.uids.o = DOI0+Handle1 && Work1.metadata = Metadata1 && Work1.putcode = Putcode1 && Work1.source = User &&
	Work3.uids.o = DOI1 && Work3.metadata = Metadata1 && Work3.putcode = Putcode3 && Work3.source = User &&
	Work0 in _preferred[o]
	o.groups = Group3 + Group4
}

pred IMPORTED_S6[p:PTCris,o:ORCID] {
	p.productions = Production0+Production1
	Production0.key = Key2 && Production0.metadata = Metadata0 && Production0.uids.p = EID0+DOI0+Handle1
	Production1.key = Key1 && Production1.metadata = Metadata1 && Production1.uids.p = DOI1
	no p.notifications
	o.groups.works = Work0+Work1+Work2+Work3
	Work0.uids.o = DOI0+EID0 && Work0.metadata = Metadata0 && Work0.putcode = Putcode0 && Work0.source = Scopus &&
	Work1.uids.o = DOI0+Handle1 && Work1.metadata = Metadata1 && Work1.putcode = Putcode1 && Work1.source = User &&
	Work2.uids.o = DOI1+Handle1 && Work2.metadata = Metadata1 && Work2.putcode = Putcode2 && Work2.source = Scopus &&
	Work3.uids.o = DOI1 && Work3.metadata = Metadata1 && Work3.putcode = Putcode3 && Work3.source = User &&
	Work0 in _preferred[o]
}

run IMPORTED_S6 {some o:ORCID,o':o.next,p:PTCris,p':p.next | 
  IMPORTED_S6_pre[p,o] && IMPORTED_S6[p,o'] && EXPORTED[p,o'] && not IMPORTED[p,o'] && IMPORT[o',p,p'] } for 20 but 2 ORCID, 2 PTCris, 4 Work


pred IMPORTED_S8_pre[p:PTCris,o:ORCID] {
	no p.exported
	p.productions = Production0
	Production0.key = Key1 && Production0.metadata = Metadata1 && Production0.uids.p = DOI0+EID0
	no p.notifications
	no o.groups.works
}

pred IMPORTED_S8[p:PTCris,o:ORCID] {
	no p.exported
	p.productions = Production0
	Production0.key = Key1 && Production0.metadata = Metadata1 && Production0.uids.p = DOI0+EID0
	no p.notifications
	o.groups.works = Work0
	Work0.uids.o = DOI0+Handle1 && Work0.metadata = Metadata1 && Work0.putcode = Putcode0 && Work0.source = User &&
	Work0 in _preferred[o] 
}


run IMPORTED_S8 {some o:ORCID,o':o.next,p:PTCris,p':p.next | 
	IMPORTED_S8_pre[p,o] && IMPORTED[p,o] && EXPORTED[p,o] &&
	IMPORTED_S8[p,o'] && EXPORTED[p,o'] && not IMPORTED[p,o'] && IMPORT[o',p,p'] } 
for 20 but 2 ORCID, 2 PTCris, 3 Work


pred IMPORTED_S9_pre[p:PTCris,o:ORCID] {
	no p.exported
	p.productions = Production0
	Production0.key = Key1 && Production0.metadata = Metadata1 && Production0.uids.p = DOI0+EID0
	one p.notifications
	o.groups.works = Work0
	Work0.uids.o = DOI0+Handle1 && Work0.metadata = Metadata1 && Work0.putcode = Putcode0 && Work0.source = User &&
	Work0 in _preferred[o]
}

pred IMPORTED_S9[p:PTCris,o:ORCID] {
	no p.exported
	p.productions = Production0
	Production0.key = Key1 && Production0.metadata = Metadata1 && Production0.uids.p = DOI0+EID0
	one p.notifications
	o.groups.works = Work0+Work1
	Work0.uids.o = DOI0+Handle1 && Work0.metadata = Metadata1 && Work0.putcode = Putcode0 && Work0.source = User &&
	Work0 in _preferred[o] &&
	Work1.uids.o = EID0+Handle0 && Work1.metadata = Metadata3 && Work1.putcode = Putcode1 && Work1.source = Scopus &&
	Work1 in _preferred[o]
}


run IMPORTED_S9 {some o:ORCID,o':o.next,p:PTCris,p':p.next | 
	IMPORTED_S9_pre[p,o] && IMPORTED[p,o] && EXPORTED[p,o] &&
	IMPORTED_S9[p,o'] && EXPORTED[p,o'] && not IMPORTED[p,o'] && IMPORT[o',p,p'] } 
for 20 but 2 ORCID, 2 PTCris, 3 Work


pred IMPORTED_SX_pre[p:PTCris,o:ORCID] {
	no p.exported
	p.productions = Production0
	Production0.key = Key1 && Production0.metadata = Metadata1 && Production0.uids.p = DOI0+EID0
	one p.notifications
	o.groups.works = Work0
	Work0.uids.o = DOI0+Handle1 && Work0.metadata = Metadata1 && Work0.putcode = Putcode0 && Work0.source = User &&
	Work0 in _preferred[o]
}

pred IMPORTED_SX[p:PTCris,o:ORCID] {
	no p.exported
	p.productions = Production0 + Production1 + Production2
	Production0.key = Key1 && Production0.metadata = Metadata1 && Production0.uids.p = EID1+Handle1
	Production1.key = Key2 && Production1.metadata = Metadata1 && Production1.uids.p = DOI1+DOI2+EID0+EID1+Handle1+Handle0
	Production2.key = Key0 && Production2.metadata = Metadata1 && Production2.uids.p = DOI0
	no p.notifications
	o.groups.works = Work0+Work1
	Work0.uids.o = DOI2+EID1 && Work0.metadata = Metadata1 && Work0.putcode = Putcode0 && Work0.source = User
	Work1.uids.o = DOI1+EID0+Handle1+Handle0 && Work1.metadata = Metadata3 && Work1.putcode = Putcode1 && Work1.source = Scopus
}


run IMPORTED_SX {some o:ORCID,o':o.next,p:PTCris,p':p.next | 
//	IMPORTED_SX_pre[p,o] && IMPORTED[p,o] && EXPORTED[p,o] &&
	IMPORTED_SX[p,o] && EXPORTED[p,o] && not IMPORTED[p,o] && IMPORT[o,p,p'] } 
for 20 but 2 ORCID, 2 PTCris, 3 Work


pred EXPORTED_S1_pre[p:PTCris,o:ORCID] {
	p.productions = Production0+Production1
	Production0.key = Key2 && Production0.metadata = Metadata2 && Production0.uids.p = EID0+DOI0+Handle1
	Production1.key = Key1 && Production1.metadata = Metadata1 && Production1.uids.p = DOI1
	no p.notifications
	o.groups.works = Work0+Work1+Work3
	Work0.uids.o = DOI0+EID0 && Work0.metadata = Metadata0 && Work0.putcode = Putcode0 && Work0.source = Scopus &&
	Work1.uids.o = DOI0+Handle1 && Work1.metadata = Metadata1 && Work1.putcode = Putcode1 && Work1.source = User &&
	Work3.uids.o = DOI1 && Work3.metadata = Metadata1 && Work3.putcode = Putcode3 && Work3.source = User &&
	Work0 in _preferred[o]
	o.groups = Group3 + Group4
}

pred EXPORTED_S1[p:PTCris,o:ORCID] {
	p.productions = Production0+Production1
	Production0.key = Key2 && Production0.metadata = Metadata2 && Production0.uids.p = EID0+DOI0+Handle1
	Production1.key = Key1 && Production1.metadata = Metadata1 && Production1.uids.p = DOI1
	p.exported = Production0
	no p.notifications
	o.groups.works = Work0+Work1+Work3
	Work0.uids.o = DOI0+EID0 && Work0.metadata = Metadata0 && Work0.putcode = Putcode0 && Work0.source = Scopus &&
	Work1.uids.o = DOI0+Handle1 && Work1.metadata = Metadata1 && Work1.putcode = Putcode1 && Work1.source = User &&
	Work2.uids.o = DOI1+Handle1 && Work2.metadata = Metadata1 && Work2.putcode = Putcode2 && Work2.source = Scopus &&
	Work3.uids.o = DOI1 && Work3.metadata = Metadata1 && Work3.putcode = Putcode3 && Work3.source = User &&
	Work0 in _preferred[o]
}

run EXPORTED_S1 {some o:ORCID,o':o.next,p:PTCris,p':p.next | 
  EXPORTED_S1_pre[p,o] && EXPORTED_S1[p',o] && not EXPORTED[p',o] &&  IMPORTED[p',o] && EXPORT[o,o',p'] } for 20 but 2 ORCID, 2 PTCris, 4 Work


pred EXPORTED_S3_pre[p:PTCris,o:ORCID] {
	p.exported = Production0
	p.productions = Production0+Production1
	Production0.key = Key2 && Production0.metadata = Metadata2 && Production0.uids.p = EID0+DOI0+Handle1
	Production1.key = Key1 && Production1.metadata = Metadata1 && Production1.uids.p = DOI1
	no p.notifications
	o.groups.works = Work0+Work1+Work3+Work4
	Work0.uids.o = DOI0+EID0 && Work0.metadata = Metadata0 && Work0.putcode = Putcode0 && Work0.source = Scopus &&
	Work1.uids.o = DOI0+Handle1 && Work1.metadata = Metadata1 && Work1.putcode = Putcode1 && Work1.source = User &&
	Work3.uids.o = DOI1 && Work3.metadata = Metadata1 && Work3.putcode = Putcode3 && Work3.source = User &&
	Work4.uids.o = DOI0+EID0+Handle1 && Work4.metadata = Metadata2 && Work4.putcode = Putcode2 && Work4.source = PTCRIS &&	
	Work4 in _preferred[o]
	o.groups = Group0 + Group4
}

pred EXPORTED_S3[p:PTCris,o:ORCID] {
	p.productions = Production0+Production1
	Production0.key = Key2 && Production0.metadata = Metadata2 && Production0.uids.p = EID0+DOI0+Handle1
	Production1.key = Key1 && Production1.metadata = Metadata1 && Production1.uids.p = DOI1
	no p.exported 
	no p.notifications
	o.groups.works = Work0+Work1+Work3+Work4
	Work0.uids.o = DOI0+EID0 && Work0.metadata = Metadata0 && Work0.putcode = Putcode0 && Work0.source = Scopus &&
	Work1.uids.o = DOI0+Handle1 && Work1.metadata = Metadata1 && Work1.putcode = Putcode1 && Work1.source = User &&
	Work2.uids.o = DOI1+Handle1 && Work2.metadata = Metadata1 && Work2.putcode = Putcode2 && Work2.source = Scopus &&
	Work3.uids.o = DOI1 && Work3.metadata = Metadata1 && Work3.putcode = Putcode3 && Work3.source = User &&
	Work4.uids.o = DOI0+EID0+Handle1 && Work4.metadata = Metadata2 && Work4.putcode = Putcode2 && Work4.source = PTCRIS &&	
	Work4 in _preferred[o]
}

run EXPORTED_S3 {some o:ORCID,o':o.next,p:PTCris,p':p.next | 
  EXPORTED_S3_pre[p,o] && EXPORTED_S3[p',o] && not EXPORTED[p',o] &&  IMPORTED[p',o] && EXPORT[o,o',p'] } for 20 but 2 ORCID, 2 PTCris, 5 Work, 0 Group


pred EXPORTED_S4_pre[p:PTCris,o:ORCID] {
	p.exported = Production0
	p.productions = Production0+Production1
	Production0.key = Key2 && Production0.metadata = Metadata3 && Production0.uids.p = EID0+DOI0+Handle1
	Production1.key = Key1 && Production1.metadata = Metadata1 && Production1.uids.p = DOI1
	no p.notifications
	o.groups.works = Work0+Work1+Work3+Work4
	Work0.uids.o = DOI0+EID0 && Work0.metadata = Metadata0 && Work0.putcode = Putcode0 && Work0.source = Scopus &&
	Work1.uids.o = DOI0+Handle1 && Work1.metadata = Metadata1 && Work1.putcode = Putcode1 && Work1.source = User &&
	Work3.uids.o = DOI1 && Work3.metadata = Metadata1 && Work3.putcode = Putcode3 && Work3.source = User &&
	Work4.uids.o = DOI0+EID0+Handle1 && Work4.metadata = Metadata2 && Work4.putcode = Putcode2 && Work4.source = PTCRIS &&	
	Work4 in _preferred[o]
}


pred EXPORTED_S4[p:PTCris,o:ORCID] {
	p.productions = Production0+Production1
	Production0.key = Key2 && Production0.metadata = Metadata3 && Production0.uids.p = EID0+DOI0+Handle1
	Production1.key = Key1 && Production1.metadata = Metadata1 && Production1.uids.p = DOI1
	p.exported = Production0
	no p.notifications
	o.groups.works = Work0+Work1+Work3+Work4
	Work0.uids.o = DOI0+EID0 && Work0.metadata = Metadata0 && Work0.putcode = Putcode0 && Work0.source = Scopus 
	Work1.uids.o = DOI0+Handle1 && Work1.metadata = Metadata1 && Work1.putcode = Putcode1 && Work1.source = User 
	Work2.uids.o = DOI1+Handle1 && Work2.metadata = Metadata1 && Work2.putcode = Putcode2 && Work2.source = Scopus 
	Work3.uids.o = DOI1 && Work3.metadata = Metadata1 && Work3.putcode = Putcode3 && Work3.source = User 
	Work4.uids.o = DOI0+EID0+Handle1 && Work4.metadata = Metadata2 && Work4.putcode = Putcode2 && Work4.source = PTCRIS 
	Work4 in _preferred[o]
}

run EXPORTED_S4 {some o:ORCID,o':o.next,p:PTCris,p':p.next | 
  EXPORTED_S4[p',o] && not EXPORTED[p',o] &&  IMPORTED[p',o] && EXPORT[o,o',p'] } for 20 but 2 ORCID, 2 PTCris, 5 Work


pred SYNC_S2_pre[p:PTCris,o:ORCID] {
	p.exported = Production0+Production1
	p.productions = Production0+Production1
	Production0.key = Key2 && Production0.metadata = Metadata3 && Production0.uids.p = DOI0
	Production1.key = Key1 && Production1.metadata = Metadata1 && Production1.uids.p = Handle1
	no p.notifications
	o.groups.works = Work0+Work1
	Work0.uids.o = DOI0 && Work0.metadata = Metadata3 && Work0.putcode = Putcode0 && Work0.source = PTCRIS &&
	Work1.uids.o = Handle1 && Work1.metadata = Metadata1 && Work1.putcode = Putcode1 && Work1.source = PTCRIS &&
	Work0 in _preferred[o]
}


pred SYNC_S2[p:PTCris,o:ORCID] {
	p.productions = Production0+Production1
	Production0.key = Key2 && Production0.metadata = Metadata3 && Production0.uids.p = DOI0+Handle1
	Production1.key = Key1 && Production1.metadata = Metadata1 && Production1.uids.p = Handle1
	p.exported = Production0
	no p.notifications
	o.groups.works = Work0+Work1
	Work0.uids.o = DOI0 && Work0.metadata = Metadata3 && Work0.putcode = Putcode0 && Work0.source = PTCRIS &&
	Work1.uids.o = Handle1 && Work1.metadata = Metadata1 && Work1.putcode = Putcode1 && Work1.source = PTCRIS &&
	Work0 in _preferred[o]
}

run SYNC_S2 {some o:ORCID,o':o.next,p:PTCris,p':p.next | 
  /*SYNC_S2_pre[p,o] &&*/ SYNC_S2[p,o] && not EXPORTED[p,o] && IMPORTED[p,o] && EXPORT[o,o',p] && IMPORT[o',p,p'] && EXPORTED[p',o']} for 20 but 2 ORCID, 2 PTCris, 5 Work


pred EXPORTED_S5_pre[p:PTCris,o:ORCID] {
	p.exported = Production0
	p.productions = Production0
	Production0.key = Key1 && Production0.metadata = Metadata3 && Production0.uids.p = DOI0+Handle1
	no p.notifications
	o.groups.works = Work0
	Work0.uids.o = DOI0+Handle1 && Work0.metadata = Metadata3 && Work0.putcode = Putcode0 && Work0.source = PTCRIS &&
	Work0 in _preferred[o]
}


pred EXPORTED_S5[p:PTCris,o:ORCID] {
	p.exported = Production0+Production1
	p.productions = Production0+Production1
	Production0.key = Key1 && Production0.metadata = Metadata3 && Production0.uids.p = DOI0
	Production1.key = Key2 && Production1.metadata = Metadata3 && Production1.uids.p = Handle1
	no p.notifications
	o.groups.works = Work0
	Work0.uids.o = DOI0+Handle1 && Work0.metadata = Metadata3 && Work0.putcode = Putcode0 && Work0.source = PTCRIS &&
	Work0 in _preferred[o]
}

run EXPORTED_S5 {some o:ORCID,o':o.next,p:PTCris,p':p.next | 
  /*EXPORTED_S5_pre[p,o] &&*/ EXPORTED_S5[p,o] && not EXPORTED[p,o] && not IMPORTED[p,o] && EXPORT[o,o',p] && IMPORTED[p,o']} for 20 but 2 ORCID, 2 PTCris, 5 Work


pred SYNC_S1[p:PTCris,o:ORCID] {
	p.productions = Production0+Production1
	Production0.key = Key2 && Production0.metadata = Metadata2 && Production0.uids.p = EID0+DOI0+Handle1+DOI1
	Production1.key = Key1 && Production1.metadata = Metadata1 && Production1.uids.p = DOI1
	p.exported  = Production0
	no p.notifications
	o.groups.works = Work0+Work1+Work3
	Work0.uids.o = DOI0+EID0 && Work0.metadata = Metadata0 && Work0.putcode = Putcode0 && Work0.source = Scopus &&
	Work1.uids.o = DOI0+Handle1 && Work1.metadata = Metadata1 && Work1.putcode = Putcode1 && Work1.source = User &&
	Work2.uids.o = DOI1+Handle1 && Work2.metadata = Metadata1 && Work2.putcode = Putcode2 && Work2.source = Scopus &&
	Work3.uids.o = DOI1 && Work3.metadata = Metadata1 && Work3.putcode = Putcode3 && Work3.source = User &&
	Work4.uids.o = DOI0+EID0+Handle1 && Work4.metadata = Metadata2 && Work4.putcode = Putcode2 && Work4.source = PTCRIS &&	
	Work1 in _preferred[o]
	gt[Work1,Work3]
}

run SYNC_S1 {some o:ORCID,o':o.next,p:PTCris,p':p.next | 
  SYNC_S1[p,o] && not EXPORTED[p,o] && IMPORTED[p,o] && EXPORT[o,o',p] && IMPORT[o',p,p'] } for 20 but 2 ORCID, 2 PTCris, 5 Work

pred SYNC_S3_pre[p:PTCris,o:ORCID] {
	p.productions = Production0
	Production0.key = Key2 && Production0.metadata = Metadata3 && Production0.uids.p = DOI0+Handle1
	p.exported = Production0
	one p.notifications&Creation
	p.notifications.uids.p = Handle0
	o.groups.works = Work0+Work1
	Work0.uids.o = DOI0+Handle1 && Work0.metadata = Metadata3 && Work0.putcode = Putcode0 && Work0.source = PTCRIS &&
	Work1.uids.o = Handle0 && Work1.metadata = Metadata1 && Work1.putcode = Putcode1 && Work1.source = Scopus &&
	Work0 in _preferred[o]
	Work1 in _preferred[o]
}

run SYNC_S3_pre {some o:ORCID,o':o.next,p:PTCris,p':p.next | 
  SYNC_S3_pre[p,o] && SYNC_S3[p',o] && EXPORTED[p,o] && IMPORTED[p,o] && EXPORT[o,o',p'] && not IMPORTED[p',o']} for 20 but 2 ORCID, 2 PTCris, 5 Work


pred SYNC_S3[p:PTCris,o:ORCID] {
	p.productions = Production0
	Production0.key = Key2 && Production0.metadata = Metadata3 && Production0.uids.p = DOI0+Handle0
	p.exported = Production0
	one p.notifications&Creation
	p.notifications.uids.p = Handle0
	o.groups.works = Work0+Work1
	Work0.uids.o = DOI0+Handle1 && Work0.metadata = Metadata3 && Work0.putcode = Putcode0 && Work0.source = PTCRIS &&
	Work1.uids.o = Handle0 && Work1.metadata = Metadata1 && Work1.putcode = Putcode1 && Work1.source = Scopus &&
	Work0 in _preferred[o]
	Work1 in _preferred[o]
}

run SYNC_S3 {some o:ORCID,o':o.next,p:PTCris,p':p.next | 
  /*SYNC_S2_pre[p,o] &&*/ SYNC_S3[p,o] && not EXPORTED[p,o] && not IMPORTED[p,o] && EXPORT[o,o',p] && IMPORT[o',p,p'] && EXPORTED[p',o']} for 20 but 2 ORCID, 2 PTCris, 5 Work



pred EXPORTED_S6_pre[p:PTCris,o:ORCID] {
	p.exported = Production0
	p.productions = Production0+Production1
	Production0.key = Key2 && Production0.metadata = Metadata2 && Production0.uids.p = EID0+DOI0+Handle1
	Production1.key = Key1 && Production1.metadata = Metadata1 && Production1.uids.p = DOI1
	no p.notifications
	o.groups.works = Work0+Work1+Work3+Work4
	Work0.uids.o = DOI0+EID0 && Work0.metadata = Metadata0 && Work0.putcode = Putcode0 && Work0.source = Scopus &&
	Work1.uids.o = DOI0+Handle1 && Work1.metadata = Metadata1 && Work1.putcode = Putcode1 && Work1.source = User &&
	Work3.uids.o = DOI1 && Work3.metadata = Metadata1 && Work3.putcode = Putcode3 && Work3.source = User &&
	Work4.uids.o = DOI0+EID0+Handle1 && Work4.metadata = Metadata2 && Work4.putcode = Putcode2 && Work4.source = PTCRIS &&	
	Work4 in _preferred[o]
}


pred EXPORTED_S6[p:PTCris,o:ORCID] {
	p.productions = Production0+Production1
	Production0.key = Key2 && Production0.metadata = Metadata2 && Production0.uids.p = EID0+DOI0+Handle1
	Production1.key = Key1 && Production1.metadata = Metadata1 && Production1.uids.p = DOI1
	p.exported = Production0
	no p.notifications
	o.groups.works = Work0+Work1+Work3+Work4
	Work0.uids.o = DOI0+EID0 && Work0.metadata = Metadata0 && Work0.putcode = Putcode0 && Work0.source = Scopus 
	Work1.uids.o = DOI0+Handle1 && Work1.metadata = Metadata1 && Work1.putcode = Putcode1 && Work1.source = User 
	Work2.uids.o = DOI1+Handle1 && Work2.metadata = Metadata1 && Work2.putcode = Putcode2 && Work2.source = Scopus 
	Work3.uids.o = DOI1 && Work3.metadata = Metadata1 && Work3.putcode = Putcode3 && Work3.source = User 
	Work4.uids.o = DOI0+EID0+Handle1 && Work4.metadata = Metadata2 && Work4.putcode = Putcode2 && Work4.source = PTCRIS 
	Work4 in _preferred[o]
}

run EXPORTED_S6 {some o:ORCID,o':o.next,p:PTCris,p':p.next | 
  EXPORTED_S6[p',o] && EXPORTED[p',o] &&  IMPORTED[p',o] && EXPORT[o,o',p'] } for 20 but 2 ORCID, 2 PTCris, 5 Work


run Random {some o:ORCID,o':o.next,p:PTCris,p':p.next | 
	(not EXPORTED[p,o] || not EXPORTED[p,o]) && EXPORT[o,o',p] && IMPORT[o',p,p']} for 20 but 2 ORCID, 2 PTCris, 5 Work


/*pred paper_S0[p:PTCris,o:ORCID] {
	some disj p1,p2 : p.productions |
		p1.uids.p = DOI1+EID1+Handle1 && p1.metadata = Metadata1 && p1.key = Key1 &&
		p2.uids.p = DOI0+Handle0 && p2.metadata = Metadata0 && p2.key = Key0 &&
	no p.exported
	no p.notifications
	some disj w1,w2,w3 : o.groups.works | 
		w1.uids.o = DOI1+EID1 && w1.metadata = Metadata2 && w1.putcode = Putcode0 && w1.source = Scopus && w1 = Work1 &&
		w2.uids.o = EID1+Handle1 && w2.metadata = Metadata1 && w2.putcode = Putcode1 && w2.source = User && w2 = Work2 &&
		w3.uids.o = DOI0 && w3.metadata = Metadata0 && w3.putcode = Putcode2 && w3.source = User && w3 = Work0 && 
		w2 in _preferred[o]
	#o.groups.works = 3
}

run paper_S0 {some o:ORCID,p:PTCris | paper_S0[p,o] &&  EXPORTED[p,o] && IMPORTED[p,o] } for 10 but 1 ORCID, 1 PTCris, 10 Work

pred paper_S[p:PTCris,o:ORCID] {
	some disj p1,p2 : p.productions |
		p1.uids.p = DOI1+EID1+Handle1+DOI0 && p1.metadata = Metadata1 && p1.key = Key1 &&
		p2.uids.p = DOI0+Handle0 && p2.metadata = Metadata0 && p2.key = Key0 &&
		p1 in p.exported
	no p.notifications
	some disj w1,w2,w3 : o.groups.works | 
		w1.uids.o = DOI1+EID1 && w1.metadata = Metadata2 && w1.putcode = Putcode0 && w1.source = Scopus && w1 = Work1 &&
		w2.uids.o = EID1+Handle1 && w2.metadata = Metadata1 && w2.putcode = Putcode1 && w2.source = User && w2 = Work2 &&
		w3.uids.o = DOI0 && w3.metadata = Metadata0 && w3.putcode = Putcode2 && w3.source = User && w3 = Work0 && 
		w2 in _preferred[o]
	#o.groups.works = 3
}

run paper_S {some o:ORCID,o':o.next,p:PTCris,p':p.next | paper_S[p,o] && not EXPORTED[p,o] && IMPORTED[p,o] && EXPORT[o,o',p] && not IMPORTED[p,o'] && IMPORT[o',p,p'] } for 7 but 2 ORCID, 2 PTCris, 4 Work, 2 Productio*/

pred BASE0 [p:PTCris,o:ORCID] {
	p.productions = Production0+Production1
	Production0.key = Key0 && Production0.metadata = Metadata0 && Production0.uids.p = DOI0+Handle0
	Production1.key = Key1 && Production1.metadata = Metadata1 && Production1.uids.p = DOI1+Handle1
	p.exported  = Production1
	some p.notifications
	o.groups = Group0 + Group1
	Group0.works = Work0+Work1
	o.groups.works = Work0+Work1+Work2
	Work0.uids.o = DOI1 && Work0.metadata = Metadata2 && Work0.putcode = Putcode0 && Work0.source = Scopus 
	Work1.uids.o = DOI1+Handle1 && Work1.metadata = Metadata1 && Work1.putcode = Putcode2 && Work1.source = PTCRIS 
	Work2.uids.o = DOI2 && Work2.metadata = Metadata3 && Work2.putcode = Putcode1 && Work2.source = User 
	Work1 in _preferred[o]
}

run BASE0 {some o:ORCID, p:PTCris | BASE0[p,o]&&EXPORTED[p,o]&&IMPORTED[p,o]} for 18 but 1 ORCID, 1 PTCris, 6 Work, 3 Production


pred BASE1 [p:PTCris,o:ORCID] {
	p.productions = Production0+Production1
	Production0.key = Key0 && Production0.metadata = Metadata0 && Production0.uids.p = DOI0+Handle0
	Production1.key = Key1 && Production1.metadata = Metadata1 && Production1.uids.p = DOI1+Handle1
	p.exported  = Production1 + Production0
	some p.notifications
	o.groups = Group0 + Group1
	Group0.works = Work0+Work1
	o.groups.works = Work0+Work1+Work2
	Work0.uids.o = DOI1 && Work0.metadata = Metadata2 && Work0.putcode = Putcode0 && Work0.source = Scopus 
	Work1.uids.o = DOI1+Handle1 && Work1.metadata = Metadata1 && Work1.putcode = Putcode2 && Work1.source = PTCRIS 
	Work2.uids.o = DOI2 && Work2.metadata = Metadata3 && Work2.putcode = Putcode1 && Work2.source = User 
	Work1 in _preferred[o]
}

run BASE1 {some o:ORCID, o':o.next, p:PTCris | BASE1[p,o]&&EXPORTED[p,o']&&IMPORTED[p,o]&&IMPORTED[p,o']} for 18 but 2 ORCID, 1 PTCris, 6 Work, 3 Production


pred BASE2 [p:PTCris,o:ORCID] {
	p.productions = Production0+Production1
	Production0.key = Key0 && Production0.metadata = Metadata0 && Production0.uids.p = DOI0+Handle0
	Production1.key = Key1 && Production1.metadata = Metadata1 && Production1.uids.p = DOI1+Handle1
	no p.exported
	some p.notifications
	o.groups = Group0 + Group1
	Group0.works = Work0+Work1
	o.groups.works = Work0+Work1+Work2
	Work0.uids.o = DOI1 && Work0.metadata = Metadata2 && Work0.putcode = Putcode0 && Work0.source = Scopus 
	Work1.uids.o = DOI1+Handle1 && Work1.metadata = Metadata1 && Work1.putcode = Putcode2 && Work1.source = PTCRIS 
	Work2.uids.o = DOI2 && Work2.metadata = Metadata3 && Work2.putcode = Putcode1 && Work2.source = User 
	Work1 in _preferred[o]
}

run BASE2 {some o:ORCID, o':o.next, p:PTCris | BASE2[p,o]&&EXPORTED[p,o']&&IMPORTED[p,o]&&IMPORTED[p,o']} for 18 but 2 ORCID, 1 PTCris, 6 Work, 3 Production


// how are UIDs not assigned to states where work does not exist? they are

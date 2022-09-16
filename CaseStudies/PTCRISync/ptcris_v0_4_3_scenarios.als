/*
 * A formalization of a an ORCID-based synchronization framework 
 * for PTCRIS, as described in https://github.com/fccn/PTCRISync/wiki.
 * 
 * author: A. Cunha, N. Macedo 
 */

open ptcris_v0_4_3

// Calculates the preferred works of an ORCID repository.
fun _preferred[] : ORCID -> Work {
	{o:ORCID, w : o.groups.works | some g : o.groups | w = preferred[g] }
}

// Calculates all the works of an ORCID repository.
fun _works[] : ORCID -> Work {
	{o:ORCID, w : Work | w in o.groups.works }
}

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

run Random {
	some o:ORCID,o':o.next,p:PTCris,p':p.next {
		(not EXPORTED[p,o] || not EXPORTED[p,o]) && EXPORT[o,o',p] && IMPORT[o',p,p']
		some p.exported
		some p.productions - p.exported
		some x,x':p.productions | some x.uids.p & x'.uids.p
		some x:p.productions,x':o.groups | some x.uids.p & x'.uids.p
		some p'.notifications&Creation
		some p'.notifications&Modification
	}
} for 20 but 2 ORCID, 2 PTCris, 7 Work

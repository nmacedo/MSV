open util/ordering[State]
open util/ordering[Id]
open util/ordering[Source]

sig State {}

abstract sig Paper {
	title : one Title,
	ids : set UniqueId,
	type : one Type,
	year : lone Year,
	putcode : Id -> State
}

abstract sig UniqueId {}
one sig DOI, EID, ISBN extends UniqueId {}

abstract sig Title, Year {}

enum Type {Conference,Journal,Book}

// ORCID papers
sig Work extends Paper {
	orcid : set State,
	selected : set State,
	source : one Source
}

abstract sig Id {}

enum Source {User,DeGois,Scopus,Recaap}

// consistency of ORCID repositories
fact ORCID {
    // ORCID selected papers exist in the repository
	all s : State | selected.s in orcid.s
	// only a single selected work by equivalence class
	all s : State, w : orcid.s | one y : selected.s | y in w.*same
    // every work has a unique putcode within state 
	all s : State | Work<:putcode.s in orcid.s lone -> one Id

	all w:Work | one w.putcode.State
}

// DeGois papers
sig Production extends Paper {
	key : lone Id,
	degois : set State,
	pending : set State
}

/*====================Preferred=====================*/
// reflexive predicate testing if one work is preferred to another
// a work is preferred over another if its source is preferred
// is the source is the same, use the putcode to disambiguate
// ORCID selected is ignored
pred preferred[s : State, w,w' : Work] {
	(gt[w.source,w'.source]) or 
	(w.source = w'.source && lte[w.putcode.s,w'.putcode.s])
}

// retrieves the set of preferred works in a state
fun preferred : State -> set Work {
     {s:State, x : orcid.s | no w : orcid.s&x.same-x | preferred[s,w,x] }
}

/*===================Modifications====================*/
// modifications are pending productions with a key assigned, refering to the accepted production
fun mods : set Production {
	{x:pending.State | some x.key}
}

// relation between modifications and targets
fun modifies : Production -> Production {
	{x:pending.State, y:degois.State | x.key = y.key}
}

// consistency of DeGois repositories
fact DeGois {
    // no paper is simultaneosly pending and accepted as a production in a DeGois repository
	no pending.State & degois.State
	// keys are unique for accepted papers
	all s : State | degois.s<:key in degois.s lone -> one Id  
	// if (pending or accepted) production share a key, then they are identical module ids
	all s : State , disj p,p':degois.s+pending.s | (some p.key && p.key = p'.key) => equal_mod_ids[p,p'] && p.putcode.s = p'.putcode.s 
	// if pending productions have keys, then they refer to updates of an accepted production
	all s : State , p:pending.s | some p.key => some p':degois.s | p.key = p'.key
	// if pending productions have no key, they refer to fresh productions, without a match in ORCID
	all s : State , p:pending.s | no p.key => no p.putcode.s
    // ORCID works appear at most once in a DeGois repository
	all s : State | all i : Id | lone putcode.s.i & (pending.s) // tautology 
    // ORCID works appear pending most once in a DeGois repository
	all s : State | all i : Id | lone putcode.s.i & (degois.s) // tautology 
    // a pending paper has no equivalent paper pending
	all s : State | all p : pending.s, p' : pending.s | same_production[s,p,p'] implies p=p'

}

/*=====================Identity=====================
 * two papers are IDENTICAL if they share every field (minus putcodes)  			*/

// tests if two papers are identical
pred equal [p,p' : Paper] {
	p.title = p'.title and p.ids = p'.ids and p.type = p'.type and p.year = p'.year
}

// non-reflexive relation of identical papers
fun equal : Paper -> Paper {
	{x,y : Paper | x!=y and equal[x,y]}
}

/*====================Equivalence====================
 * two papers are EQUIVALENT if they share some unique identifiers 
 * papers without any unique identifier are equivalent to nothing       
 * this means that equivalence is NOT weaker than identity: 
 * productions without ids may be equal															  */

// tests if two papers are equivalent
// identity test required for reflexivity of papers without identifiers
pred same [p,p' : Paper] {
	some p.ids & p'.ids || p = p'
}

// tests if two works are equivalent within an ORCID repository
pred same_work [s : State, w,w' : Work] {
	w->w' in same_work[s]
}

// tests if two productions are equivalent within a DeGois repository
pred same_production [s : State, p,p' : Production] {
	p->p' in same_production[s]
}

// non-reflexive equivalence relation
fun same : Paper -> Paper {
	{x,y : Paper | x!=y and same[x,y]}
}

// non-reflexive equivalent relation within ORCID repository
fun same_work [s : State] : Work -> Work {
	*{x,y : orcid.s | same[x,y]} & Work -> Work
}

// non-reflexive equivalent relation within DeGois repository
fun same_production [s : State] : Production -> Production {
	*{x,y : degois.s+pending.s | same[x,y]} &  Production -> Production 
}

/*===================Aggregation====================
 * Productions should aggregate the unique identifiers of a group of works */

// tests if a production has exactly the identifiers of a group of works
// Warning: a production without ids always aggregates works without ids
pred aggregates [s:State,p:Production,w:Work] {
	p.ids = (w+w.same&orcid.s).ids
}

// tests if a production aggregates a group of works and all other fields are identical
pred equal_aggregates [s:State,p:Production,w : Work] {
	p.title = w.title and p.type = w.type and p.year = w.year and aggregates[s,p,w]
}

// tests if a production shares some identifiers but all other fields are identical
pred equal_mod_ids [p,p':Paper] {
	same[p,p'] && p.title = p'.title and p.type = p'.type and p.year = p'.year
}

// tests if a production has at least all the identifiers of a group of works
pred subsumes [s:State,p:Production,w:Work] {
	(w+w.same&orcid.s).ids in p.ids && some p.ids
}

// relation depicting the productions that aggregate works
fun subsumes : State -> Production -> Work {
	{s:State,x:Production,y :Work | subsumes[s,x,y]}
}

/*===================Consistency====================*/

pred consistent [s : State] {
	// C1: for every ORCID work from DeGois there is an identical production in DeGois with the respective putcode
	all w : orcid.s & source.DeGois | some p : degois.s & putcode.s.Id | equal[w,p] && w.putcode.s = p.putcode.s
	
	// C2: for every DeGois production with a putcode there is an identical ORCID work with the same putcode
	all p : degois.s & putcode.s.Id | some w : orcid.s & source.DeGois | equal[w,p] && w.putcode.s = p.putcode.s

	// C3: for every ORCID work, there is in DeGois either an equivalent production that subsumes the ids of the group or a pending in DeGois
	all w : orcid.s-source.DeGois | (some p : degois.s | same[p,w]) => 
		(some p : degois.s | subsumes[s,p,w] || some p : pending.s | some p.key)

	// C4:
	all w : orcid.s-source.DeGois | (no p : degois.s | same[p,w]) => 
		(some p : pending.s, w' : (w.same+w)&s.preferred | equal_aggregates[s,p,w'])
	
	// C5: for every pending insertion in DeGois, there is a group that is being aggregated and remaining fields from the preferred and no other accepted production that subsumes that group
	all p : pending.s | no p.key => (some w : s.preferred | DeGois not in w.source && equal_aggregates[s,p,w] and no p' : degois.s | same[p',p])

	// C6: for every pending modification in DeGois, there is a group that is being aggregated
	all p : pending.s | some p.key => some w : orcid.s | DeGois not in w.source && aggregates[s,p,w] && p.ids not in ((degois.s)&(key.(p.key))).ids
}

/*===================Synchronization===================*/

pred sync [s,s' : State] {
	// S1: Não altera works de outras sources
	orcid.s' & source.(Source-DeGois) = orcid.s & source.(Source-DeGois)
	all w : selected.s&orcid.s' | w in selected.s'

	// S2: As productions no degois não se alteram (mas podem deixar de estar no orcid)
	(degois.s').key = (degois.s).key
	all p : degois.s | some p' : degois.s' | p.key = p'.key and p.title = p'.title and p.ids = p'.ids and p.type = p'.type and p.year = p'.year

	// Só ficam no orcid works com source degois cujo putcode existe no degois: apaga os que já não estão
	// no degois e altera os restantes para ficarem iguais


	all p : degois.s | (some w : orcid.s | w.putcode.s = p.putcode.s) implies (some p' : degois.s' | some p'.putcode.s' && p'.putcode.s' = p.putcode.s and p'.key = p.key)
    all p : degois.s' | some p.putcode.s' implies some w : orcid.s, p' : degois.s | w.putcode.s = p'.putcode.s /*and p'.putcode.s = p.putcode.s'*/ and p'.key = p.key

	all w : orcid.s' | (some p : degois.s | same[w,p]) => (some p':degois.s' | subsumes[s',p',w] || some p'':pending.s' | aggregates[s',p'',w] && some p''.key)

	consistent[s']
}

pred same_state[s,s' : State] {
	all w : orcid.s | some w' : orcid.s' | equal[w,w'] && w.putcode.s = w'.putcode.s'
	all w : orcid.s' | some w' : orcid.s | equal[w,w'] && w.putcode.s' = w'.putcode.s
	all p : degois.s | some p' : degois.s' | p.key = p'.key and equal[p,p'] && p.putcode.s = p'.putcode.s'
	all p : degois.s' | some p' : degois.s | p.key = p'.key and equal[p,p'] && p.putcode.s' = p'.putcode.s
	all p : pending.s | some p' : pending.s' | equal[p,p'] && p.putcode.s = p'.putcode.s'
	all p : pending.s' | some p' : pending.s | equal[p,p'] && p.putcode.s' = p'.putcode.s
}

check hippocratic {
	all s : State, s' : s.next | consistent[s] and sync[s,s'] implies same_state[s,s']
} for 4 but 2 State

check deterministic {
	all s : State, s' : s.next, s'' : s.next.next | not consistent[s] and sync[s,s'] and sync[s,s''] implies same_state[s',s'']
} for 3 but 3 State


//======================================================
//=======================Scenarios==========================
//======================================================

one sig Id1,Id2,Id3 extends Id {}
one sig Year1,Year2 extends Year {}
one sig Title1,Title2 extends Title {}

pred P2_1id [s:State,p:Production] {
	p.ids = DOI
	p.key = Id1
	p.putcode.s = none
	p.title = Title2
	p.year = Year2
	p.type = Conference
}

pred P1_1id [s:State,p:Production] {
	p.ids = DOI
	p.key = Id2
	p.putcode.s = none
	p.title = Title1
	p.year = Year1
	p.type = Conference
}


pred P1_2id [s:State,p:Production] {
	p.ids = DOI+EID
	p.key = Id2
	p.putcode.s = none
	p.title = Title1
	p.year = Year1
	p.type = Conference
}



pred P2_2id [s:State,p:Production] {
	p.ids = DOI+ISBN
	p.key = Id1
	p.putcode.s = none
	p.title = Title2
	p.year = Year2
	p.type = Conference
}

pred P2_2id'_Sync [s:State,p:Production] {
	p.ids = DOI+EID
	p.key = Id1
	one p.putcode.s
	p.title = Title2
	p.year = Year2
	p.type = Conference
}

pred P1_1id_Sync [s:State,p:Production] {
	p.ids = DOI
	p.key = Id1
	one p.putcode.s
	p.title = Title1
	p.year = Year1
	p.type = Conference
}


pred P1_0Id_Sync [s:State,p:Production] {
	p.ids = none
	p.key = Id1
	one p.putcode.s
	p.title = Title1
	p.year = Year1
	p.type = Conference
}

pred W1_0Id_Sync [s:State,w:Work] {
	w.ids = none
	one w.putcode.s
	w.title = Title1
	w.year = Year1
	w.type = Conference
	w.source = DeGois
}

pred W1_0Id_Pref_Select [s:State,w:Work] {
	w.ids = none
	one w.putcode.s
	w.title = Title1
	w.year = Year1
	w.type = Conference
	w.source = Scopus
	w in selected.s
}

pred W1_0Id_NoPref_Select [s:State,w:Work] {
	w.ids = none
	one w.putcode.s
	w.title = Title1
	w.year = Year1
	w.type = Conference
	w.source = User
	w in selected.s
}

pred P2_2id_Sync [s:State,p:Production] {
	p.ids = DOI+ISBN
	p.key = Id1
	one p.putcode.s
	p.title = Title2
	p.year = Year2
	p.type = Conference
}


pred W2_1Id_Pref_Select [s:State,w:Work] {
	w.ids = DOI
	w.title = Title2
	w.year = Year2
	w.type = Conference
	w.source = Scopus
	w in selected.s
}

pred W2_1Id_Pref [s:State,w:Work] {
	w.ids = DOI
	w.title = Title2
	w.year = Year2
	w.type = Conference
	w.source = Scopus
	w not in selected.s
}

pred W2_1Id_NoPref [s:State,w:Work] {
	w.ids = DOI
	w.title = Title2
	w.year = Year2
	w.type = Conference
	w.source = User
	w not in selected.s
}

pred W2_1Id_NoPref_Select [s:State,w:Work] {
	w.ids = DOI
	w.title = Title2
	w.year = Year2
	w.type = Conference
	w.source = User
	w in selected.s
}



pred W2_2Id_Sync_Select [s:State,w:Work] {
	w.ids = DOI+ISBN
	w.title = Title2
	w.year = Year2
	w.type = Conference
	w.source = DeGois
	w in selected.s
}


pred W1_1Id_Sync_Select [s:State,w:Work] {
	w.ids = DOI
	w.title = Title1
	w.year = Year1
	w.type = Conference
	w.source = DeGois
	w in selected.s
}


pred W1_1Id_Sync [s:State,w:Work] {
	w.ids = DOI
	w.title = Title1
	w.year = Year1
	w.type = Conference
	w.source = DeGois
	w not in selected.s
}

pred W1_1Id_NoPref_Select [s:State,w:Work] {
	w.ids = DOI
	w.putcode.s = Id1
	w.source = User
	w.year = none
	w.title = Title1
	w.type = Conference
	w in selected.s
}

pred W1_1Id'_Pref_Select [s:State,w:Work] {
	w.ids = EID
	w.putcode.s = Id3
	w.source = Scopus
	w.year = none
	w.title = Title1
	w.type = Conference
	w in selected.s
}

pred W1_1Id_NoPref[s:State,w:Work] {
	w.ids = DOI
	w.putcode.s = Id3
	w.source = User
	w.year = Year1
	w.title = Title1
	w.type = Conference
	w not in selected.s
}



pred W2_2Id_Pref_Select [s:State,w:Work] {
	w.ids = DOI+EID
	w.putcode.s = Id1
	w.source = Scopus
	w.year = Year2
	w.title = Title2
	w.type = Conference
	w in selected.s
}


pred W1_1Id_Pref_Select [s:State,w:Work] {
	w.ids = DOI
	w.putcode.s = Id1
	w.source = Scopus
	w.year = none
	w.title = Title1
	w.type = Conference
	w in selected.s
}


pred W1_2Id_Pref_Select [s:State,w:Work] {
	w.ids = DOI+EID
	w.putcode.s = Id1
	w.source = Scopus
	w.year = none
	w.title = Title1
	w.type = Conference
	w in selected.s
}


pred W1_2Id_NoPref[s:State,w:Work] {
	w.ids = DOI+EID
	w.putcode.s = Id1
	w.source = User
	w.year = none
	w.title = Title1
	w.type = Conference
	w not in selected.s
}


pred W1_2Id_NoPref_Select[s:State,w:Work] {
	w.ids = DOI+EID
	w.putcode.s = Id1
	w.source = User
	w.year = none
	w.title = Title1
	w.type = Conference
	w in selected.s
}


// Cenários E1: entradas no ORCID sem equivalente no DeGois
// Cenário E1a: nova entrada no ORCID com identificador único sem equivalente prévio no DeGois
pred E1a[s:State] {
   	one w : orcid.s | W1_1Id_NoPref_Select[s,w]
   	no degois.s
    one orcid.s
	no pending.s
}

run E1a {
	some s : State, s' : s.next | not consistent[s] and E1a[s] and sync[s,s']
} for 7 but 2 State


// Cenário E1b: nova entrada no ORCID sem identificador único sem equivalente prévio no DeGois
pred E1b[s:State] {
   	one w : orcid.s | W1_0Id_NoPref_Select[s,w]
   	no degois.s
    one orcid.s
	no pending.s
}

run E1b {
	some s : State, s' : s.next | /*not consistent[s] and*/ E1b[s] and sync[s,s']
} for 7 but 2 State


// Cenários E2: grupos no ORCID sem equivalente no DeGois
// Cenário E2a: preferido contem mais ids
pred E2a[s:State] {
   	some disj w,w' : orcid.s | 
		W1_1Id_NoPref[s,w] && W2_2Id_Pref_Select[s,w']
   	no degois.s
    # orcid.s = 2
	no pending.s
}

run E2a {
	some s : State, s' : s.next | not consistent[s] and E2a[s] and sync[s,s']
} for 7 but 2 State

// Cenário E2b: preferido contem menos ids
pred E2b[s:State] {
   	some disj w,w' : orcid.s | 
		W1_2Id_NoPref_Select[s,w] && W2_1Id_Pref[s,w']
   	no degois.s
    # orcid.s = 2
	no pending.s
}

run E2b {
	some s : State, s' : s.next | not consistent[s] and E2b[s] and sync[s,s']
} for 7 but 2 State


// Cenário E2c: ids disjuntos
pred E2c[s:State] {
   	some disj w,w' : orcid.s | 
		W1_1Id_NoPref_Select[s,w] && W1_1Id'_Pref_Select[s,w']
   	no degois.s
    # orcid.s = 2
	no pending.s
}

run E2c {
	some s : State, s' : s.next | not consistent[s] and E2c[s] and sync[s,s']
} for 7 but 2 State


// Cenários E3: utilizador aceita sugestões de novos artigos
// Warning: putcode do pending tem que cair quando é aceite
// Cenário E3a: entrada com identificador é aceite (pós-E1a)
pred E3a[s:State] {
   	one w : orcid.s, p:degois.s | 
		(w.source = User && w.ids = DOI && w.type = Conference && w.putcode.s = Id2 && w.title = Title1 && w.year = Year1 &&
	 	 p.ids = DOI && p.type = Conference && p.putcode.s = none && p.title = Title1 && p.year = Year1)

   	one degois.s
    one orcid.s
	no pending.s
}

run E3a {
	some s : State, s' : s.next |  consistent[s] and E3a[s] and sync[s,s']
} for 7 but 2 State

// Cenário E3b: entrada sem identificador é aceite (pós-E1b)
pred E3b[s:State] {
   	one w : orcid.s, p:degois.s | 
		(w.source = User && w.ids = none && w.type = Conference && w.putcode.s = Id2 && w.title = Title1 && w.year = Year1 &&
	 	 p.ids = none && p.type = Conference && p.putcode.s = none && p.title = Title1 && p.year = Year1)

   	one degois.s
    one orcid.s
	no pending.s
}

run E3b {
	some s : State, s' : s.next | not consistent[s] and E3b[s] and sync[s,s']
} for 7 but 2 State

// Cenário E3c: entrada sem identificador é novamente aceite (pós-E3b)
pred E3c[s:State] {
   	some w : orcid.s, disj p,p':degois.s | 
		(w.source = User && w.ids = none && w.type = Conference && w.putcode.s = Id2 && w.title = Title1 && w.year = Year1 &&
	 	 p.ids = none && p.type = Conference && p.putcode.s = none && p.title = Title1 && p.year = Year1 && 
	 	 p'.ids = none && p'.type = Conference && p'.putcode.s = none && p'.title = Title1 && p'.year = Year1)

   	# degois.s = 2
    one orcid.s
	no pending.s
}

run E3c {
	some s : State, s' : s.next | not consistent[s] and E3c[s] and sync[s,s']
} for 7 but 2 State


// Cenários E4: novas entradas no ORCID com semelhantes no DeGois
// Cenário E4a: a nova entrada partilha ids com a existente no DeGois
pred E4a[s:State] {
   	one w : orcid.s, p : degois.s | 
			(w.source = User && same[w,p] && w.ids = DOI && w.title = Title1 && w.year = Year1 && w.type = Conference &&
			p.ids = DOI+EID && p.type = Conference && p.title = Title1 && p.year = Year1 && no p.putcode.s)
	one degois.s
	one orcid.s
   	no pending.s
}

run E4a {
	some s : State, s' : s.next |  consistent[s] and E4a[s] and sync[s,s']
} for 4 but 2 State

pred E4a_pre[s:State] {
   	some p : degois.s | 
		p.ids = DOI+EID && no p.putcode.s && p.type = Conference && p.key = Id1 && p.title = Title1 && p.year = Year1

	one degois.s
	no orcid.s
   	no pending.s
}

run E4a_pre {
	some s : State | consistent[s] && E4a_pre[s]
} for 5 but 1 State


// Cenário E4b: a nova entrada não partilha ids com a existente no DeGois
pred E4b[s:State] {
  	one w : orcid.s, p : degois.s | 
			(w.source = User && w.ids = DOI && w.title = Title1 && w.year = Year1 && w.type = Conference &&
			p.ids = EID && p.type = Conference && p.title = Title1 && p.year = Year1 && no p.putcode.s)
	one degois.s
	one orcid.s
   	no pending.s
}

run E4b {
	some s : State, s' : s.next | not  consistent[s] && E4b[s] and sync[s,s']
} for 3 but 2 State

pred E4b_pre[s:State] {
   	some p : degois.s | 
		p.ids = EID && no p.putcode.s && p.type = Conference && p.key = Id3 && p.title = Title1 && p.year = Year1

	one degois.s
	no orcid.s
   	no pending.s
}

run E4b_pre {
	some s : State | consistent[s] && E4b_pre[s]
} for 5 but 1 State

// Cenário E4c: a nova entrada partilha ids com a existente no DeGois
pred E4c[s:State] {
   	one w : orcid.s, p : degois.s | 
			(w.source = User && same[w,p] && w.ids = DOI+EID && w.title = Title1 && w.year = Year1 && w.type = Conference &&
			p.ids = DOI && p.type = Conference && p.title = Title1 && p.year = Year1 && no p.putcode.s)
	one degois.s
	one orcid.s
   	no pending.s
}

run E4c {
	some s : State, s' : s.next | not consistent[s] and E4c[s] and sync[s,s']
} for 4 but 2 State


pred E4c_pre[s:State] {
   	some p : degois.s | 
		p.ids = DOI && no p.putcode.s && p.type = Conference && p.key = Id1 && p.title = Title1 && p.year = Year1

	one degois.s
	no orcid.s
   	no pending.s
}

run E4c_pre {
	some s : State | consistent[s] && E4c_pre[s]
} for 5 but 1 State

// Cenários E5: novas entradas no ORCID agrupam com existentes
// Cenário E5a: a nova entrada não introduz novos ids para o DeGois
pred E5a[s:State] {
   	some disj w,w' : orcid.s, p : degois.s | 
			(w.source = User && same[w,p] && w.ids = DOI && w.title = Title1 && w.year = Year1 && w.type = Conference && w.putcode.s = Id1 &&
			 w'.source = Scopus && w'.ids = DOI+EID && w'.title = Title2 && w'.year = Year2 && w'.type = Conference &&
	    	 p.ids = DOI+EID && p.type = Conference && p.title = Title1 && p.year = Year1 && no p.putcode.s && p.key = Id1)
	one degois.s
	# orcid.s = 2
   	no pending.s
}

run E5a {
	some s : State, s' : s.next | consistent[s] and E5a[s] and sync[s,s']
} for 4 but 2 State

pred E5a_pre[s:State] {
   	some disj w: orcid.s, p : degois.s | 
			(w.source = User && same[w,p] && w.ids = DOI && w.title = Title1 && w.year = Year1 && w.type = Conference && w.putcode.s = Id1 &&
			 p.ids = DOI+EID && p.type = Conference && p.title = Title1 && p.year = Year1 && no p.putcode.s && p.key = Id1)
	one degois.s
	one orcid.s 
   	no pending.s
}

run E5a_pre {
	some s : State | consistent[s] && E5a_pre[s]
} for 5 but 1 State


// Cenário E5a: a nova entrada é preferida e introduz novos ids para o DeGois
pred E5b[s:State] {
   	some disj w,w' : orcid.s, p : degois.s | 
			(w.source = User && same[w,p] && w.ids = DOI && w.title = Title1 && w.year = Year1 && w.type = Conference &&
			 w'.source = Scopus && w'.ids = DOI+EID && w'.title = Title2 && w'.year = Year2 && w'.type = Conference && w' in s.preferred &&
	    	 p.ids = DOI && p.type = Conference && p.title = Title1 && p.year = Year1 && no p.putcode.s)
	one degois.s
	# orcid.s = 2
   	no pending.s
}

run E5b {
	some s : State, s' : s.next | not consistent[s] and E5b[s] && sync[s,s']
} for 4 but 2 State

pred E5b_pre[s:State] {
   	some disj w: orcid.s, p : degois.s | 
			(w.source = User && same[w,p] && w.ids = DOI && w.title = Title1 && w.year = Year1 && w.type = Conference && w.putcode.s = Id2 &&
			 p.ids = DOI && p.type = Conference && p.title = Title1 && p.year = Year1 && no p.putcode.s && p.key = Id1)
	one degois.s
	one orcid.s 
   	no pending.s
}

run E5b_pre {
	some s : State | consistent[s] && E5b_pre[s]
} for 5 but 1 State

// Cenário E5a: a nova entrada não é preferida e introduz novos ids para o DeGois
pred E5c[s:State] {
   	some disj w,w' : orcid.s, p : degois.s | 
			(w.source = Scopus && same[w,p] && w.ids = DOI && w.title = Title1 && w.year = Year1 && w.type = Conference &&
			 w'.source = User && w'.ids = DOI+EID && w'.title = Title2 && w'.year = Year2 && w'.type = Conference && w' not in s.preferred &&
	    	 p.ids = DOI && p.type = Conference && p.title = Title1 && p.year = Year1 && no p.putcode.s)
	one degois.s
	# orcid.s = 2
   	no pending.s
}

run E5c {
	some s : State, s' : s.next | not consistent[s] and E5c[s] && sync[s,s']
} for 4 but 2 State


// Cenários E6: novas entradas no DeGois
// Cenário E6a: não existe trabalho com identificadores partilhados no ORCID
pred E6a[s:State] {
   	some p : degois.s  | 
		p.ids = DOI && no p.putcode.s && p.title = Title1 && p.year = Year1 && p.type = Conference && p.key = Id1
	one degois.s
	no orcid.s
   	no pending.s
}

run E6a {
	some s : State, s' : s.next | consistent[s] && E6a[s] and sync[s,s']
} for 7 but 2 State

// Cenário E6b:  existe trabalho com identificadores exatos no ORCID
pred E6b[s:State] {
   	some p : degois.s, w : orcid.s, p':pending.s  | 
		p.ids = DOI && no p.putcode.s && p.title = Title1 && p.year = Year1 && p.type = Conference && p.key = Id1 &&
		w. ids = DOI && w.title = Title1 && no w.year && w.source = User && w.type = Conference &&
		p'.ids = DOI && p'.title = Title1 && no p'.year && p'.type = Conference && no p'.key
	one degois.s
	one orcid.s
   	one pending.s
}

run E6b {
	some s : State, s' : s.next | not consistent[s] && E6b[s] and sync[s,s']
} for 7 but 2 State

pred E6b_pre[s:State] {
   	some w: orcid.s | 
		w.source = User && w.putcode.s = Id1 && w.type = Conference && w.title = Title1 && no w.year && w.ids = DOI

	no degois.s
	one orcid.s 

}

run E6b_pre {
	some s : State | consistent[s] && E6b_pre[s]
} for 5 but 1 State


// Cenário E6b:  existe trabalho com alguns identificadores no ORCID
pred E6c[s:State] {
   	some p : degois.s, w : orcid.s, p':pending.s  | 
		p.ids = DOI+EID && no p.putcode.s && p.title = Title1 && p.year = Year1 && p.type = Conference && p.key = Id1 &&
		w. ids = DOI && w.title = Title1 && no w.year && w.source = User && w.type = Conference &&
		p'.ids = DOI && p'.title = Title1 && no p'.year && p'.type = Conference && no p'.key
	one degois.s
	one orcid.s
   	one pending.s
}

run E6c {
	some s : State, s' : s.next | not consistent[s] && E6c[s] and sync[s,s']
} for 7 but 2 State

// Cenário E6b:  existe trabalho com identificadores extra no ORCID
pred E6d[s:State] {
   	some p : degois.s, w : orcid.s, p':pending.s  | 
		p.ids = DOI && no p.putcode.s && p.title = Title1 && p.year = Year1 && p.type = Conference && p.key = Id1 &&
		w. ids = DOI+EID && w.title = Title1 && no w.year && w.source = User && w.type = Conference &&
		p'.ids = DOI && p'.title = Title1 && no p'.year && p'.type = Conference && no p'.key
	one degois.s
	one orcid.s
   	one pending.s
}

run E6d {
	some s : State, s' : s.next | not consistent[s] && E6d[s] and sync[s,s']
} for 7 but 2 State

pred E6d_pre[s:State] {
   	some w: orcid.s | 
		w.source = User && w.putcode.s = Id1 && w.type = Conference && w.title = Title1 && no w.year && w.ids = DOI+EID

	no degois.s
	one orcid.s 

}

run E6d_pre {
	some s : State | consistent[s] && E6d_pre[s]
} for 5 but 1 State


// Cenários E7: atualização de produções DeGois
// Cenário E7a: mantem os identificadores
pred E7a[s:State] {
   	some p : degois.s, w : orcid.s  | 
		p.ids = DOI && no p.putcode.s && p.title = Title2 && p.year = Year2 && p.type = Conference && p.key = Id1 &&
		w. ids = DOI && w.title = Title1 && Year1 = w.year && w.source = User && w.type = Conference && w.putcode.s = Id3 
	one degois.s
	one orcid.s
   	no pending.s
}

run E7a {
	some s : State, s' : s.next |  consistent[s] && E7a[s] and sync[s,s']
} for 5 but 2 State

pred E7a_pre[s:State] {
   	some p : degois.s, w : orcid.s  | 
		p.ids = DOI && no p.putcode.s && p.title = Title1 && p.year = Year1 && p.type = Conference && p.key = Id1 &&
		w. ids = DOI && w.title = Title1 && Year1 = w.year && w.source = User && w.type = Conference && w.putcode.s = Id3 
	one degois.s
	one orcid.s
   	no pending.s
}

run E7a_pre {
	some s : State | consistent[s] && E7a_pre[s]
} for 5 but 1 State

// Cenário E7a: quebra os identificadores
pred E7b[s:State] {
   	some p : degois.s, w : orcid.s  | 
		p.ids = ISBN && no p.putcode.s && p.title = Title2 && p.year = Year2 && p.type = Conference && p.key = Id1 &&
		w. ids = DOI && w.title = Title1 && Year1 = w.year && w.source = User && w.type = Conference && w.putcode.s = Id3 
	one degois.s
	one orcid.s
   	no pending.s
}

run E7b {
	some s : State, s' : s.next | not consistent[s] && E7b[s] and sync[s,s']
} for 5 but 2 State

// Cenário E7c: mantem alguns identificadores
pred E7c[s:State] {
   	some p : degois.s, w : orcid.s | 
		p.ids = DOI && no p.putcode.s && p.title = Title1 && p.year = Year1 && p.type = Conference && p.key = Id1 &&
		w. ids = DOI+ISBN && w.title = Title1 && Year1 = w.year && w.source = User && w.type = Conference && w.putcode.s = Id3 
	one degois.s
	one orcid.s
   	no pending.s
}

run E7c {
	some s : State, s' : s.next | not  consistent[s] && E7c[s] and sync[s,s']
} for 5 but 2 State



pred E7c_pre[s:State] {
   	some p : degois.s, w : orcid.s | 
		p.ids = DOI+ISBN && no p.putcode.s && p.title = Title1 && p.year = Year1 && p.type = Conference && p.key = Id1 &&
		w. ids = DOI+ISBN && w.title = Title1 && Year1 = w.year && w.source = User && w.type = Conference && w.putcode.s = Id3 
	one degois.s
	one orcid.s
   	no pending.s
}

run E7c_pre {
	some s : State | consistent[s] && E7c_pre[s]
} for 5 but 1 State

// Cenários E8: remoção de produções DeGois

// Cenários E9: remoção de trabalhos ORCID

pred E9b[s:State] {
   	some p : pending.s | 
		p.ids = DOI && no p.putcode.s && p.title = Title2 && p.year = Year2 && p.type = Conference
	no degois.s
	no orcid.s
   	one pending.s
}

run E9b {
	some s : State, s' : s.next | not consistent[s] && E9b[s] and sync[s,s']
} for 5 but 2 State

pred E9b_pre[s:State] {
   	some w : orcid.s | 
		W2_1Id_Pref_Select[s,w]	

	no degois.s
	one orcid.s
   	one pending.s
}

run E9b_pre {
	some s : State | consistent[s] && E9b_pre[s]
} for 5 but 1 State

pred E9c[s:State] {
   	some p : degois.s, w : orcid.s  | 
		p.ids = DOI+ISBN && no p.putcode.s && p.title = Title2 && p.year = Year2 && p.type = Conference && p.key = Id1 &&
		w. ids = DOI && w.title = Title1 && Year1 = w.year && w.source = User && w.type = Conference
	one degois.s
	one orcid.s
   	no pending.s
}

run E9c {
	some s : State, s' : s.next |  consistent[s] && E9c[s] and sync[s,s']
} for 5 but 2 State

pred E9c_pre[s:State] {
   	some disj w,w' : orcid.s, p:degois.s | 
		W1_1Id_Pref_Select[s,w]	&& W1_1Id_NoPref[s,w']	&& P2_2id[s,p]

	one degois.s
	# orcid.s = 2
   	no pending.s
}

run E9c_pre {
	some s : State | consistent[s] && E9c_pre[s]
} for 5 but 1 State

pred E9d[s:State] {
   	some p : pending.s, w : orcid.s | 
		p.ids = DOI+EID && no p.putcode.s && p.title = Title1 && no p.year && p.type = Conference &&
		W2_1Id_NoPref_Select[s,w]	
	no degois.s
	one orcid.s
   	one pending.s
}

run E9d {
	some s : State, s' : s.next | not consistent[s] && E9d[s] and sync[s,s']
} for 5 but 2 State


pred E9d_pre[s:State] {
   	some disj w,w' : orcid.s | 
		W1_2Id_Pref_Select[s,w]	&& W2_1Id_NoPref[s,w']

	no degois.s
	# orcid.s = 2
   	one pending.s
}

run E9d_pre {
	some s : State | consistent[s] && E9d_pre[s]
} for 5 but 1 State


pred E9e[s:State] {
   	some p : degois.s, p' : pending.s  | 
		p.ids = DOI && no p.putcode.s && p.title = Title2 && p.year = Year2 && p.type = Conference && p.key = Id1 &&
		p'.key = p.key && p'.ids = DOI+EID
	one degois.s
	no orcid.s
   	one pending.s
}

run E9e {
	some s : State, s' : s.next | not consistent[s] && E9e[s] and sync[s,s']
} for 5 but 2 State


pred E9e_pre[s:State] {
   	some disj w : orcid.s, p:degois.s | 
		P2_1id[s,p] && W2_2Id_Pref_Select[s,w]

	one degois.s
	one orcid.s
   	one pending.s
}

run E9e_pre {
	some s : State | consistent[s] && E9e_pre[s]
} for 5 but 1 State



// Cenários E10: produções importadas para o DeGois

pred E10a[s:State] {
   	some p : degois.s, w: orcid.s | 
		p.ids = DOI  && p.title = Title2 && p.year = Year2 && p.type = Conference && p.key = Id1 &&
		equal[p,w] && w.putcode.s = p.putcode.s && w.source = DeGois
	one degois.s
	one orcid.s
   	no pending.s
}

run E10a {
	some s : State, s' : s.next | consistent[s] && E10a[s] and sync[s,s']
} for 5 but 2 State

pred E10a_pre[s:State] {
   	some p : degois.s |  
		P2_1id[s,p]
	one degois.s
	no orcid.s
   	no pending.s
}

run E10a_pre {
	some s : State | consistent[s] && E10a_pre[s]
} for 5 but 1 State

pred E10b[s:State] {
   	some p : degois.s, disj w,w': orcid.s | 
		p.ids = DOI+ISBN  && p.title = Title2 && p.year = Year2 && p.type = Conference && p.key = Id1 &&
		equal[p,w] && w.putcode.s = p.putcode.s && w.source = DeGois &&
		w'.source = User && w'.putcode.s = Id1 && w'.ids = DOI
	one degois.s
	# orcid.s = 2
   	no pending.s
}

run E10b {
	some s : State, s' : s.next |  consistent[s] && E10b[s] and sync[s,s']
} for 5 but 2 State

pred E10b_pre[s:State] {
   	some p : degois.s, w: orcid.s |  
		P2_2id[s,p] && W1_1Id_NoPref_Select[s,w]
	one degois.s
	one orcid.s
   	no pending.s
}

run E10b_pre {
	some s : State | consistent[s] && E10b_pre[s]
} for 5 but 1 State

pred E10c[s:State] {
   	some p : degois.s, disj w,w': orcid.s | 
		p.ids = DOI+ISBN  && p.title = Title2 && p.year = Year2 && p.type = Conference && p.key = Id1 &&
		equal[p,w] && w.source = DeGois && w.putcode.s = Id1 && w in selected.s && w in s.preferred &&
		equal[p,w'] && w'.putcode.s = p.putcode.s && w'.source = DeGois 
	one degois.s
	# orcid.s = 2
   	no pending.s
}

run E10c {
	some s : State, s' : s.next | not consistent[s] && E10c[s] and sync[s,s']
} for 5 but 2 State


pred E10c_pre[s:State] {
  some p : degois.s, w: orcid.s |  
		P2_2id_Sync[s,p] && W2_2Id_Sync_Select[s,w]
	one degois.s
	one orcid.s
   	no pending.s
}

run E10c_pre {
	some s : State | consistent[s] && E10c_pre[s]
} for 5 but 1 State

pred E10d[s:State] {
   	some p : degois.s, disj w': orcid.s | 
		p.ids = DOI+ISBN  && p.title = Title2 && p.year = Year2 && p.type = Conference && p.key = Id1 &&
		equal[p,w'] && w'.putcode.s = p.putcode.s && w'.source = DeGois && p.putcode.s = Id3
	one degois.s
	one orcid.s
   	no pending.s
}

run E10d {
	some s : State, s' : s.next |  consistent[s] && E10d[s] and sync[s,s']
} for 5 but 2 State


pred E10e[s:State] {
   	some w,w': orcid.s, p :degois.s | 
		P1_0Id_Sync[s,p] && W1_0Id_Sync[s,w] && W1_0Id_Sync[s,w'] && w.putcode.s = Id1 && w'.putcode.s = Id2 && p.putcode.s = Id2

	one degois.s
	# orcid.s = 2
   	no pending.s
}

run E10e {
	some s : State, s' : s.next | not consistent[s] && E10e[s] and sync[s,s']
} for 5 but 2 State

pred E10e_pre[s:State] {
   	some w: orcid.s, p :degois.s | 
		P1_0Id_Sync[s,p] && W1_0Id_Sync[s,w] && w.putcode.s = Id1

	one degois.s
	one orcid.s
   	no pending.s
}

run E10e_pre {
	some s : State | consistent[s] && E10e_pre[s]
} for 5 but 1 State

pred E10f[s:State] {
   	some w,w': orcid.s, p :degois.s | 
		P1_0Id_Sync[s,p] && W1_0Id_Pref_Select[s,w] && W1_0Id_Sync[s,w'] && w.putcode.s = Id1 && w'.putcode.s = Id2 && p.putcode.s = Id2

	one degois.s
	# orcid.s = 2
   	no pending.s
}

run E10f {
	some s : State, s' : s.next | not consistent[s] && E10f[s] and sync[s,s']
} for 5 but 2 State


// Cenários E11: trabalhos adicionados após importação

pred E11a[s:State] {
   	some p : degois.s, w,w': orcid.s | 
		p.ids = DOI+ISBN  && p.title = Title2 && p.year = Year2 && p.type = Conference && p.key = Id1 &&
		equal[p,w] && w.putcode.s = p.putcode.s && w.source = DeGois && w.putcode.s = Id1 &&
		w'.ids = DOI && w'.title = Title1 && w'.type = Conference && no w'.year && w'.source = User && w' not in selected.s
	one degois.s
	# orcid.s = 2
   	no pending.s
}

run E11a {
	some s : State, s' : s.next | consistent[s] && E11a[s] and sync[s,s']
} for 5 but 2 State
	
pred E11b[s:State] {
   	some p : degois.s, w,w': orcid.s | 
		p.ids = DOI+ISBN  && p.title = Title2 && p.year = Year2 && p.type = Conference && p.key = Id1 &&
		equal[p,w] && w.putcode.s = p.putcode.s && w.source = DeGois && w.putcode.s = Id1 &&
		w'.ids = DOI && w'.title = Title1 && w'.type = Conference && no w'.year && w'.source = User && w'  in selected.s
	one degois.s
	# orcid.s = 2
   	no pending.s
}

run E11b {
	some s : State, s' : s.next | consistent[s] && E11b[s] and sync[s,s']
} for 5 but 2 State


pred E11c[s:State] {
   	some p : degois.s, w,w': orcid.s | 
		p.ids = DOI+ISBN  && p.title = Title2 && p.year = Year2 && p.type = Conference && p.key = Id1 &&
		equal[p,w] && w.putcode.s = p.putcode.s && w.source = DeGois && w.putcode.s = Id1 &&
		w'.ids = DOI && w'.title = Title1 && w'.type = Conference && no w'.year && w'.source = Scopus && w'  in selected.s
	one degois.s
	# orcid.s = 2
   	no pending.s
}

run E11c {
	some s : State, s' : s.next | consistent[s] && E11c[s] and sync[s,s']
} for 5 but 2 State
	
pred E11d[s:State] {
   	some p : degois.s, w,w': orcid.s | 
		p.ids = DOI+ISBN  && p.title = Title2 && p.year = Year2 && p.type = Conference && p.key = Id1 &&
		equal[p,w] && w.putcode.s = p.putcode.s && w.source = DeGois && w.putcode.s = Id1 && w.ids = DOI+ISBN &&
		w'.ids = DOI+EID && w'.title = Title1 && w'.type = Conference && no w'.year && w'.source = Scopus && w'  in selected.s
	one degois.s
	# orcid.s = 2
   	no pending.s
}

run E11d {
	some s : State, s' : s.next | not consistent[s] && E11d[s] and sync[s,s']
} for 5 but 2 State


// Cenários E12: atualização após importação
// Cenário E12a: mantem os identificadores
pred E12a[s:State] {
   	some p : degois.s, w : orcid.s  | 
		p.ids = DOI && p.putcode.s = w.putcode.s && p.title = Title2 && p.year = Year2 && p.type = Conference && p.key = Id1 &&
		w. ids = DOI && w.title = Title1 && Year1 = w.year && w.source = DeGois && w.type = Conference
	one degois.s
	one orcid.s
   	no pending.s
}

pred E12a_pre[s:State] {
  some p : degois.s, w: orcid.s |  
		P1_1id_Sync[s,p] && W1_1Id_Sync_Select[s,w] && w.putcode.s = Id3
	one degois.s
	one orcid.s
   	no pending.s
}

run E12a_pre {
	some s : State | consistent[s] && E12a_pre[s]
} for 5 but 1 State



// Cenário E12b: nao mantem os identificadores
pred E12b[s:State] {
   	some p : degois.s, w : orcid.s  | 
		p.ids = ISBN && p.putcode.s = w.putcode.s && p.title = Title2 && p.year = Year2 && p.type = Conference && p.key = Id1 &&
		w. ids = DOI && w.title = Title1 && Year1 = w.year && w.source = DeGois && w.type = Conference
	one degois.s
	one orcid.s
   	no pending.s
}

run E12b {
	some s : State, s' : s.next | not consistent[s] && E12b[s] and sync[s,s']
} for 5 but 2 State

// Cenário E12c: remove os identificadores
pred E12c[s:State] {
   	some p : degois.s, w : orcid.s  | 
		p.ids = none && p.putcode.s = w.putcode.s && p.title = Title2 && p.year = Year2 && p.type = Conference && p.key = Id1 &&
		w. ids = DOI && w.title = Title1 && Year1 = w.year && w.source = DeGois && w.type = Conference
	one degois.s
	one orcid.s
   	no pending.s
}

run E12c {
	some s : State, s' : s.next | not consistent[s] && E12c[s] and sync[s,s']
} for 5 but 2 State


pred E12d[s:State] {
   	some p : degois.s, w,w' : orcid.s  | 
		p.ids = EID+DOI && p.putcode.s = w.putcode.s && p.title = Title2 && p.year = Year2 && p.type = Conference && p.key = Id1 &&
		w. ids = DOI && w.title = Title1 && Year1 = w.year && w.source = DeGois && w.type = Conference &&
		w'.ids = EID+DOI && w'.source = Scopus && w' in selected.s
	one degois.s
	# orcid.s = 2
   	no pending.s
}

run E12d {
	some s : State, s' : s.next | not consistent[s] && E12d[s] and sync[s,s']
} for 5 but 2 State

pred E12d_pre[s:State] {
  some p : degois.s, w,w': orcid.s |  
		P1_1id_Sync[s,p] && W1_1Id_Sync[s,w] && W1_2Id_Pref_Select[s,w'] && w.putcode.s = Id2
	one degois.s
	# orcid.s = 2
   	one pending.s
}

run E12d_pre {
	some s : State | consistent[s] && E12d_pre[s]
} for 5 but 1 State

pred E12e[s:State] {
   	some p : degois.s, w,w' : orcid.s  | 
		p.ids = EID+DOI && p.putcode.s = w.putcode.s && p.title = Title2 && p.year = Year2 && p.type = Conference && p.key = Id1 &&
		w. ids = DOI && w.title = Title1 && Year1 = w.year && w.source = DeGois && w.type = Conference &&
		w'.ids = EID+DOI && w'.source = User && w' not in selected.s
	one degois.s
	# orcid.s = 2
   	no pending.s
}

run E12e {
	some s : State, s' : s.next | not consistent[s] && E12e[s] and sync[s,s']
} for 5 but 2 State

pred E12e_pre[s:State] {
  some p : degois.s, w,w': orcid.s |  
		P1_1id_Sync[s,p] && W1_1Id_Sync_Select[s,w] && W1_2Id_NoPref[s,w'] && w.putcode.s = Id2 && w'.putcode.s = Id1
	one degois.s
	# orcid.s = 2
   	one pending.s
}

run E12e_pre {
	some s : State | consistent[s] && E12e_pre[s]
} for 5 but 1 State


// Cenários E13: produções removidas após importação

pred E13a[s:State] {
   	some w: orcid.s | 
		w.ids = DOI && w.title = Title1 && w.type = Conference && no w.year && w.source = DeGois
	no degois.s
	one orcid.s
   	no pending.s
}

run E13a {
	some s : State, s' : s.next | not consistent[s] && E13a[s] and sync[s,s']
} for 5 but 2 State

pred E13a_pre[s:State] {
   	some w: orcid.s, p: degois.s | 
		w.ids = DOI && w.title = Title1 && w.type = Conference && no w.year && w.source = DeGois &&
		p.ids = DOI && p.title = Title1 && p.putcode.s = w.putcode.s

	one degois.s
	one orcid.s 
   	no pending.s
}

run E13a_pre {
	some s : State | consistent[s] && E13a_pre[s]
} for 5 but 1 State

pred E13b[s:State] {
   	some w,w': orcid.s | 
		w.ids = DOI && w.title = Title1 && w.type = Conference && no w.year && w.source = DeGois && w not in selected.s &&
		w'.ids = DOI && w'.title = Title1 && w'.type = Conference && w'.year = Year1 && w'.source = User 
	no degois.s
	# orcid.s = 2
   	no pending.s
}

run E13b {
	some s : State, s' : s.next | not consistent[s] && E13b[s] and sync[s,s']
} for 5 but 2 State

pred E13b_pre[s:State] {
   	some disj w,w': orcid.s, p: degois.s | 
		w.ids = DOI && w.title = Title1 && w.type = Conference && no w.year && w.source = DeGois && w not in selected.s && w.putcode.s = Id3 &&
		w'.ids = DOI && w'.title = Title1 && w'.type = Conference && w'.year = Year1 && w'.source = User && w'.putcode.s = Id2 &&
		p.ids = DOI && p.title = Title1 && p.putcode.s = w.putcode.s

	one degois.s
	# orcid.s = 2
   	no pending.s
}

run E13b_pre {
	some s : State | consistent[s] && E13b_pre[s]
} for 5 but 1 State

pred E13c[s:State] {
   	some w,w': orcid.s | 
		w.ids = DOI && w.title = Title1 && w.type = Conference && no w.year && w.source = DeGois && w in selected.s &&
		w'.ids = DOI && w'.title = Title1 && w'.type = Conference && w'.year = Year1 && w'.source = User 
	no degois.s
	# orcid.s = 2
   	no pending.s
}

run E13c {
	some s : State, s' : s.next | not consistent[s] && E13c[s] and sync[s,s']
} for 5 but 2 State

pred E13c_pre[s:State] {
   	some disj w,w': orcid.s, p: degois.s | 
		w.ids = DOI && w.title = Title1 && w.type = Conference && no w.year && w.source = DeGois && w in selected.s && w.putcode.s = Id3 &&
		w'.ids = DOI && w'.title = Title1 && w'.type = Conference && w'.year = Year1 && w'.source = User && w'.putcode.s = Id2 &&
		p.ids = DOI && p.title = Title1 && p.putcode.s = w.putcode.s

	one degois.s
	# orcid.s = 2
   	no pending.s
}

run E13c_pre {
	some s : State | consistent[s] && E13c_pre[s]
} for 5 but 1 State

// Scenarios E14: work removal after imports
// Scenario E14a: no equivalent work remaining
pred E14a[s:State] {
   	some p : degois.s | 
		p.ids = DOI+EID && p.title = Title2 && p.year = Year2 && p.type = Conference && p.key = Id1 && p.putcode.s = Id2

	one degois.s
	no orcid.s
   	no pending.s
}

run E14a {
	some s : State, s' : s.next | not consistent[s] && E14a[s] and sync[s,s']
} for 5 but 2 State

pred E14a_pre[s:State] {
   	some p : degois.s, w:orcid.s | 
		p.ids = DOI+EID && p.title = Title2 && p.year = Year2 && p.type = Conference && p.key = Id1 && p.putcode.s = Id2 &&
		w.source = DeGois && w.putcode.s = p.putcode.s

	one degois.s
	one orcid.s
   	no pending.s
}

run E14a_pre {
	some s : State | consistent[s] && E14a_pre[s]
} for 5 but 1 State

// Scenario E14b: no equivalent work remaining with same ids
pred E14b[s:State] {
   	some p : degois.s, w : orcid.s | 
		p.ids = DOI+EID && p.title = Title2 && p.year = Year2 && p.type = Conference && p.key = Id1 && p.putcode.s = Id2 &&
		w.ids = DOI+EID && w.source = User && w.title = Title2 && w.year = Year2 && w.type = Conference && w.putcode.s = Id3

	one degois.s
	one orcid.s
   	no pending.s
}

run E14b {
	some s : State, s' : s.next | not consistent[s] && E14b[s] and sync[s,s']
} for 5 but 2 State

pred E14b_pre[s:State] {
   	some p : degois.s, disj w,w' : orcid.s | 
		p.ids = DOI+EID && p.title = Title2 && p.year = Year2 && p.type = Conference && p.key = Id1 && p.putcode.s = Id2 &&
		w.ids = DOI+EID && w.source = User && w.title = Title2 && w.year = Year2 && w.type = Conference && w.putcode.s = Id3 &&
		w'.source = DeGois && w'.putcode.s = p.putcode.s

	one degois.s
	# orcid.s = 2
   	no pending.s
}

run E14b_pre {
	some s : State | consistent[s] && E14b_pre[s]
} for 5 but 1 State

// Scenario E14b: no equivalent work remaining with some ids
pred E14c[s:State] {
   	some p : degois.s, w : orcid.s | 
		p.ids = DOI+EID && p.title = Title2 && p.year = Year2 && p.type = Conference && p.key = Id1 && p.putcode.s = Id2 &&
		w.ids = DOI && w.source = User && w.title = Title2 && w.year = Year2 && w.type = Conference && w.putcode.s = Id3

	one degois.s
	one orcid.s
   	no pending.s
}

run E14c {
	some s : State, s' : s.next | not consistent[s] && E14c[s] and sync[s,s']
} for 5 but 2 State

pred E14c_pre[s:State] {
   	some p : degois.s, disj w,w' : orcid.s | 
		p.ids = DOI+EID && p.title = Title2 && p.year = Year2 && p.type = Conference && p.key = Id1 && p.putcode.s = Id2 &&
		w.ids = DOI && w.source = User && w.title = Title2 && w.year = Year2 && w.type = Conference && w.putcode.s = Id3 &&
		w'.source = DeGois && w'.putcode.s = p.putcode.s

	one degois.s
	# orcid.s = 2
   	no pending.s
}

run E14c_pre {
	some s : State | consistent[s] && E14c_pre[s]
} for 5 but 1 State


// Cenários E15: produções equivalentes


pred E15a[s:State] {
   	some disj p,p' : degois.s, disj w : orcid.s, e : pending.s | 
		P1_1id[s,p] && P2_1id[s,p'] && W1_2Id_Pref_Select[s,w] && e.ids = w.ids && p.key = e.key
	# degois.s = 2
	one orcid.s
   	one pending.s
}

run E15a {
	some s : State, s' : s.next |  consistent[s] && E15a[s] && sync[s,s']
} for 5 but 2 State


pred E15a_pre[s:State] {
   	some disj p: degois.s, disj w : orcid.s, e : pending.s | 
		P1_1id[s,p]  && W1_2Id_Pref_Select[s,w]
	one degois.s 
	one orcid.s
   	one pending.s
}

run E15a_pre {
	some s : State | consistent[s] && E15a_pre[s]
} for 5 but 1 State

pred E15b[s:State] {
   	some w: orcid.s, p :degois.s | 
		w.ids = DOI && w.title = Title1 && w.type = Conference && no w.year && w.source = DeGois &&
		p.ids = DOI && no p.putcode.s && p.type = Conference && p.key = Id3
	one degois.s
	one orcid.s
   	no pending.s
}

run E15b {
	some s : State, s' : s.next | not consistent[s] && E15b[s] and sync[s,s']
} for 5 but 2 State

pred E15b_pre[s:State] {
   	some disj p',p : degois.s, w : orcid.s | 
		w.ids = DOI && w.title = Title1 && w.type = Conference && no w.year && w.source = DeGois &&
		p.ids = DOI && no p.putcode.s && p.type = Conference && p.key = Id3 &&
		p'.ids = DOI && p'.putcode.s = w.putcode.s

	# degois.s = 2
	one orcid.s
   	no pending.s
}

run E15b_pre {
	some s : State | consistent[s] && E15b_pre[s]
} for 5 but 1 State


pred E15c[s:State] {
   	some disj p,p' : degois.s, disj w,w' : orcid.s | 
		P1_2id[s,p] && P1_1id_Sync[s,p'] && W1_1Id_Sync[s,w]  &&  W1_2Id_Pref_Select[s,w']  && p'.putcode.s = w.putcode.s
	# degois.s = 2
	# orcid.s = 2
   	no pending.s
}

run E15c {
	some s : State, s' : s.next |  consistent[s] && E15c[s] and sync[s,s']
} for 5 but 2 State


pred E15c_pre[s:State] {
   	some disj p,p' : degois.s, disj w: orcid.s | 
		P1_2id[s,p] && P1_1id_Sync[s,p'] && W1_1Id_Sync_Select[s,w]   && p'.putcode.s = w.putcode.s
	one orcid.s
	no pending.s
	# degois.s = 2
}

run E15c_pre {
	some s : State | consistent[s] && E15c_pre[s]
} for 5 but 1 State


/*
pred E26a[s:State] {
	some disj w,w':orcid.s,p:degois.s | w'.title = p.title && w'.type = p.type && w'.year = p.year && p.ids = w'.ids && some p.year && same[w,p] && w in preferred.s && DeGois in w'.source &&
			w.source not in DeGois && same[w,w'] && one w.ids && p.type = Conference && w.source = User && w.putcode.s = Id2 && some w.year &&
		p.ids = DOI && p.key = Id0
    one degois.s
	# orcid.s = 2
	no pending.s
}

run E26a {
	some s : State, s' : s.next |   consistent[s] and E26a[s] and sync[s,s']
} for 5 but 2 State, 1 Year, 1 Title


pred E26_pre[s:State] {
	some disj w:orcid.s,p:degois.s | same[w,p] && w in preferred.s && 
			w.source not in DeGois && one w.ids && p.ids = DOI && p.key = Id0 && some p.year && p.type = Conference &&
			w.ids = DOI && w.putcode.s = Id2
    one degois.s
	one orcid.s
	no pending.s
}

run E26_pre {
	some s : State |   consistent[s] and E26_pre[s]
} for 4 but 1 State, 1 Title



pred E30a[s:State] {
   	some disj w:orcid.s, disj p,p': degois.s | same[p,p']  && same[p,w] && DeGois not in w.source
    #degois.s = 2
	one orcid.s
	no pending.s
}

run E30a {
	some s : State, s' : s.next |  not consistent[s] and E30a[s] and sync[s,s']
} for 5 but 2 State


pred E40a[s:State] {
	some disj w,w',w'' : orcid.s, p : degois.s |
		w.source = DeGois && w''.source = DeGois && equal[s,s,w'',p] && same[w,w'] && same[w',w''] && 
		w in preferred.s and w'.source != DeGois

    #degois.s = 1
	#orcid.s = 3
	no pending.s
}

run E50a {
	some s : State, s' : s.next |  not consistent[s] and E40a[s] and sync[s,s']
} for 4 but 2 State
*/

//E23: apagar grupo inteiro
// importa
// importar DeGois para ORCID quando tinha equivalente
// putcode de DeGois igual a putcode de ORCID não Degois: pode acontecer?


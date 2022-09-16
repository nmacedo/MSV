/*
 * A formalization of a an ORCID-based synchronization framework 
 * for PTCRIS, as described in https://github.com/fccn/PTCRISync/wiki.
 * 
 * author: A. Cunha, N. Macedo, 11/2014 
 */

open util/ordering[State]
open util/ordering[Id]

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

sig Title, Year {}

enum Type {Conference,Journal,Book}

// ORCID papers
sig Work extends Paper {
	orcid : set State,
	preferred : set State,
	source : one Source
}

sig Id {}

enum Source {User,Scopus,DeGois,Recaap}

fact Orcid {
    // preferred papers exist in the repository
	all s : State | preferred.s in orcid.s
	// only a single preferred by group
	all s : State, w : orcid.s | one y : preferred.s | y in w.*group

    // orcid does not change putcodes of entries
    all i : Id | lone (putcode.State.i & orcid.State)
	all w : orcid.State | one w.putcode.State
	all p : degois.State | lone p.putcode.State
//	all s : State, w : orcid.s | one w.putcode.s

    // every paper has a putcode assigned
	all s : State, w : orcid.s | one w.putcode.s
}

// DeGois papers
sig Production extends Paper {
	key : one Id,
	degois : set State,
	pending : set State
}

fact DeGois {
    // no paper is pending and accepted as a production in a DeGois repository
	all s : State | no pending.s & degois.s
	// keys are unique for pending and accepted papers
	all s : State | all i : Id | lone key.i & (degois.s + pending.s)
    // ORCID works appear at most once in a DeGois repository
	all s : State | all i : Id | lone putcode.s.i & (pending.s)
	all s : State | all i : Id | lone putcode.s.i & (degois.s)
    // a pending paper has no equivalent paper accepted or an equivalent pending
	all s : State | all p : pending.s, p' : degois.s+pending.s | same_production[s,p,p'] implies p=p'
}

pred equal [s,s':State,p,p' : Paper] {
	p.title = p'.title and p.ids = p'.ids and p.type = p'.type and p.year = p'.year and p.putcode.s = p'.putcode.s'
}

fun equal_within : State -> Paper -> Paper {
  {s:State,x,y : Paper |  x->y in equal[s,s] }
}

fun equal[s,s':State] : Paper -> Paper {
	{x,y : Paper | x!=y and equal[s,s',x,y]}
}

// Quando é que um registo é preferível a outro? Convem ser uma ordem reflexiva.
// Para já uso o putcode mais baixo para desempatar quando não há um preferred claro.
pred preferred[s : State, w,w' : Work] {
	(w in preferred.s and w' not in preferred.s) or 
	(w in preferred.s and w' in preferred.s and lte[w.putcode.s,w'.putcode.s]) or 
	(w not in preferred.s and w' not in preferred.s and lte[w.putcode.s,w'.putcode.s])
}

fun select : State -> set Work {
     {s:State, x : Work |  no w : orcid.s-x | preferred[s,w,x] }
}

// Noção de grupo do ORCID 
pred same_group [w,w' : Work] {
	some w.ids & w'.ids
}

// Noção de grupo do ORCID 
fun group : Work -> Work {
	{ x,y : Work | same_group [x,y] } - iden
}

// Noção de equivalência entre artigos
// Que deve ser considerado o mesmo na sincronização?
pred same [p,p' : Paper] {
	some p.ids & p'.ids or (p.title = p'.title and p.type = p'.type)
}

// Noção de equivalência entre artigos
fun same : Paper -> Paper {
	{x,y : Paper | x!=y and same[x,y]}
}

// Artigos equivalentes no repositório ORCID
fun same_work [s : State] : Work -> Work {
	*{x,y : orcid.s | same[x,y]} & Work -> Work
}

// Artigos equivalentes no repositório DeGois
fun same_production [s : State] : Production -> Production {
	*{x,y : degois.s+pending.s | same[x,y]} &  Production -> Production 
}

// Artigos equivalentes no repositório ORCID
pred same_work [s : State, w,w' : Work] {
	w->w' in same_work[s]
}

// Artigos equivalentes no repositório DeGois
pred same_production [s : State, p,p' : Production] {
	p->p' in same_production[s]
}

pred consistent [s : State] {
	// todos os artigos no repositório ORCID do DeGois têm uma entrada idêntica no DeGois com um putcode associado
	all w : orcid.s & source.DeGois | some p : degois.s & putcode.s.Id | equal[s,s,w,p] 
	// para quê aquele filtro do putcode se o "equal" também testa isso?
	
	// todos os artigos no repositório DeGois com um putcode associado têm uma entrada idêntica no ORCID do DeGois
	all p : degois.s & putcode.s.Id | some w : orcid.s & source.DeGois | equal[s,s,w,p]

	// todas as entradas no ORCID, o seu respectivo preferred existe semelhante no repositório DeGois, ou a sugestão exata
	all w : orcid.s | some w' : orcid.s | same_work[s,w,w'] and preferred[s,w',w] and ((some p : degois.s | same[w',p]) or (some p : pending.s | equal[s,s,w',p])) 
	
	// todos os pendings no DeGois, existe uma entrada idêntica no ORCID que tem que ser a preferred de entre os semelhantes
	all p : pending.s | some w : orcid.s | equal[s,s,p,w] and no w' : orcid.s | w' != w and same_work[s,w,w'] and preferred[s,w',w]
}

run { some s : State | consistent[s] and interessante[s]} for 6 but exactly 1 State

check {
	all s : State | consistent[s] implies
		all p : pending.s | no w : orcid.s & source.DeGois | same[p,w]
} for 5 but 1 State

pred interessante[s : State] {
	some preferred.s
//	some pending.s
	some degois.s
	some orcid.s & source.DeGois
	some orcid.s & source.(Source-DeGois)
	no w : orcid.s | no w' : orcid.s-w | same[w,w']
	no w : orcid.s | some w' : orcid.s-w | DeGois in w.source&w'.source
	some p:degois.s,w:orcid.s | p.putcode.s = w.putcode.s
    #(preferred.s) > 1
	#(group & orcid.s -> orcid.s) > 1

}

run { some s : State | not consistent[s] and interessante[s] } for 5 but exactly 1 State

pred sync[s,s' : State] {
	// Não altera works de outras sources
	orcid.s' & source.(Source-DeGois) = orcid.s & source.(Source-DeGois)
	preferred.s' & source.(Source-DeGois) =preferred.s & source.(Source-DeGois)

	// As productions no degois não se alteram (mas podem deixar de estar no orcid)
	(degois.s').key = (degois.s).key
	all p : degois.s | some p' : degois.s' | p.key = p'.key and p.title = p'.title and p.ids = p'.ids and p.type = p'.type and p.year = p'.year

	// Só ficam no orcid works com source degois cujo putcode existe no degois: apaga os que já não estão
	// no degois e altera os restantes para ficarem iguais

//	all w' : orcid.s' | (some w : orcid.s, p : degois.s | same[p,w'] && w.putcode.s = p.putcode.s) or (some x : degois.s' | x.putcode.s' = w'.putcode.s')
	all p : degois.s | (some w : orcid.s | w.putcode.s = p.putcode.s) implies (some p' : degois.s' | some p'.putcode.s' && /*p'.putcode.s' = p.putcode.s and*/ p'.key = p.key)
	all p : degois.s' | some p.putcode.s' implies some w : orcid.s, p' : degois.s | w.putcode.s = p'.putcode.s /*and p'.putcode.s = p.putcode.s'*/ and p'.key = p.key
	consistent[s']
}

run test0 {
	some s : State, s' : s.next | not consistent[s] and interessante[s] and no pending.s and some (degois.s).putcode and sync[s,s'] and some pending.s'
} for 7 but 2 State

run test1 {
	some s : State, s' : s.next, w : orcid.s, p : degois.s {
		w.putcode = p.putcode
		w.title != p.title
		sync[s,s']
	}
} for 3 but 2 State

pred same_state[s,s' : State] {
	all w : orcid.s | some w' : orcid.s' | equal[s,s',w,w']
	all w : orcid.s' | some w' : orcid.s | equal[s',s,w,w']
	all p : degois.s | some p' : degois.s' | p.key = p'.key and equal[s,s',p,p']
	all p : degois.s' | some p' : degois.s | p.key = p'.key and equal[s',s,p,p']
	all p : pending.s | some p' : pending.s' | equal[s,s',p,p']
	all p : pending.s' | some p' : pending.s | equal[s',s,p,p']	
}

check hippocratic {
	all s : State, s' : s.next | consistent[s] and sync[s,s'] implies same_state[s,s']
} for 6 but 2 State

check deterministic {
	all s : State, s' : s.next, s'' : s.next.next | not consistent[s] and sync[s,s'] and sync[s,s''] implies same_state[s',s'']
} for 3 but 3 State



// nova entrada no ORCID com identificador único sem equivalente prévio no DeGois
pred E1a[s:State] {
   	one w : orcid.s | w.source = User && some w.ids
   	no degois.s
	no pending.s
}

run E1a {
	some s : State, s' : s.next | not consistent[s] and E1a[s] and sync[s,s']
} for 7 but 2 State


// nova entrada no ORCID sem equivalente prévio no DeGois
pred E1b[s:State] {
   	one w : orcid.s | w.source = User && no w.ids
   	no degois.s
    one orcid.s
	no pending.s
}

run E1b {
	some s : State, s' : s.next | not consistent[s] and E1b[s] and sync[s,s']
} for 7 but 2 State

pred E2a[s:State] {
   	one w : orcid.s, p : degois.s | w.source = User && same[w,p] && no p.putcode.s && no w.ids && 
			one p.ids && p.ids in DOI && Journal in p.type
	one degois.s
	one orcid.s
   	no pending.s
}

// nova entrada no ORCID com equivalente prévio no DeGois
run E2a {
	some s : State, s' : s.next | E2a[s] and sync[s,s']
} for 3 but 2 State, 1 Title, 1 Year, 1 DOI

pred E2_pre[s:State] {
   	one p : degois.s | no p.putcode.s &&  one p.ids && p.ids in DOI && Journal in p.type
	one degois.s
	no orcid.s
   	no pending.s
}

run E2_pre {
	some s : State | E2_pre[s]
} for 3 but 1 State, 1 Title, 1 Year, 1 DOI


pred E2b[s:State] {
   	one w : orcid.s, p : degois.s | w.source = User && same[w,p] && no p.putcode.s && some w.ids && 
			one p.ids && p.ids in DOI && Journal in p.type
	one degois.s
	one orcid.s
   	no pending.s
}

run E2b {
	some s : State, s' : s.next | consistent[s] && E2b[s] and sync[s,s']
} for 3 but 2 State

// nova entrada no DeGois 
pred E3a[s:State] {
   	one p : degois.s  | one p.ids && no p.putcode.s
	one degois.s
	no orcid.s
   	no pending.s
}

run E3a {
	some s : State, s' : s.next | consistent[s] && E3a[s] and sync[s,s']
} for 7 but 2 State


pred E3b[s:State] {
   	one p : degois.s, w : orcid.s | same[p,w] && User in w.source && no p.putcode.s && w.ids in DOI 
&&  Journal in w.type && some w.year
	one degois.s
	one orcid.s
   	no pending.s
}

run E3b {
	some s : State, s' : s.next |  consistent[s] && E3b[s] and sync[s,s']
} for 2 but 2 State, 1 Title, 1 Year, 1 DOI, 2 Id

pred E3_pre[s:State] {
   	one w : orcid.s | one w.ids && w.ids in DOI && Journal in w.type && User in w.source && some w.year
	no degois.s
	one orcid.s
   	no pending.s
}

run E3_pre {
	some s : State | E3_pre[s]
} for 2 but 1 State, 1 Title, 1 Year, 1 DOI, 2 Id

// atualiza entrada DeGois com equivalente no ORCID
pred E4a[s:State] {
   	one p : degois.s, w : orcid.s | same[p,w] && some p.putcode.s&w.putcode.s && DeGois in w.source && 
one p.ids && one w.ids && p.ids in DOI &&  w.ids in ISBN  && Journal in w.type
	one degois.s
	one orcid.s
   	no pending.s
}

run E4a {
	some s : State, s' : s.next | not consistent[s] && E4a[s] and sync[s,s']
} for 4 but 2 State

pred E4b[s:State] {
   	one p : degois.s, w : orcid.s | not same[p,w] && some p.putcode.s&w.putcode.s && DeGois in w.source && 
one p.ids && one w.ids && p.ids in DOI &&  w.ids in ISBN && Journal in w.type && no w.year
	one degois.s
	one orcid.s
   	no pending.s
}

run E4b {
	some s : State, s' : s.next | not consistent[s] && E4b[s] and sync[s,s']
} for 4 but 2 State, 1 ISBN, 1 Title

pred E4_pre[s:State] {
   	one p : degois.s, w : orcid.s | equal[s,s,p,w]  && DeGois in w.source && w.ids in ISBN && Journal in w.type && 
		no w.year && one w.ids && no w.year
	one degois.s
	one orcid.s
   	no pending.s
}

run E4_pre {
	some s : State | consistent[s] && E4_pre[s]
} for 2 but 1 State, 1 Title, 1 Year, 1 DOI, 2 Id

//
pred E5a[s:State] {
   	one p : degois.s, w : orcid.s | same[p,w] && no p.putcode.s && User in w.source && 
one p.ids && one w.ids && p.ids in DOI &&  w.ids in ISBN  && Journal in w.type && no w.year
	one degois.s
	one orcid.s
   	no pending.s
}

run E5a {
	some s : State, s' : s.next |  consistent[s] && E5a[s] and sync[s,s']
} for 3 but 2 State, exactly 2 ISBN


pred E5_pre[s:State] {
   	one p : degois.s, w : orcid.s | same[p,w]  && User in w.source && w.ids in ISBN && Journal in w.type && 
		no w.year && one w.ids && no w.year && no w.year
	one degois.s
	one orcid.s
   	no pending.s
}

run E5_pre {
	some s : State | consistent[s] && E5_pre[s]
} for 2 but 1 State, 1 Title, 1 Year, 2 ISBN, 2 Id

// atualização no degois quebra equivalencia
pred E6a[s:State] {
   	one p : degois.s, w : orcid.s | not same[p,w] && no p.putcode.s && User in w.source && 
one p.ids && one w.ids && p.ids in DOI &&  w.ids in ISBN  && Journal in w.type && no w.year
	one degois.s
	one orcid.s
   	no pending.s
}

run E6a {
	some s : State, s' : s.next | not consistent[s] && E6a[s] and sync[s,s']
} for 4 but 2 State, exactly 2 ISBN


// apagado no degois
pred E7a[s:State] {
   	one w : orcid.s | w.source = DeGois && w.ids in ISBN && Journal in w.type && one w.ids
   	no degois.s
	no pending.s
}

run E7a {
	some s : State, s' : s.next | not consistent[s] and E7a[s] and sync[s,s']
} for 1 but 2 State, 2 Id

pred E7b[s:State] {
   	one p : degois.s, w : orcid.s | same[p,w] &&  w.source = DeGois && w.ids in ISBN && 
		Journal in w.type && one w.ids && no p.putcode.s && no w.year
	one degois.s
	one orcid.s
   	no pending.s
}

run E7b {
	some s : State, s' : s.next | not consistent[s] && E7b[s] and sync[s,s']
} for 2 but 2 State, 2 Id, 1 Title

pred E7_pre[s:State] {
   	one disj p,p' : degois.s, w : orcid.s | same[p,w] &&  w.source = DeGois && w.ids in ISBN && 
		Journal in w.type && one w.ids && no p.putcode.s && no w.year && equal[s,s,p',w] && 
		p.ids in ISBN+EID && #(p.ids) = 2 && no p.year
	# degois.s = 2
	one orcid.s
   	no pending.s
}

run E7_pre {
	some s : State | consistent[s] && E7_pre[s]
} for 4 but 1 State, 1 ISBN, 1 Title, 2 Id, 1 EID

// apagado no orcid
pred E8a[s:State] {
   	one p : degois.s | some p.putcode.s && Conference in p.type && some p.year
   	one degois.s
	no orcid.s
	no pending.s
}

run E8a {
	some s : State, s' : s.next | not consistent[s] and E8a[s] and sync[s,s']
} for 1 but 2 State, 2 Id

pred E8_pre[s:State] {
   	one p : degois.s | some p.putcode.s && Conference in p.type && some p.year && no p.ids
   	one degois.s
	one orcid.s
	no pending.s
}

run E8_pre {
	some s : State | consistent[s] && E8_pre[s]
} for 4 but 1 State, 1 ISBN, 1 Title, 2 Id, 1 EID, 1 Year

// grupo de equivalência introduzido no orcid
pred E9a[s:State] {
   	some disj w,w' : orcid.s | same_group[w,w']  && w in preferred.s && DeGois not in w.source+w'.source
   	no degois.s
	no pending.s
}

run E9a {
	some s : State, s' : s.next | not consistent[s] and E9a[s] and sync[s,s']
} for 3 but 2 State


pred E9b[s:State] {
   	some disj w,w' : orcid.s | not same_group[w,w']  && w in preferred.s && DeGois not in w.source+w'.source && same[w,w']
   	no degois.s
	no pending.s
}

run E9b {
	some s : State, s' : s.next | not consistent[s] and E9b[s] and sync[s,s']
} for 3 but 2 State


// adicionado trabalho equivalente a entrada do degois, preferido ou não
pred E10a[s:State] {
   	some disj w,w' : orcid.s, p: degois.s | equal[s,s,w,p] && DeGois in w.source && w in preferred.s && DeGois not in w'.source && same_group[w,w']  && 
		Conference in p.type && p.ids in EID && one p.ids && no p.year && User in w'.source && Journal in w'.type && some w'.year
	#(orcid.s) = 2
    one degois.s
	no pending.s
}

run E10a {
	some s : State, s' : s.next |  consistent[s] and E10a[s] and sync[s,s']
} for 3 but 2 State, 4 Id

pred E10b[s:State] {
   	some disj w,w' : orcid.s, p: degois.s | equal[s,s,w,p] && DeGois in w.source && w' in preferred.s && DeGois not in w'.source && 
		not same_group[w,w'] && same[w,w'] && Conference in p.type && p.ids in EID && one p.ids && no p.year
	#(orcid.s) = 2
    one degois.s
	no pending.s
    no Work - orcid.State
}

run E10b {
	some s : State, s' : s.next |  consistent[s] and E10b[s] and sync[s,s']
} for 4 but 2 State, 1 EID


pred E10_pre[s:State] {
   	one p : degois.s, w : orcid.s | equal[s,s,w,p]  && Conference in p.type && p.ids in EID && one p.ids && no p.year
   	one degois.s
	one orcid.s
	no pending.s
}

run E10_pre {
	some s : State | consistent[s] && E10_pre[s]
} for 4 but 1 State, 1 ISBN, 1 Title, 4 Id, 1 EID, 1 Year

// adicionado trabalho não equivalente a entrada do degois, preferido ou não
pred E11a[s:State] {
   	some disj w,w' : orcid.s, p: degois.s | same[w,p] && not same[w',p] && same[w,w'] && DeGois not in w'.source && w' in s.select
	#(orcid.s) = 2
    one degois.s
	no pending.s
}

run E11a {
	some s : State, s' : s.next | not consistent[s] and E11a[s] and sync[s,s']
} for 4 but 2 State, 2 Id


pred E11b[s:State] {
   	some disj w,w' : orcid.s, p: degois.s | same[w,p] && not same[w',p] && same[w,w'] && DeGois not in w'.source && w not in preferred.s
	#(orcid.s) = 2
    one degois.s
	no pending.s
}

run E11b {
	some s : State, s' : s.next | not consistent[s] and E11b[s] and sync[s,s']
} for 4 but 2 State, 2 Id


// produção atualizada match com grupo quando o degois não era fav
pred E12a[s:State] {
   	some disj w,w' : orcid.s, p: degois.s | not equal[s,s,p,w] && p.putcode.s = w.putcode.s && DeGois in w.source && w' in preferred.s && 
		DeGois not in w'.source && same_group[w,w']   && some p.ids&w'.ids && one p.ids && same[p,w] && p.ids = w.ids && p.ids = w'.ids
	#(orcid.s) = 2
    one degois.s
	no pending.s
}

run E12a {
	some s : State, s' : s.next | not  consistent[s] and E12a[s] and sync[s,s']
} for 5 but 2 State, 3 Id, 1 Year, 1 ISBN, 1 EID, 1 DOI, 2 Title

pred E12_pre[s:State] {
  	some disj w,w' : orcid.s, p: degois.s | equal[s,s,p,w] && p.putcode.s = w.putcode.s && DeGois in w.source && w' in preferred.s && 
		DeGois not in w'.source && same_group[w,w']   && some p.ids&w'.ids && one p.ids && same[p,w] && p.ids in ISBN && 
		Book in p.type && p.ids = w.ids && p.ids = w'.ids && no w.year && User in w'.source && w'.putcode.s = p.key
	#(orcid.s) = 2
    one degois.s
	no pending.s
}

run E12_pre {
	some s : State | consistent[s] && E12_pre[s]
} for 4 but 1 State, 1 ISBN, exactly 2 Title, 3 Id, 0 EID, 0 DOI, 1 Year, 0 Int

pred E12b[s:State] {
   	some disj w,w' : orcid.s, p: degois.s | not equal[s,s,p,w] && p.putcode.s = w.putcode.s && DeGois in w.source && w' in preferred.s && 
		DeGois not in w'.source && same_group[w,w']   && no p.ids&w'.ids && one p.ids 
	#(orcid.s) = 2
    one degois.s
	no pending.s
}

run E12b {
	some s : State, s' : s.next | not  consistent[s] and E12b[s] and sync[s,s']
} for 5 but 2 State


// produção atualizada match com grupo quando o degois era fav; BUG, pref muda
pred E13a[s:State] {
   	some disj w,w' : orcid.s, p: degois.s | not equal[s,s,p,w] && same[p,w] && one w'.ids && one w.ids && one w'.putcode.s &&
	 p.putcode.s = w.putcode.s && DeGois in w.source && w in preferred.s && DeGois not in w'.source && same_group[w,w']   && one p.putcode.s &&
	p.type = w.type && p.title = w.title && p.year = w.year
	#(orcid.s) = 2
    one degois.s
	no pending.s
}

run E13a {
	some s : State, s' : s.next | not  consistent[s] and E13a[s] and sync[s,s']
} for 5 but 2 State, 1 Year, 1 Title, 1 ISBN, 1 DOI, 3 Id

one sig Id1,Id0,Id2 extends Id{}

pred E13_pre[s:State] {
   	some disj w,w' : orcid.s, p: degois.s | equal[s,s,p,w] && same[p,w] && one w'.ids && one w.ids && one w'.putcode.s && p.putcode.s = w.putcode.s && DeGois in w.source && 
		w in preferred.s && DeGois not in w'.source && same_group[w,w']   && one p.putcode.s && p.ids = EID && w.ids = EID && w'.ids = EID && no w.year && no w'.year &&
		Recaap in w'.source && p.putcode.s = Id1 && w'.putcode.s = Id0 && p.key = Id2
	#(orcid.s) = 2
    one degois.s
	no pending.s
}

run E13_pre {
	some s : State | consistent[s] && E13_pre[s]
} for 4 but 1 State, 1 ISBN, exactly 1 Title, 3 Id

//
pred E14a[s:State] {
   	some disj w,w' : orcid.s | same_group[w,w'] && DeGois in w.source && w' in preferred.s && one w.ids && one w'.ids && DeGois not in w'.source
	no degois.s
    #orcid.s = 2
	no pending.s
}

run E14a {
	some s : State, s' : s.next | not  consistent[s] and E14a[s] and sync[s,s']
} for 3 but 2 State, 1 Year, 1 Title, 1 ISBN, 1 DOI, 2 Id

pred E14_pre[s:State] {
   	some disj w,w' : orcid.s | same_group[w,w'] && DeGois in w.source && w'.putcode.s = Id2 && w.putcode.s = Id0 &&

		 w' in preferred.s && one w.ids && one w'.ids && DeGois not in w'.source && Recaap in w'.source && Book in w'.type && no w'.year
	one degois.s
    #orcid.s = 2
	no pending.s
}

run E14_pre {
	some s : State | consistent[s] && E14_pre[s]
} for 4 but 1 State, 1 ISBN, exactly 1 Title, 3 Id


//
pred E15a[s:State] {
   	some disj w,w' : orcid.s | same_group[w,w'] && DeGois in w.source && w in preferred.s && DeGois not in w'.source && one w.ids && one w'.ids
	no degois.s
    #orcid.s = 2
	no pending.s
}

run E15a {
	some s : State, s' : s.next | E15a[s] 
} for 2 but 2 State, 1 Year, 1 Title, 1 ISBN, 1 DOI, 3 Id


pred E15_pre[s:State] {
     	some disj w,w' : orcid.s | same_group[w,w'] && DeGois in w.source && w in preferred.s && DeGois not in w'.source && one w.ids && one w'.ids &&
			w.ids = DOI && w'.ids = DOI && w.putcode.s = Id2 && w'.putcode.s = Id1 && Recaap in w'.source && no w.year && no w'.year &&
			Book in w'.type && Journal in w.type
	one degois.s
    #orcid.s = 2
	no pending.s
}

run E15_pre {
	some s : State | consistent[s] && E15_pre[s]
} for 4 but 1 State, 1 ISBN, exactly 1 Title, 3 Id



//
pred E16a[s:State] {
   	some disj w : orcid.s, p: degois.s | some w.ids && some p.putcode.s && w.ids = p.ids && p.putcode.s != w.putcode.s && DeGois not in w.source
	one orcid.s
    one degois.s
	no pending.s
}

run E16a {
	some s : State, s' : s.next | not  consistent[s] and E16a[s] and sync[s,s']
} for 5 but 2 State, 1 Year, 1 Title, 1 ISBN, 1 DOI, 3 Id

pred E16_pre[s:State] {
    	some disj w : orcid.s, p: degois.s | some w.ids && some p.putcode.s && w.ids = p.ids && p.putcode.s != w.putcode.s && DeGois not in w.source &&
		w.putcode.s = Id0 && Recaap in w.source && Conference in w.type && no w.year &&
		p.key = Id0 && p.putcode.s = Id1 && Journal in p.type && no p.year

    one degois.s
    #orcid.s = 2
	no pending.s
}

run E16_pre {
	some s : State | consistent[s] && E16_pre[s]
} for 3 but 1 State



//
pred E17a[s:State] {
   	some disj w,w' : orcid.s, p: degois.s | same_group[w,w'] && w in preferred.s && some w.ids && some p.putcode.s && not same[w,p] && p.putcode.s != w.putcode.s && DeGois not in w.source
	# orcid.s = 2
    one degois.s
	no pending.s
}

run E17a {
	some s : State, s' : s.next | not  consistent[s] and E17a[s] and sync[s,s']
} for 5 but 2 State, 1 Year, 1 Title, 1 ISBN, 1 DOI, 3 Id


pred E17_pre[s:State] {
   	some disj w,w' : orcid.s, p: degois.s | some w.ids && some p.putcode.s && not same[w,p] && p.putcode.s != w.putcode.s && DeGois not in w.source &&
		w.putcode.s = Id1 && Recaap in w.source && Conference in w.type && no w.year &&
		p.key = Id1 && p.putcode.s = Id2 && Book in p.type && no p.year &&
		equal[s,s,p,w'] && not same_group[w,w']

    one degois.s
    #orcid.s = 3
	no Work-orcid.State
	no pending.s
}

run E17_pre {
	some s : State | consistent[s] &&  E17_pre[s]
} for 5 but 1 State


//
pred E19a[s:State] {
   	some disj w',w:orcid.s, disj p,p': degois.s | same[p,p']  && some p.putcode.s &&  equal[s,s,p,w] && equal[s,s,p',w']
    #degois.s = 2
	no pending.s
}

run E19a {
	some s : State, s' : s.next |   consistent[s] and E19a[s] and sync[s,s']
} for 5 but 2 State

pred E19_pre[s:State] {
    	some disj w:orcid.s, disj p,p': degois.s | same[p,p']  && some p.putcode.s &&  equal[s,s,p,w] &&
			p.putcode.s = Id0 && p.ids = DOI && p.type = Book && some p.year && p.key = Id1 &&
			p'.type = Book && p'.key = Id2
    # degois.s = 2
    one orcid.s
	no Work-orcid.State
	no pending.s
}

run E19_pre {
	some s : State | consistent[s] &&  E19_pre[s]
} for 5 but 1 State, 1 Title


pred E19c[s:State] {
   	some disj w',w:orcid.s, disj p,p': degois.s | same[p,p']  && some p.putcode.s &&  equal[s,s,p,w] && equal[s,s,p',w'] && same_group[w,w']
    #degois.s = 2
	no pending.s
}

run E19c {
	some s : State, s' : s.next |   consistent[s] and E19c[s] and sync[s,s']
} for 5 but 2 State


pred E19c_pre[s:State] {
   	some disj w:orcid.s, disj p,p': degois.s | same[p,p']  && some p.putcode.s &&  equal[s,s,p,w]  &&
			p.putcode.s = Id0 && p.ids = DOI && p.type = Journal && no p.year && p.key = Id0 &&
			p'.type = Journal && p'.key = Id2 && p'.ids = DOI  + ISBN
    # degois.s = 2
    one orcid.s
	no Work-orcid.State
	no pending.s
}

run E19c_pre {
	some s : State | consistent[s] &&  E19c_pre[s]
} for 5 but 1 State, 1 Title



//
pred E20a[s:State] {
   	some disj w',w:orcid.s, disj p: degois.s | DeGois in w.source && DeGois in w'.source &&  equal[s,s,p,w] && same_group[w,w'] &&
			w'.ids = EID && w.ids = EID && p.key = Id2 && w'.putcode.s = Id0 && some p.year && some w'.year && p.type = Book &&
			w in preferred.s
    #degois.s = 1
	no pending.s
}

run E20a {
	some s : State, s' : s.next |  not consistent[s] and E20a[s] and sync[s,s']
} for 3 but 2 State, 1 Year, 1 Title



pred E20_pre[s:State] {
     some disj w:orcid.s, disj p: degois.s | DeGois in w.source &&  equal[s,s,p,w] &&
		p.putcode.s = Id0 && p.type = Book && p.ids = EID && p.key = Id2 && some p.year 
    one degois.s
    one orcid.s
	no Work-orcid.State
	no pending.s
}

run E20_pre {
	some s : State | consistent[s] &&  E20_pre[s]
} for 5 but 1 State, exactly 1 Title, exactly 1 Year






pred E21_pre[s:State] {
     some disj w:orcid.s, disj p: degois.s | DeGois in w.source &&  equal[s,s,p,w] &&
		p.putcode.s = Id0 && p.type = Journal && p.ids = DOI && p.key = Id0 && no p.year
    one degois.s
    one orcid.s
	no Work-orcid.State
	no pending.s
}

run E21_pre {
	some s : State | consistent[s] &&  E21_pre[s]
} for 5 but 1 State, exactly 1 Title, exactly 1 Year

pred E21b[s:State] {
   	some disj w',w:orcid.s, disj p: degois.s | DeGois in w.source && DeGois in w'.source &&  equal[s,s,p,w] && same_group[w,w'] && w' in preferred.s &&
		p.ids = DOI && p.key = Id0 && p.type = Journal && no p.year
    #degois.s = 1
	no pending.s
	no pending.s
}

run E21b {
	some s : State, s' : s.next |  not consistent[s] and E21b[s] and sync[s,s']
} for 3 but 2 State

//
pred E22a[s:State] {
   	some disj w',w:orcid.s, disj p: degois.s | DeGois in w.source && DeGois not in w'.source &&  equal[s,s,p,w'] && same_group[w,w'] &&
			w in preferred.s && p.putcode.s = Id2 && p.key = Id0 && p.type = Journal && no p.year && w'.type = Journal
					
	
    #degois.s = 1
	#orcid.s = 2
	no pending.s
}

run E22a {
	some s : State, s' : s.next |  not consistent[s] and E22a[s] and sync[s,s']
} for 3 but 2 State


pred E23a[s:State] {
    no degois.s
	no orcid.s
	one pending.s
}

run E23a {
	some s : State, s' : s.next |  not consistent[s] and E23a[s] and sync[s,s']
} for 3 but 2 State


pred E23_pre[s:State] {
    no degois.s
	one orcid.s
	one pending.s
}

run E23_pre {
	some s : State | consistent[s] &&  E23_pre[s]
} for 5 but 1 State, exactly 1 Title, exactly 1 Year


pred E24a[s:State] {
	some w:orcid.s,p:pending.s | same[w,p] && not equal[s,s,w,p] && DeGois not in w.source && one p.ids && some p.putcode.s
    no degois.s
	one orcid.s
	one pending.s
}

run E24a {
	some s : State, s' : s.next |  not consistent[s] and E24a[s] and sync[s,s']
} for 3 but 2 State, 1 Title


pred E24_pre[s:State] {
	some w',w:orcid.s,p:pending.s | same[w,p] && not equal[s,s,w,p] && DeGois not in w.source && one p.ids && p.key = Id1 && p.type = Conference &&
		same_group[w,w'] && equal[s,s,p,w'] && some p.year && p.ids = DOI && p.putcode.s = Id1 && w.source = Scopus && w.putcode.s = Id0 &&
		some w.year && Conference = w.type
    no degois.s
	# orcid.s = 2
	one pending.s
}

run E24_pre {
	some s : State | consistent[s] &&  E24_pre[s]
} for 5 but 1 State, exactly 1 Title, exactly 1 Year



pred E25a[s:State] {
	some w:orcid.s,p':degois.s | equal[s,s,w,p'] 
    one degois.s
	one orcid.s
	no pending.s
}

run E25a {
	some s : State, s' : s.next |   consistent[s] and E25a[s] and sync[s,s']
} for 4 but 2 State


pred E25_pre[s:State] {
	some w:orcid.s,p:pending.s | equal[s,s,w,p]  && p.ids = DOI && p.key = Id0 && p.type = Book && no p.year && p.putcode.s = Id0
    no degois.s
	one orcid.s
	one pending.s
}

run E25_pre {
	some s : State |   consistent[s] and E25_pre[s]
} for 4 but 1 State



pred E26a[s:State] {
	some disj w,w':orcid.s,p:degois.s | w'.title = p.title && w'.type = p.type && w'.year = p.year && p.ids = w'.ids && some p.year && same[w,p] && w in preferred.s && DeGois in w'.source &&
			w.source not in DeGois && same_group[w,w'] && one w.ids && p.type = Conference && w.source = User && w.putcode.s = Id2 && some w.year &&
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
		w.source = DeGois && w''.source = DeGois && equal[s,s,w'',p] && same_group[w,w'] && same_group[w',w''] && 
		w in preferred.s and w'.source != DeGois

    #degois.s = 1
	#orcid.s = 3
	no pending.s
}

run E50a {
	some s : State, s' : s.next |  not consistent[s] and E40a[s] and sync[s,s']
} for 4 but 2 State


//E23: apagar grupo inteiro
// importa
// importar DeGois para ORCID quando tinha equivalente
// putcode de DeGois igual a putcode de ORCID não Degois: pode acontecer?


/*
 * Model of least-change lenses
 *
 * Demonstrations and properties for the paper:
 * [1] N. Macedo, H. Pacheco, A. Cunha and J. N. Oliveira. Composing Least-change Lenses, 2013
 * 
 * Author: Nuno Macedo 
 */

open util/natural

// *** Definition of the models and transformations ***
// ** S sources **
// f : S -> U transformation
sig S {
	getf : lone U,
	dist : S -> one Natural
}
// ** U sources/views **
// g : U -> V transformation
sig U {
	putf : S -> S,
	getg : lone V,
	dist : U -> one Natural
}
// ** V views **
sig V {
	putg : U -> U,
	dist : V -> one Natural
}
// ** g . f : S -> V transformation (composition) **
fun getgf : S -> V {
	{s : S, v : V | v in (getf.getg)[s]}
}
fun putgf : V -> S -> S {
	{v : V, s : S, s' : getgf.v | s' in v.putg[getf[s]].putf[s]}
}

// ** Distance properties **
// DistStable (identity of indiscernibles) ([1] Definition 2)
pred DistStable_S {
	all s, s' : S | s'.dist[s] = Zero iff s' = s
}
pred DistStable_U {
	all u, u' : U | u'.dist[u] = Zero iff u' = u
}
// Symmetry
fact DistSym {
	all s, s' : S | s'.dist[s] = s.dist[s']
	all u, u' : U | u'.dist[u] = u.dist[u']
	all s, s' : V | s'.dist[s] = s.dist[s']
}
// Discrete distance (for Proposition 4)
pred DistDiscrete_S{
	all s, s' : S | s = s' => dist[s,s'] = Zero else dist[s,s'] = One
}
// Redundant distance (for Proposition 5)
pred DistRedundant{
	all s, s' : S | s = s' => dist[s,s'] = Zero else (putf[getf[s'],s] = s' => dist[s,s'] = One else dist[s,s'] = inc[One])
	all u, u' : U | u = u' => dist[u,u'] = Zero else (putg[getg[u'],u] = u' => dist[u,u'] = One else dist[u,u'] = inc[One])
}

// ** Definition of shrinks
fun shrink_f : U -> S -> S {
	{u : U, s : S, s' : getf.u | all s'' : getf.u | lte[s'.dist[s],s''.dist[s]]}
}
fun shrink_g : V -> U -> U {
	{v : V, u : U, u' : getg.v | all u'' : getg.v | lte[u'.dist[u],u''.dist[u]]}
}
fun shrink_gf : V -> S -> S {
	{v : V, s : S, s' : getgf.v | all s'' : getgf.v | lte[s'.dist[s],s''.dist[s]]}
}

// ** Definition of complements (for Propositions 9 and 13)
sig S' {
	cplf : set S,
	dist : S' -> one Natural,
}
sig U' {
	cplg : set U,
	dist : U' -> one Natural
}
fact CplFun{
   all s : S | one cplf.s
   all u : U | one cplg.u
}
fact DistSym_Cpl {
	all s, s' : S' | s'.dist[s] = s.dist[s']
	all u, u' : U' | u'.dist[u] = u.dist[u']
}
pred PerfectComplement_f {
	all s:S | one getf[s] and one cplf.s
	all s':S', u:U | one s:S | s in getf.u and s in s'.cplf
}
pred PerfectComplement_g {
	all u:U | one getg[u] and one cplg.u
	all u':U', v:V | one u:U | u in getg.v and u in u'.cplg
}

// *** Behavioral properties of the transformations
// ** Transformation properties
// get Total
pred Total_f {
	all s : S | some getf[s]
}
pred Total_g {
	all u : U | some getg[u]
}
// get Injective
pred Injective_f {
	all u : U | lone getf.u
}
pred Injective_g {
	all v : V | lone getg.v
}
// get Surjective
pred Surjective_f {
	all u : U | some getf.u
}
pred Surjective_g {
	all v : V | some getg.v
}

// get Strictly Increasing
pred StrictlyIncreasing_f {
	all s, s', s'' : S | lt[dist[s,s'],dist[s,s'']] implies lt[dist[getf[s],getf[s']],dist[getf[s],getf[s'']]]
}
pred StrictlyIncreasing_g {
	all s, s', s'' : U | lt[dist[s,s'],dist[s,s'']] implies lt[dist[getg[s],getg[s']],dist[getg[s],getg[s'']]]
}
pred StrictlyIncreasing_gf {
	all s, s', s'' : S | lt[dist[s,s'],dist[s,s'']] implies lt[dist[getgf[s],getgf[s']],dist[getgf[s],getgf[s'']]]
}

// get Quasi Strictly Increasing
pred QuasiStrictlyIncreasing_f {
	all s, s', s'' : S | (all s''' : S | getf[s''] = getf[s'''] => lt[dist[s,s'],dist[s,s''']] ) implies lt[dist[getf[s],getf[s']],dist[getf[s],getf[s'']]]
}
pred QuasiStrictlyIncreasing_g {
	all s, s', s'' : U | (all s''' : U | getg[s''] = getg[s'''] => lt[dist[s,s'],dist[s,s''']] ) implies lt[dist[getg[s],getg[s']],dist[getg[s],getg[s'']]]
}
pred QuasiStrictlyIncreasing_gf {
	all s, s', s'' : S | (all s''' : S | getgf[s''] = getgf[s'''] => lt[dist[s,s'],dist[s,s''']] ) implies lt[dist[getgf[s],getgf[s']],dist[getgf[s],getgf[s'']]]
}

// get Strictly Increasing with complement
pred ComplementStrictlyIncreasing_f {
	all s, s', s'' : S | (lte[dist[getf[s],getf[s']],dist[getf[s],getf[s'']]] && cplf.s' = cplf.s'') implies lte[dist[s,s'],dist[s,s'']] 
}

// get Monotonic
pred Monotonic_f {
	all s, s', s'' : S | lte[dist[s,s'],dist[s,s'']] implies lte[dist[getf[s],getf[s']],dist[getf[s],getf[s'']]]
}
pred Monotonic_g {
	all s, s', s'' : U | lte[dist[s,s'],dist[s,s'']] implies lte[dist[getg[s],getg[s']],dist[getg[s],getg[s'']]]
}
pred Monotonic_gf {
	all s, s', s'' : S | lte[dist[s,s'],dist[s,s'']] implies lte[dist[getgf[s],getgf[s']],dist[getgf[s],getgf[s'']]]
}

// get Quasi Monotonic
pred QuasiMonotonic_f {
	all s, s', s'' : S | (all s''' : S | getf[s''] = getf[s'''] => lte[dist[s,s'],dist[s,s''']] ) implies lte[dist[getf[s],getf[s']],dist[getf[s],getf[s'']]]
}
pred QuasiMonotonic_g {
	all s, s', s'' : U | (all s''' : U | getg[s''] = getg[s'''] => lte[dist[s,s'],dist[s,s''']] ) implies lte[dist[getg[s],getg[s']],dist[getg[s],getg[s'']]]
}
pred QuasiMonotonic_gf {
	all s, s', s'' : S | (all s''' : S | getgf[s''] = getgf[s'''] => lte[dist[s,s'],dist[s,s''']] ) implies lte[dist[getgf[s],getgf[s']],dist[getgf[s],getgf[s'']]]
}

// get Monotonic with complement
pred ComplementMonotonic_f {
	all s, s', s'' : S | (lt[dist[getf[s],getf[s']],dist[getf[s],getf[s'']]] && cplf.s' = cplf.s'') implies lt[dist[s,s'],dist[s,s'']] 
}


// put Deterministic
pred Deterministic_putf {
	all s : S, u : U | lone u.putf[s]
}
pred Deterministic_putg {
	all u : U, v : V | lone v.putg[u]
}
pred Deterministic_putgf {
	all s : S, v : V | lone v.putgf[s]
}
// put Total (for views on the range of get)
pred Total_putf {
	all s : S, u : S.getf | some u.putf[s]
}
pred Total_putg {
	all u : U, v : U.getg | some v.putg[u]
}
pred Total_putgf {
	all s : S, v : S.getgf | some v.putgf[s]
}
// shrink Deterministic
pred Deterministic_shrink_f {
	all s : S, u : U | lone u.shrink_f[s]
}
pred Deterministic_shrink_g {
	all u : U, v : V | lone v.shrink_g[u]
}
pred Deterministic_shrink_gf {
	all s : S, v : V | lone v.shrink_gf[s]
}

// ** Bidirectional properties ([1] Sec. 2)
// PutGet
pred PutGet_f {
	all s : S, u : U | u.putf[s] in getf.u
}
pred PutGet_g {
	all u : U, v : V | v.putg[u] in getg.v
}
pred PutGet_gf {
	all s : S, v : V | v.putgf[s] in getgf.v
}
// GetPut
pred GetPut_f {
	all u : U, s : getf.u | s in u.putf[s]
}
pred GetPut_g {
	all v : V, u : getg.v | u in v.putg[u]
}
pred GetPut_gf {
	all v : V, s : getgf.v | s in v.putgf[s]
}
// LeastPutGet
pred LeastPutGet_f {
	all s : S, u : U | u.putf[s] in u.shrink_f[s]
}
pred LeastPutGet_g {
	all u : U, v : V | v.putg[u] in v.shrink_g[u]
}
pred LeastPutGet_gf {
	all s : S, v : V | v.putgf[s] in v.shrink_gf[s]
}
// LeastGetPut
pred LeastGetPut_f {
	all s : S, u : U | u.shrink_f[s] in u.putf[s]
}
pred LeastGetPut_g {
	all u : U, v : V | v.shrink_g[u] in v.putg[u]
}
pred LeastGetPut_gf {
	all s : S, v : V | v.shrink_gf[s] in v.putgf[s]
}
// ** Lens definitions ([1] Sec. 2)
// Regular (classic) lens ([1] Definition 1)
pred Regular_lens_f{
	Deterministic_putf
    GetPut_f
	PutGet_f
}
pred Regular_lens_g{
	Deterministic_putgf
    GetPut_g
	PutGet_g
}
// Deterministic least-change lens ([1] Definition 3)
pred Deterministic_lclens_f{
	Deterministic_putf
	DistStable_S
    GetPut_f
	LeastPutGet_f
}
pred Deterministic_lclens_g{
	Deterministic_putg
	DistStable_U
    GetPut_g
	LeastPutGet_g
}
pred Deterministic_lclens_gf{
	Deterministic_putgf
	DistStable_S
    GetPut_gf
	LeastPutGet_gf
}
// Nondeterministic least-change lens ([1] Definition 4)
pred Nondeterministic_lclens_f{
	DistStable_S
    PutGet_f
	LeastGetPut_f
}
pred Nondeterministic_lclens_g{
	DistStable_U
    PutGet_g
	LeastGetPut_g
}
pred Nondeterministic_lclens_gf{
	DistStable_S
    PutGet_gf
	LeastGetPut_gf
}

// *** Propositions from [1] ***
// ** Least-change lens properties ([1] Sec. 3) **
// Proposition 1
check LeastPutGet_Stronger_PutGet {
	LeastPutGet_f
	implies
	PutGet_f
} for 6
check LeastGetPut_Stronger_GetPut {
	(LeastGetPut_f and DistStable_S)
	implies
	GetPut_f
} for 6
// Proposition 2
check UniqueDeterministicPut {
	(Total_putf and Deterministic_lclens_f and Deterministic_shrink_f)
	implies
	(putf = shrink_f)
} for 6
// Proposition 3
check DetLeastChangeLens_RegularLens {
	Deterministic_lclens_f
	implies
	Regular_lens_f
} for 6
// Proposition 4
check RegularLens_DetLeastChangeLens {
	(Regular_lens_f and DistDiscrete_S)
	implies
	Deterministic_lclens_f
} for 6
// Proposition 5
check RegularLens_NDetLeastChangeLens {
	(Regular_lens_f and DistRedundant and Total_putf)
	implies
	Nondeterministic_lclens_f
} for 6

// ** Compositionality of deterministic least-change lens ([1] Sec. 4) **
// Proposition 6
check DetLeastChangeLens_Injective_g {
	(Deterministic_lclens_f and Deterministic_lclens_g and Injective_g)
	implies
	Deterministic_lclens_gf
} for 6
// Proposition 7
check DetLeastChangeLens_StrictlyIncreasing_f {
	(Deterministic_lclens_f and Deterministic_lclens_g and StrictlyIncreasing_f)
	implies
	Deterministic_lclens_gf
} for 6
// Proposition 8
check Compose_StrictlyIncreasing {
	(StrictlyIncreasing_f and StrictlyIncreasing_g)
	implies
	StrictlyIncreasing_gf
} for 6
// Proposition 9
check DetLeastChangeLens_QuasiStrictlyIncreasing_f {
	(Deterministic_lclens_f and Deterministic_lclens_g and QuasiStrictlyIncreasing_f)
	implies
	Deterministic_lclens_gf
} for 6
// Proposition 10
check Compose_QuasiStrictlyIncreasing {
	(QuasiStrictlyIncreasing_f and QuasiStrictlyIncreasing_g and Surjective_f)
	implies
	QuasiStrictlyIncreasing_gf
} for 6
// Proposition 11
check DetLeastChangeLens_CplStrictlyIncreasing_f {
	(ComplementStrictlyIncreasing_f and PerfectComplement_f)
	implies
	QuasiStrictlyIncreasing_f
} for 6

// ** Compositionality of nondeterministic least-change lens ([1] Sec. 4) **
// Proposition 12
check NDetLeastChangeLens_Injective_g {
	(Nondeterministic_lclens_f and Nondeterministic_lclens_g and Injective_g and Total_f)
	implies
	Nondeterministic_lclens_gf
} for 6
// Proposition 13
check NDetLeastChangeLens_Monotonic_f {
	(Nondeterministic_lclens_f and Nondeterministic_lclens_g and Monotonic_f and Surjective_f)
	implies
	Nondeterministic_lclens_gf
} for 6
// Proposition 14
check Compose_Monotonic {
	(Monotonic_f and Monotonic_g)
	implies
	Monotonic_gf
} for 6
// Proposition 15
check NDetLeastChangeLens_QuasiMonotonic_f {
	(Nondeterministic_lclens_f and Nondeterministic_lclens_g and QuasiMonotonic_f and Surjective_f)
	implies
	Nondeterministic_lclens_gf
} for 6
// Proposition 16
check Compose_QuasiMonotonic {
	(QuasiMonotonic_f and QuasiMonotonic_g and Surjective_f)
	implies
	QuasiMonotonic_gf
} for 6
// Proposition 17
check NDetLeastChangeLens_CplMonotonic_f {
	(ComplementMonotonic_f and PerfectComplement_f)
	implies
	QuasiMonotonic_f
} for 6

// *** Other properties ***
// Put from Nondeterminisitc least-change lenses is total
check NDetLeastChangeLens_Total_put {
	(Nondeterministic_lclens_f)
	implies
	Total_putf
} for 6
// Strictly Increasing is stronger than Quasi Strictly Increasing
check StrictlyIncreasing_QuasiStrictlyIncreasing {
	StrictlyIncreasing_f
	implies
	QuasiStrictlyIncreasing_f
} for 6
// Monotonic is stronger than Quasi Monotonic
check Monotonic_QuasiMonotonic {
	Monotonic_f
	implies
	QuasiMonotonic_f
} for 6


check {
  (LeastGetPut_g and LeastGetPut_f  and QuasiMonotonic_f and  DistStable_S  and Surjective_f)
  =>
  LeastGetPut_gf
} for 5


// *** Example runs ***
run ExampleDeterministic {
	Deterministic_lclens_g and Deterministic_lclens_f and some S and some U and some V
} for 3

run ExampleNondeterministic {
	Nondeterministic_lclens_g and Nondeterministic_lclens_f and some S and some U and some V
} for 3



/**
@author Nuno Macedo
**/

open util/ordering[Passo]

sig Passo {}

abstract sig Margem {}
one sig Esquerda, Direita extends Margem {}

abstract sig Objeto {
	margem : Margem one -> Passo
}

one sig Agricultor extends Objeto {} 

abstract sig Comestivel extends Objeto {}
one sig Lobo, Ganso, Couve extends Comestivel {}

pred inicio[p:Passo] {
	all o : Objeto | (o.margem).p = Esquerda
}

pred leva[p,p':Passo,o:Objeto] {
	(o.margem).p = (Agricultor.margem).p

	(Agricultor.margem).p' = atravessa[(Agricultor.margem).p]	
	(o.margem).p' = atravessa[(o.margem).p]

	all o' : Comestivel - o | o'.margem.p = o'.margem.p'
}

pred sozinho[p,p':Passo] {
	(Agricultor.margem).p' = atravessa[(Agricultor.margem).p]

	all o' : Comestivel | o'.margem.p = o'.margem.p'
}

fun atravessa [m:Margem] : Margem {
	Margem - m
}

fact evolucao {
	inicio[first]
	all p: Passo - last | 
		(some o : Comestivel | leva[p,p.next,o]) or sozinho[p,p.next]
}

pred come[p:Passo] {
	((Ganso.margem).p = (Couve.margem).p and (Ganso.margem).p != (Agricultor.margem).p) or
	((Ganso.margem).p = (Lobo.margem).p and (Ganso.margem).p != (Agricultor.margem).p)		
}

run {
	all p : Passo | not come[p]
	some p : Passo | all o:Objeto | o.margem.p = Direita
} for 8 Passo

/** 
@author: Nuno Macedo
**/

abstract sig Pessoa {
	father: lone Man,
	mother: lone Woman
	}

sig Man extends Pessoa {
	wife: lone Woman
	}

sig Woman extends Pessoa {
	husband: lone Man
	}

fact Biology {
	no p: Pessoa | p in p.^(mother+father)
	}

fact Terminology {
	wife = ~husband
	}

fact SocialConvention {
	no (wife+husband) & ^(mother+father)
	}

run {} for exactly 2 Woman, exactly 2 Man
------------------------------------------

assert NoSelfFather {
	no m: Man | m = m.father
	}

// This should not find any counterexample.
check NoSelfFather

------------------------------------------

fun grandpas [p: Pessoa] : set Pessoa {
	let parent = mother + father + father.wife + mother.husband |
		p.parent.parent & Man
	}

pred ownGrandpa [p: Pessoa] {
	p in p.grandpas
	}

// This generates an instance similar to Fig 4.3
run ownGrandpa for 4 Pessoa

------------------------------------------

pred SocialConvention1 {
	no (wife + husband) & ^(mother + father)
	}

pred SocialConvention2 {
	let parent = mother + father {
		no m: Man | some m.wife and m.wife in m.*parent.mother
		no w: Woman | some w.husband and w.husband in w.*parent.father
		}
	}

// This assertion was described on page 90.
assert Same {
	SocialConvention1 iff SocialConvention2
	}

// This should not find any counterexample
check Same

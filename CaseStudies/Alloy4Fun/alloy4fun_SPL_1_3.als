module alloy4fun

/* 
 * A model of Alloy4Fun (http://alloy4fun.inesctec.pt)
 * with several independent features
 * 
 * ➀store derivation trees➀
 * ➁allow models with secrets➁
 * ➂store models when executing commands➂
 * ➃allow permalinks to instances➃
 *
 * author: Colorful Alloy team, 07/2019
 */

fact FeatureModel {

}

sig StoredModel {
	derivationOf : lone StoredModel,
	public : lone Link,
	command : lone Command
}

sig Link {}

sig Command {}

fact Links {
	// Links are not shared between models there are no links without models
	all l : Link | one (public).l
}

pred BadSpec {

}

pred GoodSpec {

}

fact Derivations {
	// The derivations form a tree
	no m : StoredModel | m in m.^derivationOf
	// Models without a link can only have at most one derivation
	all m : StoredModel | no m.public implies lone derivationOf.m
}

fact Commands {
	// Commands are unique to one model and there ano commands without models
	all c : Command | one command.c
	// With commands a model is either stored as result permalinking xor running a command
	all m : StoredModel | no m.public iff some m.command
}

fact Instances {

}

run {} for 4 but 8 Link

assert NoCommands {

}

assert PublicAndSecretLinksDisjoint {

}

assert OneDerivation{
	// models without a public link can have at most one Dervation
	all m:StoredModel | no m.public implies lone derivationOf.m
}

check OneDerivation for 20
check OneDerivation for 30

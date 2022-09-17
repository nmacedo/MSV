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
	secret : lone Link,
	command : lone Command
}

sig Secret in StoredModel {}

sig Link {}

sig Command {}

fact Links {
	// Links are not shared between models there are no links without models
	all l : Link | one (public+secret).l
	// Only models with secrets can have a secret link 
	secret.Link in Secret
	// Secret link are created with permalinking
	all m : Secret | some m.secret implies some m.public
	// If a model with secrets has a public link it must be or derive from one with
	// a secret link
	all m : Secret | some m.public implies some m.(^derivationOf+iden).secret
}

pred BadSpec {
	// Private and public links, if existing, must be different
	all m : StoredModel | m.public != m.secret
}

pred GoodSpec {
	// Private and public links, if existing, must be different
	all m : StoredModel | no m.public & m.secret
}

fact Derivations {
	// The derivations form a tree
	no m : StoredModel | m in m.^derivationOf
	// Models without a link can only have at most one derivation
	all m : StoredModel | no m.public implies lone derivationOf.m
	// When secrets are removed a new derivation tree is started,
	// otherwise you could gain access to secret information of others
	all m : Secret | ^derivationOf.m in Secret
	// A model with secrets just with a public link cannot derive into one with a secret link
	all m : Secret | (some m.public and no m.secret) implies no (*derivationOf.m).secret
}

fact Commands {
	// Commands are unique to one model and there ano commands without models
	all c : Command | one command.c
	// With commands a model is either stored as result permalinking xor running a command
	all m : StoredModel | no m.public iff some m.command
}

fact Instances {

}

run {GoodSpec} for 4 but 8 Link

assert NoCommands {
	// There are no commands
	BadSpec implies no command
}

check NoCommands for 20
check NoCommands for 20

assert PublicAndSecretLinksDisjoint {
	// The set of public and secret links is disjoint
	GoodSpec implies no StoredModel.public & StoredModel.secret
}

check PublicAndSecretLinksDisjoint for 20
check PublicAndSecretLinksDisjoint for 20

assert OneDerivation{
	// models without a public link can have at most one Dervation
	all m:StoredModel | no m.public implies lone derivationOf.m
}

check OneDerivation for 20
check OneDerivation for 30

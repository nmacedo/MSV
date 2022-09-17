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

abstract sig Feature {}
one sig F1,F2,F3,F4 extends Feature{}
sig Variant in Feature {}

fact FeatureModel {
	(no F3 & Variant and F4 in Variant) implies some none 
}

sig StoredModel {
	derivationOf : lone StoredModel,
	public : lone Link,
	secret : lone Link,
	command : set Command
}

fact {
	F1 in Variant implies derivationOf in StoredModel -> lone StoredModel else no derivationOf
	F2 in Variant implies secret in StoredModel -> lone Link else no secret
	F3 in Variant implies command in StoredModel -> lone Command else no command
	no F2 & Variant implies no Secret
	no F3 & Variant implies no Command
	no (F3+F4) & Variant implies no Instance
}

sig Secret in StoredModel {}

sig Link {}

sig Command {}

sig Instance {
	instanceOf : one Command,
	model : set StoredModel,
	link : one Link
}

fact Links {
	// Links are not shared between models there are no links without models
	all l : Link | one (public+(F2 in Variant implies secret else none -> none)+(F3+F4 in Variant implies link else none -> none)).l
	// Without commands all models have links
	no F3 & Variant implies all m : StoredModel | one m.public
	// Only models with secrets can have a secret link 
	F2 in Variant implies secret.Link in Secret
	// Secret link are created with permalinking
	F2 in Variant implies all m : Secret | some m.secret implies some m.public
	// If a model with secrets has a public link it must be or derive from one with
	// a secret link
	F2 in Variant implies all m : Secret | some m.public implies some m.((F1 in Variant implies ^derivationOf else none -> none)+iden).secret
}

pred BadSpec {
	// Private and public links, if existing, must be different
	F2 in Variant implies all m : StoredModel | m.public != m.secret
}

pred GoodSpec {
	// Private and public links, if existing, must be different
	F2 in Variant implies all m : StoredModel | no m.public & m.secret
}

fact Derivations {
	// The derivations form a tree
	F1 in Variant implies no m : StoredModel | m in m.^derivationOf
	// Models without a link can only have at most one derivation
	F1 in Variant implies all m : StoredModel | no m.public implies lone derivationOf.m
	// When secrets are removed a new derivation tree is started,
	// otherwise you could gain access to secret information of others
	F1+F2 in Variant implies all m : Secret | ^derivationOf.m in Secret
	// A model with secrets just with a public link cannot derive into one with a secret link
	F1+F2 in Variant implies all m : Secret | (some m.public and no m.secret) implies no (*derivationOf.m).secret
}

fact Commands {
	// Commands are unique to one model and there ano commands without models
	F3 in Variant implies all c : Command | one command.c
	// With commands a model is either stored as result permalinking xor running a command
	F3 in Variant implies all m : StoredModel | no m.public iff some m.command
}

fact Instances {
	// Auxiliary relation for visualization
	F3+F4 in Variant implies model = instanceOf.~command
	// Commands have at most one instance
	F3+F4 in Variant implies all c : Command | lone instanceOf.c
}

run {no (F1+F2+F3+F4) & Variant} for 4
run {F1 = Variant} for 4
run {GoodSpec and F2 = Variant} for 4
run {F3 = Variant} for 4
run {GoodSpec and F1+F2 = Variant} for 4 but 8 Link
run {F1+F3 = Variant} for 4 but 8 Link
run {GoodSpec and F2+F3 = Variant} for 4 but 8 Link
run {F3+F4 = Variant} for 4 but 8 Link
run {F1+F3+F4 = Variant} for 4 but 8 Link
run {GoodSpec and F1+F2+F3 = Variant} for 4 but 8 Link
run {GoodSpec and F2+F3+F4 = Variant} for 4 but 8 Link
run {GoodSpec and F1+F2+F3+F4 = Variant} for 4 but 8 Link

pred NoCommands {
	// There are no commands
	F2+F3 in Variant implies BadSpec implies no command
}

check {F2+F3 in Variant implies NoCommands} for 20
check {F2+F3 = Variant implies NoCommands} for 20
check {F1+F2+F3 = Variant implies NoCommands} for 20
check {F2+F3+F4 = Variant implies NoCommands} for 20
check {F1+F2+F3+F4 = Variant implies NoCommands} for 20


pred PublicAndSecretLinksDisjoint {
	// The set of public and secret links is disjoint
	F2 in Variant implies GoodSpec implies no StoredModel.public & StoredModel.secret
}
check {F2 in Variant implies PublicAndSecretLinksDisjoint} for 20
check {F2 = Variant implies PublicAndSecretLinksDisjoint} for 20
check {F1+F2 = Variant implies PublicAndSecretLinksDisjoint} for 20
check {F2+F3 = Variant implies PublicAndSecretLinksDisjoint} for 20
check {F1+F2+F3 = Variant implies PublicAndSecretLinksDisjoint} for 20
check {F2+F3+F4 = Variant implies PublicAndSecretLinksDisjoint} for 20
check {F1+F2+F3+F4 = Variant implies PublicAndSecretLinksDisjoint} for 20

pred OneDerivation{
	// models without a public link can have at most one Dervation
	F1 in Variant implies all m:StoredModel | no m.public implies lone derivationOf.m
}

check {F1 in Variant implies OneDerivation} for 20
check {F1 = Variant implies OneDerivation} for 25
check {F1 in Variant implies OneDerivation} for 30
check {F1 = Variant implies OneDerivation} for 30

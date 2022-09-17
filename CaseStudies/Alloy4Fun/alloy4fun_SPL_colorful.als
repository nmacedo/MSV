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
 * author: Alloy4Fun team, 07/2019
 */
*/

fact FeatureModel {
	// ➃ requires ➂
	➃➌some none➌➃
}

sig StoredModel {
	➀derivationOf : lone StoredModel➀,
	public : lone Link,
	➁secret : lone Link➁,
	➂command : lone Command➂
}

➁sig Secret in StoredModel {}➁

sig Link {}

➂sig Command {}➂

➂➃sig Instance {
	instanceOf : one Command,
	model : set StoredModel,
	link : one Link
}➃➂

fact Links {
	// Links are not shared between models there are no links without models
	all l : Link | one (public+➁secret➁+➂➃link➃➂).l
	// Without commands all models have links
	➌all m : StoredModel | one m.public➌
	// Only models with secrets can have a secret link 
	➁secret.Link in Secret➁
	// Secret link are created with permalinking
	➁all m : Secret | some m.secret implies some m.public➁
	// If a model with secrets has a public link it must be or derive from one with
	// a secret link
	➁all m : Secret | some m.public implies some m.(➀^derivationOf➀+iden).secret➁
}

pred BadSpec {
	// Private and public links, if existing, must be different
	➁all m : StoredModel | m.public != m.secret➁
}

pred GoodSpec {
	// Private and public links, if existing, must be different
	➁all m : StoredModel | no m.public & m.secret➁
}

fact Derivations {
	// The derivations form a tree
	➀no m : StoredModel | m in m.^derivationOf➀
	// Models without a link can only have at most one derivation
	➀all m : StoredModel | no m.public implies lone derivationOf.m➀
	// When secrets are removed a new derivation tree is started,
	// otherwise you could gain access to secret information of others
	➀➁all m : Secret | ^derivationOf.m in Secret➁➀
	// A model with secrets just with a public link cannot derive into one with a secret link
	➀➁all m : Secret | (some m.public and no m.secret) implies no (*derivationOf.m).secret➁➀
}

fact Commands {
	// Commands are unique to one model and there ano commands without models
	➂all c : Command | one command.c➂
	// With commands a model is either stored as result permalinking xor running a command
	➂all m : StoredModel | no m.public iff some m.command➂
}

fact Instances {
	// Auxiliary relation for visualization
	➂➃model = instanceOf.~command➃➂
	// Commands have at most one instance
	➂➃all c : Command | lone instanceOf.c➃➂
}

run {} with ➊,➋,➌,➍ for 4
run {} with exactly ➀ for 4
run {GoodSpec} with exactly ➁ for 4
run {} with exactly ➂ for 4
run {GoodSpec} with exactly ➀,➁ for 4 but 8 Link
run {} with exactly ➀,➂ for 4 but 8 Link
run {GoodSpec} with exactly ➁,➂ for 4 but 8 Link
run {} with exactly ➂,➃ for 4 but 8 Link
run {} with exactly ➀,➂,➃ for 4 but 8 Link
run {GoodSpec} with exactly ➀,➁,➂ for 4 but 8 Link
run {GoodSpec} with exactly ➁,➂,➃ for 4 but 8 Link
run {GoodSpec} with exactly ➀,➁,➂,➃ for 4 but 8 Link

assert NoCommands {
	// There are no commands
	➂➁BadSpec implies no command➁➂
}

check NoCommands with ➁,➂ for 20
check NoCommands with exactly ➁,➂ for 20
check NoCommands with exactly ➀,➁,➂ for 20
check NoCommands with exactly ➁,➂,➃ for 20
check NoCommands with exactly ➀,➁,➂,➃ for 20

assert PublicAndSecretLinksDisjoint {
	// The set of public and secret links is disjoint
	➁GoodSpec implies no StoredModel.public & StoredModel.secret➁
}

check PublicAndSecretLinksDisjoint with ➁ for 20
check PublicAndSecretLinksDisjoint with exactly ➁ for 20
check PublicAndSecretLinksDisjoint with exactly ➀,➁ for 20
check PublicAndSecretLinksDisjoint with exactly ➁,➂ for 20
check PublicAndSecretLinksDisjoint with exactly ➀,➁,➂ for 20
check PublicAndSecretLinksDisjoint with exactly ➁,➂,➃ for 20
check PublicAndSecretLinksDisjoint with exactly ➀,➁,➂,➃ for 20

assert OneDerivation{
	// models without a public link can have at most one Dervation
	➀all m:StoredModel | no m.public implies lone derivationOf.m➀ 
}

check OneDerivation with ➀ for 20
check OneDerivation with exactly ➀ for 25
check OneDerivation with ➀ for 30
check OneDerivation with exactly ➀ for 30

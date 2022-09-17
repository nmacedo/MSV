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
	public : lone Link,
	secret : lone Link,
}

sig Secret in StoredModel {}

sig Link {}

fact Links {
	// Links are not shared between models there are no links without models
	all l : Link | one (public+secret).l
	// Without commands all models have links
	all m : StoredModel | one m.public
	// Only models with secrets can have a secret link 
	secret.Link in Secret
	// Secret link are created with permalinking
	all m : Secret | some m.secret implies some m.public
	// If a model with secrets has a public link it must be or derive from one with
	// a secret link
	all m : Secret | some m.public implies some m.(iden).secret
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
	
}

fact Commands {

}

fact Instances {

}

run {GoodSpec} for 4

assert NoCommands {

}

assert PublicAndSecretLinksDisjoint {
	// The set of public and secret links is disjoint
	GoodSpec implies no StoredModel.public & StoredModel.secret
}

check PublicAndSecretLinksDisjoint for 20
check PublicAndSecretLinksDisjoint for 20

assert OneDerivation{

}

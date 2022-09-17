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
}

sig Link {}

fact Links {
	// Links are not shared between models there are no links without models
	all l : Link | one (public).l
	// Without commands all models have links
	all m : StoredModel | one m.public
}

pred BadSpec {

}

pred GoodSpec {

}

fact Derivations {

}

fact Commands {

}

fact Instances {

}

run {} for 4

assert NoCommands {

}

assert PublicAndSecretLinksDisjoint {

}

assert OneDerivation{

}

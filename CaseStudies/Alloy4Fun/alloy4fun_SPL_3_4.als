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
	command : lone Command
}

sig Link {}

sig Command {}

sig Instance {
	instanceOf : one Command,
	model : set StoredModel,
	link : one Link
}

fact Links {
	// Links are not shared between models there are no links without models
	all l : Link | one (public+link).l
}

pred BadSpec {

}

pred GoodSpec {

}

fact Derivations {

}

fact Commands {
	// Commands are unique to one model and there ano commands without models
	all c : Command | one command.c
	// With commands a model is either stored as result permalinking xor running a command
	all m : StoredModel | no m.public iff some m.command
}

fact Instances {
	// Auxiliary relation for visualization
	model = instanceOf.~command
	// Commands have at most one instance
	all c : Command | lone instanceOf.c
}

run {} for 4 but 8 Link

assert NoCommands {

}

assert PublicAndSecretLinksDisjoint {

}

assert OneDerivation{

}

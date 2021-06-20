module NHSM [Model]
sig StateN {staten : set Model,nameN : String -> Model}

fact {all m : Model | nameN.m in (staten.m -> one String)}

sig TransitionN {transitionn : set Model,triggerN : String -> Model,effectN : String -> Model,sourceN : StateN -> Model,targetN : StateN -> Model}

fact {all m : Model | (triggerN.m in (transitionn.m -> lone String)) && ((effectN.m in (transitionn.m -> set String)) && ((sourceN.m in (transitionn.m -> one staten.m)) && (targetN.m in (transitionn.m -> one staten.m))))}

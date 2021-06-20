module HSM [Model]
sig StateH {stateh : set Model,nameH : String -> Model,owner : CState -> Model}

fact {all m : Model | (nameH.m in (stateh.m -> one String)) && (owner.m in (stateh.m -> lone cstate.m))}

sig CState extends StateH {cstate : set Model}

sig TransitionH {transitionh : set Model,triggerH : String -> Model,effectH : String -> Model,sourceH : StateH -> Model,targetH : StateH -> Model}

fact {all m : Model | (triggerH.m in (transitionh.m -> lone String)) && ((effectH.m in (transitionh.m -> set String)) && ((sourceH.m in (transitionh.m -> one stateh.m)) && (targetH.m in (transitionh.m -> one stateh.m))))}

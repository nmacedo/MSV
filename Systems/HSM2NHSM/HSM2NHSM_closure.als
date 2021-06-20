open util/ordering[Model]

module HSM2NHSM
open HSM [Source]
open NHSM [Target]
open util/integer
abstract sig Model {}

abstract sig Source extends Model {
   state2state : Target -> Class -> Table,
   primitivestate2state : Target -> Class -> Table,
   complexstate2state : Target -> Class -> Table,
   transition2transition : Target -> Class -> Table
}
abstract sig Target extends Model {}

pred Pattern_State2State_Source [hsm : Source,srcS : StateH,n : String] {(n in srcS.(nameH.hsm)) && (none = srcS.(owner.hsm))}

pred Pattern_State2State_Target [nhsm : Target,trgS : StateN,n : String] {n in trgS.(nameN.nhsm)}

pred Check_State2State_Source [hsm : Source,nhsm : Target] {all srcS : stateh.hsm,n : String | Pattern_State2State_Source[hsm,srcS,n] => (some trgS : StateN | Pattern_State2State_Target[nhsm,trgS,n])}

pred Check_State2State_Target [hsm : Source,nhsm : Target] {all trgS : staten.nhsm,n : String | Pattern_State2State_Target[nhsm,trgS,n] => (some srcS : StateH | Pattern_State2State_Source[hsm,srcS,n])}

fun State2State_Target [hsm : Source,nhsm : Target] : staten.nhsm -> stateh.hsm {{trgS : staten.nhsm,srcS : stateh.hsm | all n : String | Pattern_State2State_Target[nhsm,trgS,n] => Pattern_State2State_Source[hsm,srcS,n]}}

fun State2State_Source [hsm : Source,nhsm : Target] : stateh.hsm -> staten.nhsm {{srcS : stateh.hsm,trgS : staten.nhsm | all n : String | Pattern_State2State_Source[hsm,srcS,n] => Pattern_State2State_Target[nhsm,trgS,n]}}

pred Pattern_Transition2Transition_Source [hsm : Source,srcSS : StateH,srcST : StateH,srcT : TransitionH] {srcSS in srcT.(sourceH.hsm) && srcST in srcT.(targetH.hsm)}

pred Pattern_Transition2Transition_Target [nhsm : Target,trgSS : StateN,trgST : StateN,trgT : TransitionN] {trgSS in trgT.(sourceN.nhsm) && trgST in trgT.(targetN.nhsm)}

pred Check_Transition2Transition_Source [hsm : Source,nhsm : Target] {all srcSS : stateh.hsm,srcST : stateh.hsm,srcT : transitionh.hsm | Pattern_Transition2Transition_Source[hsm,srcSS,srcST,srcT] => (some trgSS : staten.nhsm,trgST : staten.nhsm,trgT : transitionn.nhsm | Pattern_Transition2Transition_Target[nhsm,trgSS,trgST,trgT] && Where_Transition2Transition[hsm,nhsm,srcSS,srcST,trgSS,trgST])}

pred Check_Transition2Transition_Target [hsm : Source,nhsm : Target] {all trgSS : staten.nhsm,trgST : staten.nhsm,trgT : transitionn.nhsm | Pattern_Transition2Transition_Target[nhsm,trgSS,trgST,trgT] => (some srcSS : stateh.hsm,srcST : stateh.hsm,srcT : transitionh.hsm | Pattern_Transition2Transition_Source[hsm,srcSS,srcST,srcT] && Where_Transition2Transition[hsm,nhsm,srcSS,srcST,trgSS,trgST])}

fun Transition2Transition_Target [hsm : Source,nhsm : Target] : transitionn.nhsm -> transitionh.hsm {{trgT : transitionn.nhsm,srcT : transitionh.hsm | all trgSS : staten.nhsm,trgST : staten.nhsm | Pattern_Transition2Transition_Target[nhsm,trgSS,trgST,trgT] => (some srcSS : stateh.hsm,srcST : stateh.hsm | Pattern_Transition2Transition_Source[hsm,srcSS,srcST,srcT] && Where_Transition2Transition[hsm,nhsm,srcSS,srcST,trgSS,trgST])}}

fun Transition2Transition_Source [hsm : Source,nhsm : Target] : transitionh.hsm -> transitionn.nhsm {{srcT : transitionh.hsm,trgT : transitionn.nhsm | all srcSS : stateh.hsm,srcST : stateh.hsm | Pattern_Transition2Transition_Source[hsm,srcSS,srcST,srcT] => (some trgSS : staten.nhsm,trgST : staten.nhsm | Pattern_Transition2Transition_Target[nhsm,trgSS,trgST,trgT] && Where_Transition2Transition[hsm,nhsm,srcSS,srcST,trgSS,trgST])}}

pred Where_Transition2Transition [hsm : Source,nhsm : Target,srcSS : StateH,srcST : StateH,trgSS : StateN,trgST : StateN] {
  (some s : StateH | s in srcSS.*(owner.hsm) && no s.owner && s in State2State_Source[hsm,nhsm].trgSS && trgSS in State2State_Target[hsm,nhsm].s) && 
  (some s : StateH | s in srcST.*(owner.hsm) && no s.owner && s in State2State_Source[hsm,nhsm].trgST && trgST in State2State_Target[hsm,nhsm].s)}

pred Check_State2State [hsm : Source,nhsm : Target] {Check_State2State_Source[hsm,nhsm] && Check_State2State_Target[hsm,nhsm]}

pred Check_Transition2Transition [hsm : Source,nhsm : Target] {Check_Transition2Transition_Source[hsm,nhsm] && Check_Transition2Transition_Target[hsm,nhsm]}

pred Check [hsm : Source,nhsm : Target] {Check_State2State[hsm,nhsm] && Check_Transition2Transition[hsm,nhsm] && Valid_HSM[hsm]}

pred state_add[hsm,hsm' : Source] {
        one x : StateH {
                x not in stateh.hsm
                stateh.hsm' = stateh.hsm + x

				nameH.hsm' = nameH.hsm
                cstate.hsm' = cstate.hsm
                transitionh.hsm' = transitionh.hsm
                triggerH.hsm' = triggerH.hsm
                effectH.hsm' = effectH.hsm
                sourceH.hsm' = sourceH.hsm
                targetH.hsm' = targetH.hsm
				owner.hsm' = owner.hsm
        }
}

pred state_del[hsm,hsm' : Source] {
        one x : StateH {
                x in stateh.hsm
                stateh.hsm' = stateh.hsm - x

				nameH.hsm' = nameH.hsm
                cstate.hsm' = cstate.hsm
                transitionh.hsm' = transitionh.hsm
                triggerH.hsm' = triggerH.hsm
                effectH.hsm' = effectH.hsm
                sourceH.hsm' = sourceH.hsm
                targetH.hsm' = targetH.hsm
				owner.hsm' = owner.hsm
        }
}

pred cstate_add[hsm,hsm' : Source] {
        one x : CState {
                x not in stateh.hsm
                cstate.hsm' = cstate.hsm + x

                nameH.hsm' = nameH.hsm
                stateh.hsm' = stateh.hsm
                transitionh.hsm' = transitionh.hsm
                triggerH.hsm' = triggerH.hsm
                effectH.hsm' = effectH.hsm
                sourceH.hsm' = sourceH.hsm
                targetH.hsm' = targetH.hsm
				owner.hsm' = owner.hsm
        }
}

pred cstate_del[hsm,hsm' : Source] {
        one x : CState {
                x in stateh.hsm
                cstate.hsm' = cstate.hsm - x

                nameH.hsm' = nameH.hsm
                stateh.hsm' = stateh.hsm
                transitionh.hsm' = transitionh.hsm
                triggerH.hsm' = triggerH.hsm
                effectH.hsm' = effectH.hsm
                sourceH.hsm' = sourceH.hsm
                targetH.hsm' = targetH.hsm
				owner.hsm' = owner.hsm
        }
}


pred nameH_set[hsm,hsm' : Source] {
        one x : StateH, y : String {
                x->y not in nameH.hsm
                x->y in nameH.hsm'

                stateh.hsm' = stateh.hsm
                cstate.hsm' = cstate.hsm
                transitionh.hsm' = transitionh.hsm
                triggerH.hsm' = triggerH.hsm
                effectH.hsm' = effectH.hsm
                sourceH.hsm' = sourceH.hsm
                targetH.hsm' = targetH.hsm
				owner.hsm' = owner.hsm
        }
}


pred owner_add[hsm,hsm' : Source] {
        one x : StateH, y : CState {
                x->y not in owner.hsm
                owner.hsm' = owner.hsm + x->y

                nameH.hsm' = nameH.hsm
                stateh.hsm' = stateh.hsm
                cstate.hsm' = cstate.hsm
                transitionh.hsm' = transitionh.hsm
                triggerH.hsm' = triggerH.hsm
                effectH.hsm' = effectH.hsm
                sourceH.hsm' = sourceH.hsm
                targetH.hsm' = targetH.hsm
        }
}

pred owner_del[hsm,hsm' : Source] {
        one x : StateH, y : CState {
                x->y in owner.hsm
                owner.hsm' = owner.hsm - x->y

                nameH.hsm' = nameH.hsm
                stateh.hsm' = stateh.hsm
                cstate.hsm' = cstate.hsm
                transitionh.hsm' = transitionh.hsm
                triggerH.hsm' = triggerH.hsm
                effectH.hsm' = effectH.hsm
                sourceH.hsm' = sourceH.hsm
                targetH.hsm' = targetH.hsm
        }
}


pred transition_add[hsm,hsm' : Source] {
        one x : TransitionH {
                x not in transitionh.hsm
                transitionh.hsm' = transitionh.hsm + x

                nameH.hsm' = nameH.hsm
                cstate.hsm' = cstate.hsm
                stateh.hsm' = stateh.hsm
                triggerH.hsm' = triggerH.hsm
                effectH.hsm' = effectH.hsm
                sourceH.hsm' = sourceH.hsm
                targetH.hsm' = targetH.hsm
				owner.hsm' = owner.hsm
        }
}

pred transition_del[hsm,hsm' : Source] {
        one x : TransitionH {
                x in transitionh.hsm
                transitionh.hsm' = transitionh.hsm - x

                nameH.hsm' = nameH.hsm
                cstate.hsm' = cstate.hsm
                stateh.hsm' = stateh.hsm
                triggerH.hsm' = triggerH.hsm
                effectH.hsm' = effectH.hsm
                sourceH.hsm' = sourceH.hsm
                targetH.hsm' = targetH.hsm
				owner.hsm' = owner.hsm
        }
}

pred source_set[hsm,hsm' : Source] {
        one x : TransitionH, y : StateH {
                x->y not in sourceH.hsm
                x->y in sourceH.hsm'

                stateh.hsm' = stateh.hsm
                cstate.hsm' = cstate.hsm
                transitionh.hsm' = transitionh.hsm
                triggerH.hsm' = triggerH.hsm
                effectH.hsm' = effectH.hsm
                nameH.hsm' = nameH.hsm
                targetH.hsm' = targetH.hsm
				owner.hsm' = owner.hsm
        }
}

pred target_set[hsm,hsm' : Source] {
        one x : TransitionH, y : StateH {
                x->y not in targetH.hsm
                x->y in targetH.hsm'

                stateh.hsm' = stateh.hsm
                cstate.hsm' = cstate.hsm
                transitionh.hsm' = transitionh.hsm
                triggerH.hsm' = triggerH.hsm
                effectH.hsm' = effectH.hsm
                nameH.hsm' = nameH.hsm
                sourceH.hsm' = sourceH.hsm
				owner.hsm' = owner.hsm
        }
}






--

pred state_add[nhsm,nhsm' : Target] {
        one x : StateN {
                x not in staten.nhsm
                staten.nhsm' = staten.nhsm + x

                nameN.nhsm' = nameN.nhsm
                transitionn.nhsm' = transitionn.nhsm
                triggerN.nhsm' = triggerN.nhsm
                effectN.nhsm' = effectN.nhsm
                sourceN.nhsm' = sourceN.nhsm
                targetN.nhsm' = targetN.nhsm
        }
}

pred state_del[nhsm,nhsm' : Target] {
        one x : StateN {
                x in staten.nhsm
                staten.nhsm' = staten.nhsm - x

                nameN.nhsm' = nameN.nhsm
                transitionn.nhsm' = transitionn.nhsm
                triggerN.nhsm' = triggerN.nhsm
                effectN.nhsm' = effectN.nhsm
                sourceN.nhsm' = sourceN.nhsm
                targetN.nhsm' = targetN.nhsm
        }
}


pred transition_add[nhsm,nhsm' : Target] {
        one x : TransitionN {
                x not in transitionn.nhsm
                transitionn.nhsm' = transitionn.nhsm + x

                nameN.nhsm' = nameN.nhsm
                staten.nhsm' = staten.nhsm
                triggerN.nhsm' = triggerN.nhsm
                effectN.nhsm' = effectN.nhsm
                sourceN.nhsm' = sourceN.nhsm
                targetN.nhsm' = targetN.nhsm
        }
}

pred transition_del[nhsm,nhsm' : Target] {
        one x : TransitionN {
                x in transitionn.nhsm
                transitionn.nhsm' = transitionn.nhsm - x

                nameN.nhsm' = nameN.nhsm
                staten.nhsm' = staten.nhsm
                triggerN.nhsm' = triggerN.nhsm
                effectN.nhsm' = effectN.nhsm
                sourceN.nhsm' = sourceN.nhsm
                targetN.nhsm' = targetN.nhsm
        }
}

pred source_set[nhsm,nhsm' : Target] {
        one x : TransitionN, y : StateN {
                x->y not in sourceN.nhsm
                x->y in sourceN.nhsm'

                staten.nhsm' = staten.nhsm
                transitionn.nhsm' = transitionn.nhsm
                triggerN.nhsm' = triggerN.nhsm
                effectN.nhsm' = effectN.nhsm
                nameN.nhsm' = nameN.nhsm
                targetN.nhsm' = targetN.nhsm
        }
}

pred target_set[nhsm,nhsm' : Target] {
        one x : TransitionN, y : StateN {
                x->y not in targetN.nhsm
                x->y in targetN.nhsm'

                staten.nhsm' = staten.nhsm
                transitionn.nhsm' = transitionn.nhsm
                triggerN.nhsm' = triggerN.nhsm
                effectN.nhsm' = effectN.nhsm
                nameN.nhsm' = nameN.nhsm
                sourceN.nhsm' = sourceN.nhsm
        }
}



fact {
        all i : Source, i' : i.next {
                state_add[i,i'] or state_del[i,i'] or transition_add[i,i'] or transition_del[i,i'] or
				nameH_set[i,i'] or source_set[i,i'] or source_set[i,i'] or owner_add[i,i'] or owner_del[i,i']
        }
}



fun Delta_Source [hsm,hsm' : Source] : Int {(#((stateh.hsm - stateh.hsm') + (stateh.hsm' - stateh.hsm))).plus[(#((nameH.hsm - nameH.hsm') + (nameH.hsm' - nameH.hsm))).plus[(#((owner.hsm - owner.hsm') + (owner.hsm' - owner.hsm)))].plus[(#((cstate.hsm - cstate.hsm') + (cstate.hsm' - cstate.hsm))).plus[(#((transitionh.hsm - transitionh.hsm') + (transitionh.hsm' - transitionh.hsm))).plus[(#((triggerH.hsm - triggerH.hsm') + (triggerH.hsm' - triggerH.hsm))).plus[(#((effectH.hsm - effectH.hsm') + (effectH.hsm' - effectH.hsm))).plus[(#((sourceH.hsm - sourceH.hsm') + (sourceH.hsm' - sourceH.hsm))).plus[(#((targetH.hsm - targetH.hsm') + (targetH.hsm' - targetH.hsm)))]]]]]]]}

fun Delta_Target [nhsm,nhsm' : Target] : Int {(#((staten.nhsm - staten.nhsm') + (staten.nhsm' - staten.nhsm))).plus[(#((nameN.nhsm - nameN.nhsm') + (nameN.nhsm' - nameN.nhsm))).plus[(#((transitionn.nhsm - transitionn.nhsm') + (transitionn.nhsm' - transitionn.nhsm))).plus[(#((triggerN.nhsm - triggerN.nhsm') + (triggerN.nhsm' - triggerN.nhsm))).plus[(#((effectN.nhsm - effectN.nhsm') + (effectN.nhsm' - effectN.nhsm))).plus[(#((sourceN.nhsm - sourceN.nhsm') + (sourceN.nhsm' - sourceN.nhsm))).plus[(#((targetN.nhsm - targetN.nhsm') + (targetN.nhsm' - targetN.nhsm)))]]]]]]}

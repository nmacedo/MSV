open HSM2NHSM
one sig S,S' extends Source {}


one sig T extends Target {}

one sig A,B,C extends StateH {}

fact { stateh.S = A + B + C + X }
fact { transitionh.S = T1 + T2 }
--fact { transitionh.S' = T1 + T2 + T3}

fact {((((A -> "Simple") -> S) + (((B -> "Sub1") -> S) + (((C -> "Sub2") -> S) + (((X -> "Comp") -> S))))) in nameH) && (nameH in ((((A -> "Simple") -> S) + (((B -> "Sub1") -> S) + (((C -> "Sub2") -> S) + (((X -> "Comp") -> S))))) + ((StateH -> String) -> (Source - S))))}

fact {((((B ->  X) -> S) + ((C ->  X) -> S)) in owner) && (owner in ((((B ->  X) -> S) + ((C ->  X) -> S)) + ((StateH -> CState) -> (Source - S))))}

one sig X extends CState {}

one sig T1,T2 extends TransitionH {}

fact {(triggerH in (((none -> none) -> none) + ((TransitionH -> String) -> (Source - S))))}

fact {(effectH in (((none -> none) -> none) + ((TransitionH -> String) -> (Source - S))))}

fact {(((T1 ->  X -> S) + (T2 ->  A -> S) in sourceH) && (sourceH in ((((T1 ->  X) -> S) + ((T2 ->  A) -> S))) + ((TransitionH -> StateH) -> (Source - S))))}

fact {(((T1 ->  A -> S) + (T2 ->  C -> S) in targetH) && (targetH in ((((T1 ->  A) -> S) + ((T2 ->  C) -> S))) + ((TransitionH -> StateH) -> (Source - S))))}

one sig A',B',C' extends StateN {}

fact {(A' -> "Simple" -> T + B' -> "Comp" -> T  + C' -> "New" -> T in nameN) && (nameN in A' -> "Simple" -> T + B' -> "Comp" -> T + C' -> "New" -> T)}

one sig T1',T2',T3' extends TransitionN {}

fact {(triggerN = ((none -> none) -> none))}

fact {(effectN = ((none -> none) -> none))}

fact {(T2' ->  A' -> T + T1' ->  B' -> T + T3' -> C' -> T in sourceN) && (sourceN in T2' ->  A' -> T + T1' ->  B' -> T  + T3' -> C' -> T )}

fact {(T2' ->  B' -> T + T1' ->  A' -> T  + T3' -> A' -> T in targetN) && (targetN in T2' ->  B' -> T + T1' ->  A' -> T  + T3' -> A' -> T )}

run {Check[S',T]} for 0 but 9 StateH,7 TransitionH,3 StateN,3 TransitionN, 1 Target, 5 Source

run {Check[S',T] && (Delta_Source[S,S'] = 5)} for 0 but 5 Int, 9 StateH,7 TransitionH,3 StateN,3 TransitionN, 1 Target, 2 Source

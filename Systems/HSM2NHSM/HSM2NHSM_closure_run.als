/*
 * Runner for HSM2NHSM transformation (with transitive closure)
 *
 * Model for the synchronization of hierarchical and non-hierarchical state machines, as
 * defined in the hsm2nhsm_closure.qvtr QVT-R bidirectional transformation.
 *
 * This version relies on a transformation defined with transitive closure over the state
 * hierarchy; an alternative version uses recursion. 
 *
 * It uses graph-edit distance to calculate the distance from the original model.
 *
 * Used as running example in
 * [1] N. Macedo and A. Cunha. Least-change bidirectional model transformation with QVT-R and ATL. SoSyM 2016
 * 
 * author: nmm, 10/2012
 */
open HSM2NHSM_closure as H2N

one sig HSM,HSM' extends Source {}
one sig NSM extends Target {}

one sig SM extends H2N/HSM/SMachine {}
one sig S1, S2, S3 extends H2N/HSM/State {}
one sig C extends H2N/HSM/CompositeState {}
one sig T1 extends H2N/HSM/Transition {}

one sig NM extends H2N/NHSM/SMachine {}
one sig S4, S5 extends H2N/NHSM/State {}
one sig T2, T3 extends H2N/NHSM/Transition {}

fact Instances {
	SMachine_.HSM = SM
	State_.HSM = S1+S2+S3+C
	Transition_.HSM = T1
	states.HSM = SM -> (S1+S2+S3+C)
	container.HSM = (S2+S3) -> C
	SMachine<:name.HSM = SM -> "Machine"
	State<:name.HSM = S1->"Idle" + S2->"Waiting" + S3->"Running" + C->"Active"
	source.HSM = T1 -> S1
	target.HSM = T1 -> S2

	SMachine_.NSM =NM
	State_.NSM = S4 + S5
	Transition_.NSM = T2+T3
	states.NSM = NM -> (S4+S5)
	SMachine<:name.NSM = NM -> "Machine"
	State<:name.NSM = S4->"Idle" + S5->"Active"
	source.NSM = T2 -> S4 + T3 -> S5
	target.NSM = T2 -> S5 + T3 -> S4

}

run {HSM2NHSM[HSM',NSM] && (H2N/HSM/Delta[HSM,HSM'] = 3)} for 10

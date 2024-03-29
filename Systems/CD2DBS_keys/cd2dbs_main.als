/*
 * CD2DBS transformation instance
 *
 * Instance for the object/relational mapping, as defined in the uml2rdbms_simple.qvtr
 * QVT-r transformation.
 *
 * Demonstration of the models generated by the CD2DBS QVT-r bidirectional transformation.
 *
 * Used as running example in
 * [1] N. Macedo, T. Guimarães and A. Cunha. Model repair and transformation with Echo. ASE 2013
 * 
 * author: N. Macedo, 10/2012
 */
module cd2dbs_main

open cd2dbs [Model]
open cd_inst[Model]
open dbs_inst[Model]

abstract sig Model{}

one sig C1 extends CD {}
one sig C2 extends CD {}
one sig D1 extends DBS {}

fact {
	C1_Def[C1]
	D1_Def[D1]
}



/*
run {Check[S',T] && Delta_CD[S,S'] = 3} for 13 Class, 13 Attribute, 4 Package, 3 Int, 1 Schema, 10 Table, 5 Column, 1 S, 1 S', 1 T
run {Check[S',T] && Delta_CD[S,S'] = 2} for 12 Class, 12 Attribute, 3 Package, 3 Int, 1 Schema, 10 Table, 5 Column, 1 S, 1 S', 1 T
run {Check[S',T] && Delta_CD[S,S'] = 1} for 11 Class, 11 Attribute, 2 Package, 2 Int, 1 Schema, 10 Table, 5 Column, 1 S, 1 S', 1 T
run {Check[S',T] && Delta_CD[S,S'] = 0} for 10 Class, 10 Attribute, 1 Package, 2 Int, 1 Schema, 10 Table, 5 Column, 1 S, 1 S', 1 T
*/

run {Check[C2,D1] && Delta_CD[C1,C2] = 7} for 10 but 3 Model, 1 DBS, 2 CD
--run {Check[S',T] && Delta_CD[S,S'] = 2} for 26 Class, 26 Attribute, 3 Package, 3 Int, 1 Schema, 12 Table, 24 Column, 1 S, 1 S', 1 T
--run {Check[S',T] && Delta_CD[S,S'] = 1} for 25 Class, 25 Attribute, 2 Package, 2 Int, 1 Schema, 12 Table, 24 Column, 1 S, 1 S', 1 T
--run {Check[S',T] && Delta_CD[S,S'] = 0} for 24 Class, 24 Attribute, 1 Package, 2 Int, 1 Schema, 12 Table, 24 Column, 1 S, 1 S', 1 T

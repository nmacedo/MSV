/*
 * Simplified CD2DBS bidirectional transformation
 *
 * Model for the object/relational mapping, as defined in the uml2rdbms_keys.qvtr QVT-r transformation.
 *
 * Demonstration of the models generated by the simplified CD2DBS QVT-r bidirectional transformation.
 *
 * Used as running example in
 * [1] N. Macedo and A. Cunha. Implementing QVT-R bidirectional model transformations using Alloy. FASE 2013
 * 
 * author: N. Macedo, 10/2012
 */
 module cd2dbs[Model]

open CD [Model]
open DBS [Model]
open util/integer

one sig Aux {
  p2s_DBS,p2s_CD : CD -> DBS -> Package -> Schema,
  a2c_DBS,a2c_CD : CD -> DBS -> Class -> Table,
  c2t_DBS,c2t_CD : CD -> DBS -> Class -> Table
}

pred Pattern_P2S_CD [cd : CD, p : Package, pn : String] {pn in p.(name.cd)}

pred Pattern_P2S_DBS [ds : DBS,s : Schema,pn : String] {pn in s.(name.ds)}

pred Check_P2S_CD [cd : CD,ds : DBS] {When_P2S_CD[cd,ds] => (all p : Package_.cd,pn : String | Pattern_P2S_CD[cd,p,pn] => (some s : Schema_.ds | Pattern_P2S_DBS[ds,s,pn] && Where_P2S_CD[cd,ds]))}

pred Check_P2S_DBS [cd : CD,ds : DBS] {When_P2S_DBS[cd,ds] => (all s : Schema_.ds,pn : String | Pattern_P2S_DBS[ds,s,pn] => (some p : Package_.cd | Pattern_P2S_CD[cd,p,pn] && Where_P2S_DBS[cd,ds]))}

fact {Aux.p2s_DBS = {cd : CD,ds : DBS,p : Package_.cd,s : Schema_.ds | When_P2S_DBS[cd,ds] => (all pn : String | Pattern_P2S_DBS[ds,s,pn] => Pattern_P2S_CD[cd,p,pn] && Where_P2S_DBS[cd,ds])}}

fact {Aux.p2s_CD = {cd : CD,ds : DBS,p : Package_.cd,s : Schema_.ds | When_P2S_CD[cd,ds] => (all pn : String | Pattern_P2S_CD[cd,p,pn] => Pattern_P2S_DBS[ds,s,pn]&& Where_P2S_CD[cd,ds])}}

pred When_P2S_CD [cd : CD,ds : DBS] {no none}

pred When_P2S_DBS [cd : CD,ds : DBS] {no none}

pred Where_P2S_CD [cd : CD,ds : DBS] {no none}

pred Where_P2S_DBS [cd : CD,ds : DBS] {no none}

pred Pattern_C2T_CD [cd : CD,p : Package,c : Class,cn : String] {(c in persistent.cd) && (((p in c.(~(classes.cd)))) && (cn in c.(name.cd)))}

pred Pattern_C2T_DBS [ds : DBS,s : Schema,t : Table,cn : String] {((s in t.(~(tables.ds)))) && (cn in t.(name.ds))}

pred Check_C2T_CD [cd : CD,ds : DBS] {all p : Package,s : Schema | When_C2T_CD[cd,ds,p,s] => (all c : Class_.cd,cn : String | Pattern_C2T_CD[cd,p,c,cn] => (some t : Table_.ds | Pattern_C2T_DBS[ds,s,t,cn] && Where_C2T_CD[cd,ds,c,t]))}

pred Check_C2T_DBS [cd : CD,ds : DBS] {all p : Package,s : Schema | When_C2T_DBS[cd,ds,p,s] => (all t : Table_.ds,cn : String | Pattern_C2T_DBS[ds,s,t,cn] => (some c : Class_.cd | Pattern_C2T_CD[cd,p,c,cn] && Where_C2T_DBS[cd,ds,c,t]))}

fact {Aux.c2t_DBS = {cd : CD,ds : DBS,c : Class_.cd,t : Table_.ds | all p : Package_.cd,s : Schema_.ds | When_C2T_DBS[cd,ds,p,s] => (all cn : String | Pattern_C2T_DBS[ds,s,t,cn] => Pattern_C2T_CD[cd,p,c,cn] && Where_C2T_CD[cd,ds,c,t])}}

fact {Aux.c2t_CD = {cd : CD,ds : DBS,c : Class_.cd,t : Table_.ds | all p : Package_.cd,s : Schema_.ds | When_C2T_CD[cd,ds,p,s] => (all cn : String | Pattern_C2T_CD[cd,p,c,cn] => Pattern_C2T_DBS[ds,s,t,cn] && Where_C2T_DBS[cd,ds,c,t])}}

pred When_C2T_CD [cd : CD,ds : DBS,p : Package,s : Schema] { p->s in Aux.p2s_CD[cd,ds]}

pred When_C2T_DBS [cd : CD,ds : DBS,p : Package,s : Schema] { p->s in Aux.p2s_DBS[cd,ds]}

pred Where_C2T_CD [cd : CD,ds : DBS,c : Class,t : Table] { c->t in Aux.a2c_CD[cd,ds]}

pred Where_C2T_DBS [cd : CD,ds : DBS,c : Class,t : Table] {c->t in Aux.a2c_DBS[cd,ds]}

pred Pattern_A2C_CD [cd : CD,c : Class,cn : String,a : Attribute,g : Class] {(((g in c.^{x : univ,v0 : x.(general.cd) | no none}) || (g = c)) && (a in g.(attributes.cd))) && (cn in a.(name.cd))}

pred Pattern_A2C_DBS [ds : DBS,cl : Column,t : Table,cn : String] {(cn in cl.(name.ds)) && (cl in t.(columns.ds))}

pred Check_A2C_CD [cd : CD,ds : DBS] {When_A2C_CD[cd,ds] => (all c : Class_.cd,cn : String,a : Attribute_.cd,g : Class_.cd | Pattern_A2C_CD[cd,c,cn,a,g] => (some cl : Column_.ds,t : Table_.ds | Pattern_A2C_DBS[ds,cl,t,cn] && Where_A2C_CD[cd,ds]))}

pred Check_A2C_DBS [cd : CD,ds : DBS] {When_A2C_DBS[cd,ds] => (all cl : Column_.ds,t : Table_.ds,cn : String | Pattern_A2C_DBS[ds,cl,t,cn] => (some c : Class_.cd,a : Attribute_.cd,g : Class_.cd | Pattern_A2C_CD[cd,c,cn,a,g] && Where_A2C_DBS[cd,ds]))}

fact {Aux.a2c_DBS = {cd : CD,ds : DBS,c : Class_.cd,t : Table_.ds | When_A2C_DBS[cd,ds] => (all cl : Column_.ds,cn : String | Pattern_A2C_DBS[ds,cl,t,cn] => (some a : Attribute_.cd,g : Class_.cd | Pattern_A2C_CD[cd,c,cn,a,g] && Where_A2C_DBS[cd,ds]))}}

fact {Aux.a2c_CD = {cd : CD,ds : DBS,c : Class_.cd,t : Table_.ds | When_A2C_CD[cd,ds] => (all cn : String,a : Attribute_.cd,g : Class_.cd | Pattern_A2C_CD[cd,c,cn,a,g] => (some cl : Column_.ds | Pattern_A2C_DBS[ds,cl,t,cn] && Where_A2C_CD[cd,ds]))}}

pred When_A2C_CD [cd : CD,ds : DBS] {}

pred When_A2C_DBS [cd : CD,ds : DBS] {}

pred Where_A2C_CD [cd : CD,ds : DBS] {}

pred Where_A2C_DBS [cd : CD,ds : DBS] {}




pred Top_P2S [cd : CD,ds : DBS] {Check_P2S_CD[cd,ds] && Check_P2S_DBS[cd,ds]}

pred Top_C2T [cd : CD,ds : DBS] {Check_C2T_CD[cd,ds] && Check_C2T_DBS[cd,ds]}

pred Check [cd : CD,ds : DBS] {Top_P2S[cd,ds] && Top_C2T[cd,ds]}


// ***
// *** Deltas ***
// ***
fun Delta_CD [cd,cd' : CD] : Int {
  (#((NamedEntity_.cd - NamedEntity_.cd') + (NamedEntity_.cd' - NamedEntity_.cd))).plus[
  (#((name.cd - name.cd') + (name.cd' - name.cd))).plus[
  (#((persistent.cd - persistent.cd') + (persistent.cd' - persistent.cd))).plus[
  (#((classes.cd - classes.cd') + (classes.cd' - classes.cd))).plus[
  (#((attributes.cd - attributes.cd') + (attributes.cd' - attributes.cd))).plus[
  (#((general.cd - general.cd') + (general.cd' - general.cd)))]]]]]
}

fun Delta_DBS [ds,ds' : DBS] : Int {
  (#((NamedEntity_.ds - NamedEntity_.ds') + (NamedEntity_.ds' - NamedEntity_.ds))).plus[
  (#((name.ds - name.ds') + (name.ds' - name.ds))).plus[
  (#((columns.ds - columns.ds') + (columns.ds' - columns.ds))).plus[
  (#((tables.ds - tables.ds') + (tables.ds' - tables.ds)))]]]
}

// ***
// *** Edit operations ***
// ***
/*pred addClass [p:Package,n:String,s,s' : CD]{
  some c : Class | {
     c not in class.s
     class.s' = class.s + c
     nameC.s' = nameC.s + c -> n
     namespace.s' = namespace.s + c -> p

     general.s' = general.s
     persistent.s' = persistent.s
     package.s = package.s'
     nameP.s = nameP.s'
     attribute.s = attribute.s'
     attributes.s = attributes.s'
     name.s = nameA.s'}
}

pred remClass [p:Package,n:String,s,s' : CD]{
  some c : Class | {
     c in class.s
     class.s' = class.s - c
     c -> n in nameC.s
     nameC.s' = nameC.s - c -> n
     c -> p in namespace.s
     namespace.s' = namespace.s - c -> p
     general.s' = class.s'<:general.s:>class.s'
     persistent.s' = persistent.s - c

     package.s = package.s'
     nameP.s = nameP.s'
     attribute.s = attribute.s'
     attributes.s = attributes.s'
     nameA.s = nameA.s' }
}

pred addAttribute [c:Class,n:String,s,s' : CD]{
  some a : Attribute | {
     a not in attribute.s
     attribute.s' = attribute.s + a
     nameA.s' = nameA.s + a -> n
     attributes.s' = attributes.s + c -> a

     general.s' = general.s
     persistent.s' = persistent.s
     package.s = package.s'
     nameP.s = nameP.s'
     class.s = class.s'
     namespace.s = namespace.s'
     nameC.s = nameC.s' }
}

pred remAttribute [c:Class,n:String,s,s' : CD]{
  some a : Attribute | {
     a in attribute.s
     attribute.s' = attribute.s - a
     a -> n in nameA.s
     nameA.s' = nameA.s - a -> n
     c -> a in attributes.s
     attributes.s' = attributes.s - c -> a

     general.s' = general.s
     persistent.s' = persistent.s
     package.s = package.s'
     nameP.s = nameP.s'
     class.s = class.s'
     namespace.s = namespace.s'
     nameC.s = nameC.s' }
}

pred setPersistent [c:Class,s,s' : CD]{
     c not in persistent.s
     persistent.s' = persistent.s + c

     class.s' = class.s
     nameC.s' = nameC.s
     namespace.s' = namespace.s
     general.s' = general.s
     package.s = package.s'
     nameP.s = nameP.s'
     attribute.s = attribute.s'
     attributes.s = attributes.s'
     nameA.s = nameA.s'
}

pred addGeneral [c,c':Class,s,s' : CD]{
     c -> c' not in general.s
     general.s' = general.s + c -> c'
    
     class.s' = class.s
     nameC.s' = nameC.s
     namespace.s' = namespace.s
     general.s' = general.s
     package.s = package.s'
     nameP.s = nameP.s'
     attribute.s = attribute.s'
     attributes.s = attributes.s'
     nameA.s = nameA.s' 
}

pred remGeneral [c,c':Class,s,s' : CD]{
     c -> c' in general.s
     general.s' = general.s - c -> c'
    
     class.s' = class.s
     nameC.s' = nameC.s
     namespace.s' = namespace.s
     general.s' = general.s
     package.s = package.s'
     nameP.s = nameP.s'
     attribute.s = attribute.s'
     attributes.s = attributes.s'
     nameA.s = nameA.s' 
}

pred setNameClass [c:Class,n:String,s,s' : CD]{
     nameC.s' = nameC.s ++ c -> n
  
     general.s' = general.s    
     class.s' = class.s
     namespace.s' = namespace.s
     general.s' = general.s
     package.s = package.s'
     nameP.s = nameP.s'
     attribute.s = attribute.s'
     attributes.s = attributes.s'
     nameA.s = nameA.s'
}

pred setNameAttribute [a:Attribute,n:String,s,s' : CD]{
     nameA.s' = nameA.s ++ a -> n
  
     general.s' = general.s    
     class.s' = class.s
     namespace.s' = namespace.s
     general.s' = general.s
     package.s = package.s'
     nameP.s = nameP.s'
     attribute.s = attribute.s'
     attributes.s = attributes.s'
     nameC.s = nameC.s'
}

pred setNamePackage [p:Package,n:String,s,s' : CD]{
     nameP.s' = nameP.s ++ p -> n
  
     general.s' = general.s    
     class.s' = class.s
     namespace.s' = namespace.s
     general.s' = general.s
     package.s = package.s'
     nameC.s = nameC.s'
     attribute.s = attribute.s'
     attributes.s = attributes.s'
     nameA.s = nameA.s'
}

fact { all m : S, m' : S' | {
          some p:package.m, n:String | setNamePackage[p,n,m,m'] or
          some c:class.m,n:String | setNameClass[c,n,m,m'] or
          some a:attribute.m,n:String | setNameAttribute[a,n,m,m'] or
          some p:package.m,n:String | addClass[p,n,m,m'] or
          some p:package.m,n:String | remClass[p,n,m,m'] or
          some c,c':class.m | addGeneral[c,c',m,m'] or
          some c,c':class.m | remGeneral[c,c',m,m'] or
          some c:class.m | setPersistent[c,m,m'] or
          some c:class.m,n:String | remAttribute[c,n,m,m'] or
          some c:class.m,n:String | addAttribute[c,n,m,m']
          some p:package.m,n:String | addClass[p,n,m,m']
}}*/

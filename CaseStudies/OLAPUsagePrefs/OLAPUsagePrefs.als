/**
@author: Mariana Carvalho, Nuno Macedo
**/
module OLAPCube

/** Data tables **/

-- a table of data, contained certain fields that are either measures or attributes
-- each table may be related to others, abstracting away foreign keys
abstract sig Table {
	related : set Table,
	fields : some Field
} {
	-- cannot point to itself
	this not in related
}

-- fact tables, contain measures and may be related to other fact tables and dimensions
sig FactTable extends Table {} {
	fields in Measure
}

-- dimensions, contain attributes and may be related to fact tables
sig Dimension extends Table {} {
	fields in Attribute
}

-- the tables' fields, may be measures (for table facts) or attributes (for dimensions)
abstract sig Field {} {
	-- avoid unreachable fields and duplicates
	one this.~fields
}
sig Measure, Attribute extends Field {}

/** OLAP cube **/

-- the parameters introduced by the user to generate the cube
one sig CubeParameters {
	-- the selected tables
	tabs : set Table
}

-- the OLAP cube 
one sig OLAPCube {
	struct : one MiningStructure,
	flds : set Field
}

-- the OLAP cube is built from the fields of the selected tables
pred ConstructCube[c : OLAPCube, p : CubeParameters] {
	c.flds = p.tabs.fields
}

/** Rules **/ 

-- the cube's mining structure
one sig MiningStructure {   
	model : one MiningModel
}

-- the mining structure model, containing the rules and preferences
-- TODO: do strong rules and preferences belong here?
one sig MiningModel {
	rules : set Rule,
	strongRules : set rules,
	preferences : set Preference,
	itemSets : set Field 
} {
	itemSets = rules.is + rules.o
}

-- a rule from some fields to a single field, with a performance measure
sig Rule {
	is : some Field,
	o : one Field,
	performance : one Performance
}

-- the performance of a rule, abstracted, should be extracted from the data
sig Performance {
	supp : Int, 
	conf : Int
} {
	gte[conf,0]
	gte[supp,0]
}

-- generation axiom for field subsets
-- this sig is needed to create the powerset of the available fields so
-- that every rule can be created, since there aren't higher-order quantifiers
-- NOTE: scopes must be controlled with care, with 2^#Fields == #Subset
sig SubsetFields {
	elems : set Field
} {
	all s : SubsetFields | s.@elems = elems => s = this
}

-- constructs the rules from a OLAPCube
-- these are built from the fields of the selected tables that are related
pred ConstructRules[c : OLAPCube, p : CubeParameters] {
	-- the cube is constructed 
	ConstructCube[c,p]
	-- for every field of the cube, there a rule with every combination of related fields as input 
	all f : c.flds, s : SubsetFields | some s.elems && s.elems in related[f,p] =>
		some r : c.struct.model.rules | r.o = f && r.is = s.elems
	all r : (c.struct.model.rules) {
		-- there are no rules for fields outside the cube
 		some f : c.flds | r.is in related[f,p]
		-- there are no repeated rules
		all r' : (c.struct.model.rules) - r | r.is != r'.is || r.o != r'.o
	}
}

-- for a given field, retrieves every other field that is reachable by
-- related tables that have been selected by the user
fun related[f:Field,p:CubeParameters] : set Field {
	((f.~fields&p.tabs).*(p.tabs<:related:>p.tabs)).fields - f
}

-- tests whether the rules of a cube are correct
pred RulesCorrect [c : OLAPCube] {
	-- at least one rule must be created
	some c.struct.model.rules
	-- the elements of the rules belong to the cube
	c.struct.model.rules.(is+o) in c.flds
	-- all the elements of a rule are different
	all r : c.struct.model.rules | r.o not in r.is
}

-- defines what are good parameters
pred GoodCubeParameters[p:CubeParameters] {
	-- there are at least some related fields
	some f : p.tabs.fields | some related[f,p]
}

-- an example of cube and rule construction
run {
	some c : OLAPCube, p : CubeParameters | GoodCubeParameters[p] && ConstructRules[c,p]
} for 20 but 2 Table, exactly 4 Field, exactly 16 SubsetFields

-- asserts whether the rules constructed for a cube are correct
assert CheckRules {
	all c : OLAPCube, p : CubeParameters | 
		(GoodCubeParameters[p] && ConstructRules[c,p]) => RulesCorrect[c]
}  

-- checks the correctness rule construction
check CheckRules 
for 8 but 4 Table, exactly 5 Field, exactly 32 SubsetFields

/** Strong rules **/

-- the parameters introduced by the user to generate the preferences
one sig PreferenceParameters {
	-- the minimal confidence value
	conf : one Int,
	-- the minimal support value
	supp : one Int,
	-- the selected attribute
	attr : one Attribute
} {
	gte[conf,0]
	gte[supp,0]
}

-- constructs the strong rules for an OLAP cube
pred ConstructStrongRules[c : OLAPCube, p:PreferenceParameters] {
	-- filter the rules that contain the selected atrribute and whose performance pass the thresholds
	c.struct.model.strongRules = {r : c.struct.model.rules | 
		p.attr in (r.is + r.o) && gte[r.performance.supp,p.supp] && gte[r.performance.conf,p.conf] }
}

-- an example of strong rule filtering
run {
	some c:OLAPCube,p1:CubeParameters,p2:PreferenceParameters | 
		GoodCubeParameters[p1] && ConstructRules[c,p1] && ConstructStrongRules[c,p2] && GoodPreferenceParameters[c,p1,p2]
} for 6 but 4 Table, exactly 5 Field, exactly 32 SubsetFields 

-- tests whether the strong rules of a cube are correct
pred StrongRulesCorrect [c : OLAPCube, p : PreferenceParameters] {
	-- there is at least a rule
	some c.struct.model.strongRules
	-- the selected attribute is in every rule
	p.attr in c.struct.model.strongRules.(is+o)
	-- the strong rules are among the regular rules
	c.struct.model.strongRules in c.struct.model.rules
	-- the performance of the strong rules is above the threshold
	all r : c.struct.model.strongRules.performance | gte[r.supp,p.supp] && gte[r.conf,p.conf]
}

-- achieve a correct preference extraction
pred GoodPreferenceParameters[c:OLAPCube,p1:CubeParameters,p2:PreferenceParameters] {
	-- the selected parameter must belong to the cube
	p2.attr in c.flds
	-- there is some rule that passes the thersholds
	some r : c.struct.model.strongRules.performance | gte[r.supp,p2.supp] && gte[r.conf,p2.conf]
}

-- asserts whether the filtered strong rules are correct
assert CheckStrongRules {
	all c:OLAPCube,p1:CubeParameters,p2:PreferenceParameters | 
		(GoodCubeParameters[p1] && ConstructRules[c,p1] && ConstructStrongRules[c,p2] && 
GoodPreferenceParameters[c,p1,p2] && ConstructPreferences[c]) => 
			StrongRulesCorrect[c,p2]
}  

-- checks the correctness of strong rule creation
check CheckStrongRules
for 3 but 2 Table, exactly 4 Field, exactly 16 SubsetFields, 2 Int

/** Preferences **/

-- preferences derived from a rule
sig Preference {
	flds : set Field,
	sourceRule : one Rule
}

-- constructs the preferences
pred ConstructPreferences [c : OLAPCube] {
	-- a preference contains the attributes of the origin rule
	all p : c.struct.model.preferences | p.flds = p.sourceRule.(is+o)
	-- there are no duplicate preferences
	all p1,p2 : c.struct.model.preferences | p1.sourceRule = p2.sourceRule => p1 = p2
	-- there is a preference for every strong rule
	c.struct.model.strongRules = c.struct.model.preferences.sourceRule
}


-- an example of preference extraction
run {
	some FactTable
	some related 
	#tabs = 2
	some c:OLAPCube,p1:CubeParameters,p2:PreferenceParameters | 
		GoodCubeParameters[p1] && ConstructRules[c,p1] && ConstructStrongRules[c,p2] && 
		GoodPreferenceParameters[c,p1,p2] && ConstructPreferences[c]
} for 5 but 2 Table, exactly 3 Field, exactly 8 SubsetFields 

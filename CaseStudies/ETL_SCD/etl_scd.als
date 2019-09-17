/**
@author: Bruno Oliveira, Nuno Macedo
**/
open util/ordering[State]

sig State {}

/** Data objects **/
sig Value {}

abstract sig Field {}
sig SKField, ControlField, VariationField, DescriptiveField extends Field {}
sig DateField, OperationField, ErrorField extends ControlField {}

sig Row {
	values : Field -> lone Value
}

// the only thing that evolves in time are the rows assigned to the objects
abstract sig DataObject {
	// the fields of the data object
	fields: some Field,
	// the key fields, selected from the fields of the data object
	keys : some fields & SKField,
	// the rows contained in the data object  in each moment
	rows : Row -> State
} 

// properties of the data objects that are enforced
fact dataObject {
	all o : DataObject | o.keys in o.fields
	// rows only contain fields of their parent data object
	all s : State, o : DataObject, r : o.rows.s | r.values.Value = o.fields
	// fields belong to a single data object
	all f : Field | one fields.f
}

// the consistency constraints that are expected to hold for data objects
// the operations should not break these properties
pred consistentDataObject[s:State,o:DataObject] {
	// key fields are never empty
	all f : o.keys, r : o.rows.s | one f.(r.values)
	// key field values are unique
	all r1,r2 : o.rows.s | (all f : o.keys | f.(r1.values) = f.(r2.values)) => r1 = r2
}

run consistentDataObject for 5 but 1 State, 2 DataObject, 0 Mapping

/** Table mappings **/

sig Mapping {
	inData : one DataObject,
	outData : one DataObject - inData,
	association : Field -> Field
}

// properties of the mappings that are enforced
fact mapping {
	// associations relate fields from the in and out data objects
	all m:Mapping | m.association in m.inData.fields -> m.outData.fields
}

// the consistency constraints that are expected to hold for mappings
// the operations should not break these properties
pred consistentMapping[s:State,m:Mapping] {
	// the mapped tables are consistent data objects
	consistentDataObject[s,m.inData]
	consistentDataObject[s,m.outData]
	// the keys of the out data object associated with the in data object exist
	all ro : m.outData.(rows.s) | some ri : m.inData.(rows.s) |
		all f : Field.(m.association) & m.outData.keys |
			f.(ro.values) = ((m.association).f).(ri.values)

}

run consistentMapping 
for 5 but 1 State, exactly 1 HistoryTable, exactly 1 DimensionTable, 2 DataObject, 1 Mapping

abstract sig Pattern{}
abstract sig TransformationPattern extends Pattern{}


/** Dimension tables **/

// each table has specific classes of fields that are relevant for the procedure
sig AuditTable extends DataObject {
	a_dates : some fields & DateField,
	a_ops : some fields & OperationField,
	a_vars : some fields & VariationField
} { a_dates & a_ops = none && a_dates & a_vars = none && a_ops & a_vars = none }

sig DimensionTable extends DataObject {
	d_vars : some fields & VariationField
}

sig HistoryTable extends DataObject {
	h_vars : some fields & VariationField,
	h_dates : some fields & DateField
} { h_vars & h_dates = none }

/** Concrete pattern **/
sig SCD {
	dimension2audit : one Mapping,
	dimension2history : one Mapping
}

// properties of the SCD that are enforced
fact scd {
	all scd : SCD {
		// dimension2audit maps an audit table to a dimension table
		scd.dimension2audit.inData in DimensionTable
		scd.dimension2audit.outData in AuditTable
		let i = (scd.dimension2audit.inData), 
		 	o = (scd.dimension2audit.outData) {
			// variable fields are mapped to variable fields
			(scd.dimension2audit.association).(o.a_vars) in i.d_vars
			// every key field is mapped to key fields
			(scd.dimension2audit.association).(o.keys) = i.keys
--			(i.keys).(dimension2audit.association) = o.keys
		}
		// dimension2history maps a dimension table to a history table
		scd.dimension2history.inData in DimensionTable
		scd.dimension2history.outData in HistoryTable
		let i = (scd.dimension2history.inData), 
			 o = (scd.dimension2history.outData) {
			// variable fields are mapped to variable fields
			(scd.dimension2history.association).(o.h_vars) in i.d_vars
			// every key field is mapped to key fields
			(scd.dimension2history.association).(o.keys) = i.keys
--			(i.keys).(dimension2history.association) = o.keys
		}
	}
}

// the consistency constraints that are expected to hold for SCDs
// the operations should not break these properties
pred consistentSCD[s:State,x:SCD] {
	// the mappings comprising the SCD are consistent
	// and as a consequence, the data objects are also consistent
	consistentMapping[s,x.dimension2audit]
	consistentMapping[s,x.dimension2history]
}

/** State evolution **/

// adds a row to the audit table
pred addAudit [s,s': State, r : Row, scd : SCD] {
	// pre-conditions
	// the row does not exist in the audit table
	r not in scd.dimension2audit.outData.rows.s
	// the keys of the new row are unique
	no r1 : scd.dimension2audit.outData.rows.s | 
		(all f : scd.dimension2audit.outData.keys | f.(r1.values) = f.(r.values))

	// post-conditions
	// the new row is added to the audit table
	scd.dimension2audit.outData.rows.s' = scd.dimension2audit.outData.rows.s + r

	// frame conditions
	// the remainder data objects remain unchanged
	scd.dimension2history.outData.rows.s' = scd.dimension2history.outData.rows.s
	scd.dimension2history.inData.rows.s' = scd.dimension2history.inData.rows.s

}

run addAudit
for 16 but 2 State, 3 DataObject, 2 Mapping, 3 DataObject

// checks that adding a row to the audit table does not break the SCD consistency
assert addAuditCorrect {
	all s:State,s':s.next,scd:SCD,r:Row | 
		(consistentDataObject[s,scd.dimension2audit.outData] && addAudit[s,s',r,scd]) =>
		consistentDataObject[s',scd.dimension2audit.outData]
}

check addAuditCorrect for 10 but exactly 1 SCD, exactly 2 State, 2 Mapping, 3 DataObject

// adds a row to the dimension table from the audit table
pred addDimension [s,s': State, r : Row, scd : SCD] {
	// pre-conditions
	// there is a row in the audit table to be moved
	r in scd.dimension2audit.outData.rows.s
	// the keys of the audit row are unique for the dimension table
	// otherwise, an update should be applied
	no r1 : scd.dimension2audit.inData.(rows.s) |
		all f : Field.(scd.dimension2audit.association) & scd.dimension2audit.outData.keys |
			f.(r.values) = ((scd.dimension2audit.association).f).(r1.values)

	// post-conditions
	some r' : Row {
		// there is a row that is not yet in the dimension table
 		r' not in scd.dimension2audit.inData.rows.s
		// such that the fields associated with the audit row are identical
		let assoc = scd.dimension2audit.association |
		all f : Field.assoc | f.(r'.values) = (assoc.f).(r.values)
		// that will be added to the dimension table
		scd.dimension2audit.inData.rows.s' = scd.dimension2audit.inData.rows.s + r'
	}
	// the audit row is removed from the audit table
	scd.dimension2audit.outData.rows.s' = scd.dimension2audit.outData.rows.s - r

	// frame conditions
	// the history table remains unchanged
	scd.dimension2history.outData.rows.s' = scd.dimension2history.outData.rows.s
}

run addDimension 
for 10 but 2 State, 3 DataObject, 2 Mapping, 3 DataObject

// checks that adding a row to the dimension table, after an insertion in the audit table,
// does not break the SCD consistency
assert addDimensionCorrect {
	all s:State,s':s.next,s'':s'.next,scd:SCD,r,r':Row | 
		(consistentSCD[s',scd] &&
		addAudit[s,s',r,scd] &&
		addDimension[s',s'',r',scd]) => consistentSCD[s'',scd]
}

check addDimensionCorrect for 10 but exactly 1 SCD, exactly 3 State, 2 Mapping, 3 DataObject

pred updateDimension [s,s': State, r : Row, scd : SCD] {
	// pre-conditions
	// there is a row in the audit table to be moved
	r in scd.dimension2audit.outData.rows.s

	// post-conditions
	some rd : scd.dimension2audit.inData.(rows.s), rd',rh' : Row {
		// the keys of the audit row overlap with those of a dimension row
		all f : Field.(scd.dimension2audit.association) & scd.dimension2audit.outData.keys |
			f.(r.values) = ((scd.dimension2audit.association).f).(rd.values)
		// there is a new dimension row that will be added
 		rd' not in scd.dimension2audit.inData.rows.s
		scd.dimension2audit.inData.rows.s' = scd.dimension2audit.inData.rows.s + rd' - rd
		// whose associated values are identical to those of the audit row
		let assoc = scd.dimension2audit.association |
		all f : Field.assoc | f.(r.values) = (assoc.f).(rd'.values)
		// there is a new history row that will be added
 		rh' not in scd.dimension2history.outData.rows.s
		scd.dimension2history.outData.rows.s' = scd.dimension2history.outData.rows.s + rh'
		// whose associated values are identical to those of the dimension row
		all f : Field.(scd.dimension2history.association) & scd.dimension2history.outData.keys |
			f.(rh'.values) = ((scd.dimension2history.association).f).(rd.values)
		// as long as the keys do not overlap with existing history rows
		no rh : scd.dimension2history.outData.rows.s | 
			(all f : scd.dimension2history.outData.keys | f.(rh.values) = f.(rh'.values))

	}
	// the audit row is removed from the audit table
	scd.dimension2audit.outData.rows.s' = scd.dimension2audit.outData.rows.s - r

	// frame conditions
	// every data object is changed
}

run updateDimension 
for 10 but 2 State, 3 DataObject, 2 Mapping, 3 DataObject

// checks that updating a row in the dimension table, after an insertion in the audit table,
// does not break the SCD consistency
assert updateDimensionCorrect {
	all s:State,s':s.next,s'':s'.next,scd:SCD,r,r':Row | 
		(consistentSCD[s',scd] &&
		addAudit[s,s',r,scd] &&
		updateDimension[s',s'',r',scd]) => consistentSCD[s'',scd]
}

check updateDimensionCorrect for 5 but exactly 1 SCD, exactly 3 State, 2 Mapping, 3 DataObject

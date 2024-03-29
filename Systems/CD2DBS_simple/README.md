# Object-relational mapping (without associations/keys)

A simplified version of the [object-relational mapping](https://en.wikipedia.org/wiki/Object%E2%80%93relational_mapping) in EMF along with models demonstrating a solver-based approach to bidirectional transformation. 

### Description
The [uml2rdbms_simple.qvtr](Resources/uml2rdbms_simple.qvtr) transformation is a (very) simplified version of the classical object-relational mapping, between class diagrams and database schemes, used as a running example in the QVT standard.

Every persistent Class on the UML class diagram is matched to a Table in the relational database scheme, with a Column for every Attribute, including those inherited from super-classes.

Meta-models and models are specified in the Eclipse Modelling Framework (EMF), enhanced with OCL constraints.

The provided Alloy models provide an encoding of the class diagram and database schemes and of the QVT-r transformation, demonstrating a solver-based approach to bidirectional transformations. In these models, model distance is calculated with graph-edit distance. An instantiation for a particular transformation example, described below, is also provided.

#### Meta-models
| [UML.ecore](Resources/UML.ecore) for UML class diagrams | [RDBMS.ecore](Resources/RDBMS.ecore) for relational database schemes |
| --- | --- |
| <img src="Resources/images/UML_metamodel.png" alt="UML metamodel" width="90%"> | <img src="Resources/images/RDB_metamodel.png" alt="RDBMS metamodel" width="90%"> |

#### Models
| [UML_Company.xmi](Resources/UML_Company.xmi) | [RDB_Company.xmi](Resources/RDB_Company.xmi) |
| --- | --- |
| <img src="Resources/images/UML_company.png" alt="UML company" width="90%" align="middle"/> | <img src="Resources/images/RDB_company.png" alt="RDB company" width="90%" align="middle"/> |

### Development history
* This example is a simplified version of the example illustrating the *MOF 2.0 Query/View/Transformation Specification*. 
* This example has been used to illustrate the SoSyM paper *[Least-change bidirectional model transformation with QVT-R and ATL](http://nmacedo.github.io/pubs.html#sosym16)*, FASE'13 paper *[Implementing QVT-R bidirectional model transformations using Alloy](http://nmacedo.github.io/pubs.html#fase13)*, and N. Macedo's *[PhD Thesis](http://nmacedo.github.io/pubs.html#phd14)*.
* A version with [associations and keys](../CD2DBS_keys) has been used to illustrate the ASE'13 tool demo *[Model repair and transformation with Echo](http://nmacedo.github.io/pubs.html#ase13)*.
* The [benchmarks](Resources/Synthetic) procedurally generated to evaluate the SAT-based bidirectional transformation approach are also from this example.
* Alloy models have been developed and analyzed under the *Alloy Analyzer 4.2_2012-09-25*, and subsequently tested for support under version *5.0.0.201804081720*.

---

* Language: [[Alloy](https://github.com/nmacedo/MSV/wiki/By-Language#alloy)] [[Ecore](https://github.com/nmacedo/MSV/wiki/By-Language#ecore)] [[QVT](https://github.com/nmacedo/MSV/wiki/By-Language#qvt)]
* Theme: [[Synchronization](https://github.com/nmacedo/MSV/wiki/By-Theme#synchronization)] [[Bidirectional Transformation](https://github.com/nmacedo/MSV/wiki/By-Theme#bidirectional-transformation)] [[MDE](https://github.com/nmacedo/MSV/wiki/By-Theme#mde)]
* Venue: [[SoSyM16](https://github.com/nmacedo/MSV/wiki/By-Venue#research)] [[PhD14](https://github.com/nmacedo/MSV/wiki/By-Venue#research)] [[FASE13](https://github.com/nmacedo/MSV/wiki/By-Venue#research)]

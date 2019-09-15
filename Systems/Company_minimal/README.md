# Company human resources synchronization (minimal)

A very minimal example for company human resources synchronization used to demonstrate SAT-based bidirectional transformations.

### WorldToCompany
The [WorldToCompany.atl](Resources/WorldToCompany.atl) transformation is a (very) simplified transformation between person and employees registers.

#### Overview
Every person is mapped to a emplyee with the same name, which additionally have salaries.

#### Meta-models
| [World.ecore](Resources/World.ecore) for world models | [Company.ecore](Resources/Company.ecore) for company models |
| --- | --- |
| <img src="Resources/images/World_metamodel.png" alt="World metamodel" width="400px"> | <img src="Resources/images/Company_metamodel.png" alt="Company metamodel" width="350px"> |

#### History
* This example has been used to illustrate the BX'14 *[Towards a framework for multi-directional model transformations](http://nmacedo.github.io/pubs.html#bx14)* paper and N. Macedo's *[PhD Thesis](http://nmacedo.github.io/pubs.html#phd14)*.

---

* Language: [[Alloy](https://github.com/nmacedo/MSV/wiki/By-Language#alloy)] [Ecore] [ATL]
* Theme: [[Bidirectional Transformation](https://github.com/nmacedo/MSV/wiki/By-Theme#bidirectional-transformation)] 
* Venue: [SoSyM16] [PhD]

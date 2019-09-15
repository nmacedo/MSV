# FM2CFs

A very minimal example related to SPL engineering used to demonstrate SAT-based multidirectional transformations.

### UML2RDBMS
The [fm2cfs.qvtr](Resources/fm2cfs.qvtr) transformation is a (very) simplified SPL scenario between a feature model and 2 system configurations.

#### Overview
Every mandatory feature on the feature model must be present in the configurations, while every feature selected in the configuration must belong to the feature model.

#### Meta-models
| [FM.ecore](Resources/FM.ecore) for feature models | [CF.ecore](Resources/CF.ecore) for the first configuration | [CF.ecore](Resources/CF.ecore) for the second configuration |
| --- | --- | --- |
| <img src="Resources/images/FM_metamodel.png" alt="FM metamodel" width="400px"> | <img src="Resources/images/CF_metamodel.png" alt="Configuration metamodel" width="350px"> | <img src="Resources/images/CF_metamodel.png" alt="Configuration metamodel" width="350px"> |

#### Models
| [FM.xmi](Resources/FM.xmi) | [CF1.xmi](Resources/CF1.xmi) | [CF2.xmi](Resources/CF2.xmi) |
| --- | --- | --- |

#### History
* This example has been used to illustrate the BX'14 *[Towards a framework for multi-directional model transformations](http://nmacedo.github.io/pubs.html#bx14)* paper and N. Macedo's *[PhD Thesis](http://nmacedo.github.io/pubs.html#phd14)*.

---

* Language: [[Alloy](https://github.com/nmacedo/MSV/wiki/By-Language#alloy)] [Ecore] [ATL]
* Theme: [[Bidirectional Transformation](https://github.com/nmacedo/MSV/wiki/By-Theme#bidirectional-transformation)] 
* Venue: [SoSyM16] [PhD]

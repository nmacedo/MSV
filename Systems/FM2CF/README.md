# SPL development (minimal)

A very minimal example related to SPL engineering.

### Description
The [fm2cfs.qvtr](Resources/fm2cfs.qvtr) transformation is a (very) simplified Software Product Line (SPL) development scenario between a feature model and 2 system configurations.

Every mandatory feature on the feature model must be present in the configurations, while every feature selected in the configuration must belong to the feature model.

Meta-models and models are specified in the Eclipse Modelling Framework (EMF).

The provided Alloy models provide an encoding of the class diagram and database schemes and of the QVT-r transformation, demonstrating a solver-based approach to multidirectional transformations. An instantiation for a particular transformation example, described below, is also provided.

#### Meta-models
| [FM.ecore](Resources/FM.ecore) for feature models | [CF.ecore](Resources/CF.ecore) for the first configuration | [CF.ecore](Resources/CF.ecore) for the second configuration |
| --- | --- | --- |
| <img src="Resources/images/FM_metamodel.png" alt="FM metamodel" width="90%"> | <img src="Resources/images/CF_metamodel.png" alt="Configuration metamodel" width="90%"> | <img src="Resources/images/CF_metamodel.png" alt="Configuration metamodel" width="90%"> |

#### Models
| [FM.xmi](Resources/FM.xmi) | [CF1.xmi](Resources/CF1.xmi) | [CF2.xmi](Resources/CF2.xmi) |
| --- | --- | --- |

### Development history
* This example has been used to illustrate the BX'14 *[Towards a framework for multi-directional model transformations](http://nmacedo.github.io/pubs.html#bx14)* paper and N. Macedo's *[PhD Thesis](http://nmacedo.github.io/pubs.html#phd14)*.
* All models have been developed and analyzed under the *Alloy Analyzer 4.2_2012-09-25*, and subsequently tested for support under version *5.0.0.201804081720*.

---

* Language: [[Alloy](https://github.com/nmacedo/MSV/wiki/By-Language#alloy)] [[Ecore](https://github.com/nmacedo/MSV/wiki/By-Language#ecore)] [[QVT](https://github.com/nmacedo/MSV/wiki/By-Language#qvt)]
* Theme: [[Synchronization](https://github.com/nmacedo/MSV/wiki/By-Theme#synchronization)] [[Multidirectional Transformation](https://github.com/nmacedo/MSV/wiki/By-Theme#multidirectional-transformation)] [[MDE](https://github.com/nmacedo/MSV/wiki/By-Theme#mde)] 
* Venue: [[BX14](https://github.com/nmacedo/MSV/wiki/By-Venue#bx14)] [[PhD14](https://github.com/nmacedo/MSV/wiki/By-Venue#phd14)]

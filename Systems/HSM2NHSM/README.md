# Expand/collapse hierarchical state machines

The various HSM2NHSM transformations specify the collapse/expansion of hierarchical state diagrams.

#### Overview
Every top-level State on the expanded state diagram is matched to a State in the collapsed state diagram with the same name. Transitions at the expanded sate diagram pushed up from nested States to the top-level States at the collapsed state diagram.

This version of HSM2NHSM relies on the *recursion* to retrieve Transitions from nested states. A version using *transitive closure* is also available [here](../hsm2nhsm_closure/).

#### Meta-models
| [HSM.ecore](../../../metamodels/hsm2nhsm/HSM.ecore) for expanded (hierarchical) state diagrams | [NHSM.ecore](../../../metamodels/hsm2nhsm/NHSM.ecore) for collapsed (non-hierarchical) state diagrams |
| --- | --- | --- |
| <img src="../../../metamodels/hsm2nhsm/images/HSM_metamodel.png" alt="HSM metamodel" width="400px"> | <img src="../../../metamodels/hsm2nhsm/images/NHM_metamodel.png" alt="NHSM metamodel" width="400px"> |

#### Models
| [HSM_example.xmi](../../../models/hsm2nhsm/HSM_example.xmi) | [NHM_example.xmi](../../../models/hsm2nhsm/NHM_example.xmi) |
| --- | --- | --- |
| <img src="../../../models/hsm2nhsm/images/HSM_model.png" alt="HSM model" width="250px" align="middle"/> | <img src="../../../models/hsm2nhsm/images/NHM_model.png" alt="NHSM model" width="200px" align="middle"/> |

#### History
* This example is based on the running example from the paper *JTL: a bidirectional and change propagating transformation language* by A. Cicchetti, D. Di Ruscio, R. Eramo and A. Pierantonio.
* This example has been used to illustrate the SoSyM *[Least-change bidirectional model transformation with QVT-R and ATL](http://nmacedo.github.io/pubs.html#sosym16)* paper and N. Macedo's *[PhD Thesis](http://nmacedo.github.io/pubs.html#phd14)*.

---

* Language: [Ecore] [QVT] [ATL]
* Theme: [[Bidirectional Transformation](https://github.com/nmacedo/MSV/wiki/By-Theme#bidirectional-transformation)] 
* Venue: [[SoSyM16](http://nmacedo.github.io/pubs.html#sosym16)] [[PhD](http://nmacedo.github.io/pubs.html#phd14)]
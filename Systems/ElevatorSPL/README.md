# Elevator system SPL

Models of a software product line (SPL) representing variants of an elevator system, initially proposed in paper *Feature integration using a feature construct*.

### Description

The model consists of an elevator and a set of floors; at each floor there is a button that calls the elevator, and inside it there is a button for each of the floors. The base system answers button calls giving priority to the current direction: it only changes direction when there are no more calls for the succeeding floors. This behavior is however modified as additional features are selected:
  * a parking feature moves the elevator to the first floor when there are no button calls; 
  * an idle feature forces the elevator to open the door when there are no button calls; 
  * an executive floor feature prioritizes calls to one of the floors over the others. 
  
Multiple interfering features, under some restrictions, may be selected. A feature model can impose simple dependencies/conflicts between the features restricts some combinations, namely:
  * since the idle and the parking features have conflicting behavior their choice is forced to be exclusive. 

In this model each configuration - i.e., the static component - represents a valid product from the SPL, that is, a selection of features, while the dynamic component models the evolution of the system taking into consideration those features. The feature model is encoded as a structural property. The operations the behavior of the system taking into consideration the selected features. 

There are several safety and liveness properties that can be checked about this specification. For instance, the most basic liveness property states that a pressed button will eventually be answered. These are checked over every possible feature combination. While some of these are expected to always hold, some fail under certain feature configurations. For instance, the above property will fail with the executive floor feature, as calls to those floors will be prioritized.

Electrum models are provided in a predicate-as-operations idiom and in a event-idiom. The corresponding Alloy version in the event-idiom is also provided. 

### Development history
* This example is based on the benchmarks from the paper *Symbolic Model Checking of Software Product Lines* by A. Classen and A. Legay, itself adapted from *Feature integration using a feature construct* by M. Plath and M. Ryan.
* The model has been used as a running example and in the benchmarks of the FSE'16 *[Lightweight specification and analysis of dynamic systems with rich configurations](http://nmacedo.github.io/pubs.html#fse16)* paper.
* Alloy models have been developed and analyzed under the *Alloy Analyzer 4.2_2015-02-22*.
* Electrum models have been developed and analyzed under the *Electrum Analyzer 0.1*., and subsequently tested for support under version *1.2*.

---

* Language: [[Alloy](https://github.com/nmacedo/MSV/wiki/By-Language#alloy)] [[Electrum](https://github.com/nmacedo/MSV/wiki/By-Language#electrum)]
* Theme: [[SPL](https://github.com/nmacedo/MSV/wiki/By-Theme#spl)] [[Rich Behavior](https://github.com/nmacedo/MSV/wiki/By-Theme#rich-behavior)] 
* Venue: [[FSE16](https://github.com/nmacedo/MSV/wiki/By-Venus#fse16)]

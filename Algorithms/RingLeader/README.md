# Ring leader election algorithm

Simple implementation of the [leader election](https://en.wikipedia.org/wiki/Leader_election#Rings_with_unique_IDs) in networks with ring topology for processes with unique identifiers.

### Description

* In the SMV models, the a model must be specified for each distinct number of processes due to the lack of first-order quantifications.
* In TLA the transitive closure needed to enforce the ring topology is not natively defined.

### Development history
* The original model is used as a running example in the  _Software Abstractions: Logic, Language, and Analysis_ book by D. Jackson, and is distributed with the Alloy Analyzer.
* The Alloy/Electrum models are a variation of the original, and have been used in the benchmarks of the FSE'16 *[Lightweight specification and analysis of dynamic systems with rich configurations](http://nmacedo.github.io/pubs.html#fse16)* and ASE'18 *[The Electrum Analyzer: Model checking relational first-order temporal specifications](http://nmacedo.github.io/pubs.html#ase18)* papers.
* The Electrum version has also been used as the running example of the ASE'18 *[The Electrum Analyzer: Model checking relational first-order temporal specifications](http://nmacedo.github.io/pubs.html#ase18)* tool demo.
* The TLA+ and SMV models are also inspired by the the original Alloy model.
* Alloy models have been developed and analyzed under the *Alloy Analyzer 4.2_2015-02-22*.
* Electrum models have been developed and analyzed under the *Electrum Analyzer 0.1*, and subsequently tested for support under version *1.2*.
* TLA+ models have been developed and analyzed under _TLC 2.07_ (and _TLA Toolbox 1.5.1_).

---

* Language: [[Alloy](https://github.com/nmacedo/MSV/wiki/By-Language#alloy)] [[TLA+](https://github.com/nmacedo/MSV/wiki/By-Language#tla)] [[SMV](https://github.com/nmacedo/MSV/wiki/By-Language#smv)] [[Electrum](https://github.com/nmacedo/MSV/wiki/By-Language#electrum)]
* Theme: [[Concurrency](https://github.com/nmacedo/MSV/wiki/By-Theme#concurrency)] [[Rich Structure](https://github.com/nmacedo/MSV/wiki/By-Theme#rich-structure)] [[Rich Behaviour](https://github.com/nmacedo/MSV/wiki/By-Theme#rich-behavioural)]
* Venue: [[EM15/16](https://github.com/nmacedo/MSV/wiki/By-Venue#modeling-and-specification)] [[FSE16](https://github.com/nmacedo/MSV/wiki/By-Venus#fse16)] [[ASE18](https://github.com/nmacedo/MSV/wiki/By-Venus#ase18)]
 

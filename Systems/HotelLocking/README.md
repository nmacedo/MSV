# Hotel room locking system (free configurations)

Different versions of the hotel room locking system model that comes packaged with the Alloy Analyzer, proposed by D. Jackson in _Software Abstractions: Logic, Language, and Analysis_.

### Description

These models were developed with the goal of exploring analysis rich in structural and behavioral constraints.

#### Structural model
* the universe of guests and rooms is variable;
* the number of keys is exact and must form a total order;
* keys are distributed among the rooms _a priori_;
* for 4 guests, rooms and keys, there are 18960 configurations.

#### Behavioral model
* enter a room with the current key or with a more recent one, rendering the previous obsolete;
* check in a guest and issue a new key for the room;
* check out the guest without requesting his key;
* a "no intervening" constraint must be enforced if the specification is to hold.

#### Specification
* Safety: can a guest other than the room's occupant enter that room?
* The property only holds if a "no intervening" constraint is enforced.

The original Alloy model considers a variable universe for guests and rooms. This encumbers other model checkers, so an alternative version with exact scopes is provided (models with suffix `Exact`).

In ProB the number of checked configurations is limited by the value of the `MAX_INITIALISATIONS` parameter; if this parameter is two low, a configuration for which there are counter-examples may not be analyzed. Moreover, universal quantifications are atomic propositions and operations cannot be called within; thus, the assertions had to be expanded. 

A model for the Electrum extension with explicit actions is also available (suffix `action_ext`).

### Development history
* The original model, by Daniel Jackson, is a running example in the book *Software Abstractions: Logic, Language, and Analysis* and is distributed with the Alloy Analyzer.
* Alloy and TLA+ models were developed for the tech report [_Alloy meets TLA+: An exploratory study_](http://nmacedo.github.io/pubs/CoRR16.pdf), and used as running examples and in the benchmarks.
* Electrum models were developed for the FSE'16 paper [_Lightweight specification and analysis of dynamic systems with rich configurations_](http://nmacedo.github.io/pubs/FSE16.pdf), and used as a running example and in the benchmarks.
* The Electrum model was also used as in the benchmarks of the ASE'18 *[The Electrum Analyzer: Model checking relational first-order temporal specifications](http://nmacedo.github.io/pubs.html#ase18)* paper.
* Electrum models for the action extension were developed for the ABZ'18 paper [_Proposition of an action layer for Electrum_](http://nmacedo.github.io/pubs/ABZ18b.pdf), and used as a running example.
* Electrum models for the action extension were also used as a running example for the F-IDE@FM'19 paper [_Simulation under arbitrary temporal logic constraints_](http://nmacedo.github.io/pubs/FIDE19.pdf).
* Models for fixed configurations after enumeration are also available [here](../HotelLocking_fixcfg), that require only dynamic analysis.
* Alloy models have been developed and analyzed under _Alloy Analyzer 4.2_2015-02-22_.
* B models have been developed and analyzed under _ProB 1.5.0_.
* TLA+ models have been developed and analyzed under _TLC 2.07_ (and _TLA Toolbox 1.5.1_).
* Electrum models have been developed and analyzed under the *Electrum Analyzer 0.1*, and subsequently tested for support under version *1.2*.
* Electrum models for the action extension have been developed and analyzed under *Electrum Analyzer 1.0 with actions*, and subsequently tested and updted for support under version *1.2 with actions* (and F-IDE@FM'19 version *1.1 with simulator*).

---

* Language: [[Alloy](https://github.com/nmacedo/MSV/wiki/By-Language#alloy)] [[TLA+](https://github.com/nmacedo/MSV/wiki/By-Language#tla)] [[Electrum](https://github.com/nmacedo/MSV/wiki/By-Language#electrum)] [[B](https://github.com/nmacedo/MSV/wiki/By-Language#b)]
* Theme: [[Rich Structure](https://github.com/nmacedo/MSV/wiki/By-Theme#rich-structure)] [[Rich Behaviour](https://github.com/nmacedo/MSV/wiki/By-Theme#rich-behaviour)]
* Venue: [[FSE16](https://github.com/nmacedo/MSV/wiki/By-Venue#fse16)] [[CoRR16](https://github.com/nmacedo/MSV/wiki/By-Venue#corr16)] [[ABZ18b](https://github.com/nmacedo/MSV/wiki/By-Venue#abz18b)] [[ASE18](https://github.com/nmacedo/MSV/wiki/By-Venus#ase18)] [[FIDE19](https://github.com/nmacedo/MSV/wiki/By-Venus#fide19)]


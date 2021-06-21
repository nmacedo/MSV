# Hotel room locking system (free configurations)

A simple adaptation of the hotel room locking system model that comes packaged with the Alloy Analyzer, proposed by D. Jackson in _Software Abstractions: Logic, Language, and Analysis_.

###

These models were developed with the goal of exploring analysis rich in structural and behavioural constraints.

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

The original Alloy model considers a variable universe for guests and rooms. This encumbers other model checkers, so an alternative version with exact scopes is provided (models with suffix `exact`).

### Development history
* The original model, by Daniel Jackson, is a running example in the book *Software Abstractions: Logic, Language, and Analysis* and is distributed with the Alloy Analyzer.
* The Alloy, B and TLA+ models were developed for the paper [_Alloy meets TLA+: An exploratory study_](http://macedo.github.io/pubs/CoRR16.pdf), and used as running examples and in the benchmarks.
* The Electrum model were developed for the paper [_Lightweight specification and analysis of dynamic systems with rich configurations_](http://macedo.github.io/pubs/FSE16.pdf), and used as running examples and in the benchmarks.
* Models for fixed configurations are also available [here](../HotelLocking_fixcfg), that require only dynamic analysis.

---

* Language: [[Alloy](https://github.com/nmacedo/MSV/wiki/By-Language#alloy)] [[TLA+](https://github.com/nmacedo/MSV/wiki/By-Language#tla)] [[Electrum](https://github.com/nmacedo/MSV/wiki/By-Language#electrum)] [[B](https://github.com/nmacedo/MSV/wiki/By-Language#b)]
* Theme: [[Rich Structure](https://github.com/nmacedo/MSV/wiki/By-Theme#rich-structure)] [[Rich Behaviour](https://github.com/nmacedo/MSV/wiki/By-Theme#rich-behaviour)]
* Venue: [[FSE16](https://github.com/nmacedo/MSV/wiki/By-Venue#fse16)] [[CoRR16](https://github.com/nmacedo/MSV/wiki/By-Venue#corr16)]


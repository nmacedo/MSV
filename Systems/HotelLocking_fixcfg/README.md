# Hotel room locking system (fixed configurations)

A version of the hotel room locking system model that comes packaged with the Alloy Analyzer, proposed by D. Jackson in _Software Abstractions: Logic, Language, and Analysis_, with fixed configurations enumerated by model `hotel_init.als`.

### Description

These models were developed with to measure the impact of the structural solving process, since once configurations are fixed the problems become fully behavioral. Models with suffix `s` are satisfiable, producing counter-examples; those with suffix `u` are unsatisfiable.

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

### Development history
* The original model, by Daniel Jackson, is a running example in the book *Software Abstractions: Logic, Language, and Analysis* and is distributed with the Alloy Analyzer.
* The Alloy and TLA+ models were developed for the paper [_Alloy meets TLA+: An exploratory study_](http://macedo.github.io/pubs/CoRR16.pdf), and used as running examples and in the benchmarks.
* Models where configurations are part of the problem are available [here](../HotelLocking), requiring also structural solving.
* Alloy models have been developed and analyzed under _Alloy Analyzer 4.2_2015-02-22_.
* B models have been developed and analyzed under _ProB 1.5.0_.
* TLA+ models have been developed and analyzed under _TLC 2.07_ (and _TLA Toolbox 1.5.1_).

---

* Language: [[Alloy](https://github.com/nmacedo/MSV/wiki/By-Language#alloy)] [[TLA+](https://github.com/nmacedo/MSV/wiki/By-Language#tla)] [[B](https://github.com/nmacedo/MSV/wiki/By-Language#b)]
* Theme: [[Rich Behaviour](https://github.com/nmacedo/MSV/wiki/By-Theme#rich-behaviour)]
* Venue: [[CoRR16](https://github.com/nmacedo/MSV/wiki/By-Venue#corr16)]

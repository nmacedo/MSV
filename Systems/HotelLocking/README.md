# Hotel room locking system (free configurations)

A simple adaptation of the hotel room locking system model that comes packaged with the Alloy Analyzer, proposed by D. Jackson in _Software Abstractions: Logic, Language, and Analysis_.

<http://alloy.mit.edu/alloy/download.html>

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

_Comments:_
* The specification is broken depending on whether a "no intervening" constraint is enforced.
* The original Alloy model considers a variable scope for guests and rooms. This encumbers other model checkers, so an alternative version with exact scopes is provided (files with `exact` suffix).
* This example is rich in structural properties. Alloy model <hotel_init.als> generates every valid configuration.

---

* Language: [[Alloy](https://github.com/nmacedo/MSV/wiki/By-Language#alloy)] [[TLA+](https://github.com/nmacedo/MSV/wiki/By-Language#tla)] [[Electrum](https://github.com/nmacedo/MSV/wiki/By-Language#electrum)] [[B](https://github.com/nmacedo/MSV/wiki/By-Language#b)]
* Theme: [[Structural](https://github.com/nmacedo/MSV/wiki/By-Theme#rich-structural-model)] [[Behavioral](https://github.com/nmacedo/MSV/wiki/By-Theme#rich-behavioral-model)]
* Venue: [[FSE16](https://github.com/nmacedo/MSV/wiki/By-Venue#papers)]  [FSE16 Benchmarks] [[Corr16](https://github.com/nmacedo/MSV/wiki/By-Venue#papers)]


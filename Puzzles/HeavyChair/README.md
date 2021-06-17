# Heavy chair problem

This specification tries to solve the following puzzle. There is a "heavy chair", that can only be rotated on one of its legs. Is it possible to move it to the adjacent position while preserving its direction?

#### Operations
* 8: move one of the four legs (Top/Bottom-Left/Right) Clockwise or Anti-clockwise

#### Specification
* Safety: will it ever be in the adjacent position in the initial position?

_Comments_:
* We assume that the legs' identifiers are relative, i.e., the same identifier always refers to, e.g., the top-left level in each state.
* The "board" on which the chair rests is assumed to be bounded.
* In SMV the size of the board must be defined in the model; in TLA it can be specified externally in the configuration file.
* TLA: why can't we use "ACTION-CONSTRAINT" to forbid the chair to move outside the board?
* SMV: be aware of the current definition of modulo when rotating the chair, where `-1 % 4 = -1`.

---

* Language: [[TLA+](https://github.com/nmacedo/MSV/wiki/By-Language#tla)] [[SMV](https://github.com/nmacedo/MSV/wiki/By-Language#smv)] 
* Theme: [[Transport puzzles](https://github.com/nmacedo/MSV/wiki/By-Theme#transport-puzzles)]
* Venue: [[EM15/16](https://github.com/nmacedo/MSV/wiki/By-Venue#em-1516)] [[EM18/19](https://github.com/nmacedo/MSV/wiki/By-Venue#em-1819)] 


# Alloy4Fun

A formalization of the data structures behind [Alloy4Fun](https://alloy4fun.inesctec.pt/), a platform for online editing and sharing of Alloy models.

### Description

- Alloy4Fun was first proposed in the ABZ'20 paper [_Experiences on teaching Alloy with an automated assessment platform_](http://haslab.github.io/TRUST/papers/abz20a.pdf) and its [extended version](https://nmacedo.github.io/pubs/SCP21.pdf) in the SCP journal.
- Alloy4Fun stores all models executed and shared in the platform, keeping the derivation tree of the submissions so that solving sessions can be studied.
- It also has support for the specification of challenges by marking certain model elements as *secret*. Models with secrets can be shared through a private link (the full model) or through a public link (secrets hidden).
- The model was initially developed to explore different features during design, namely:
  1. whether to store derivation trees
  2. whether to support models with secrets
  3. whether to store models when executing commands
  4. whether to allow permalinks to instances

These features are organized according to the following feature model:

<img src="fm.png" width="400">

### Development history

* This case study was initially presented in the SETTA'19 paper *[Simplifying the analysis of software design variants with a colorful Alloy](http://nmacedo.github.io/pubs.html#setta19)*.
* The Colorful and plain Alloy SPL versions of the model were developed for that same paper, and used in the benchmarks.
* A more detailed, single variant, Alloy version was developed for the SCP paper *[Experiences on teaching Alloy with an automated assessment platform](http://nmacedo.github.io/pubs.html#scp21)*.
* Plain Alloy models have been tested for support under *Alloy Analyzer 5.1.0*.
* Colorful Alloy models have been developed and analyzed under first release of *Colorful Alloy Analyzer (July 2019)*.
---

* Language: [[Alloy](https://github.com/nmacedo/MSV/wiki/By-Language#alloy)] [[Electrum](https://github.com/nmacedo/MSV/wiki/By-Language#electrum)] [[Colorful Alloy](https://github.com/nmacedo/MSV/wiki/By-Language#colorful-alloy)]
* Theme: [[Rich Structure](https://github.com/nmacedo/MSV/wiki/By-Theme#rich-structure)] [[Variability](https://github.com/nmacedo/MSV/wiki/By-Theme#variability)]
* Venue: [[SETTA19](https://github.com/nmacedo/MSV/wiki/By-Venue#setta19)] [[SCP21](https://github.com/nmacedo/MSV/wiki/By-Venue#scp21)]

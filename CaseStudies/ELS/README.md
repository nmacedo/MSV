# Adaptive Exterior Light System

Models for an Adaptive Exterior Light System in the automotive domain. The model is based on the reference [document](https://abz2020.uni-ulm.de/resources/files/casestudyABZ2020v1.17.pdf) and validation [sequences](https://abz2020.uni-ulm.de/resources/files/ValidationSequences_v1.8.xlsx) provided in the call for case study submission of [ABZ'20](https://abz2020.uni-ulm.de/).  

The description of the models, as well as the modelling approach, is available in this [conference paper](http://haslab.github.io/TRUST/papers/abz20b.pdf). Additional information, as well as an automatic validator for the validation sequences, is available [here](https://github.com/haslab/Electrum/wiki/ELS).

The ELS system is configurable, and several approaches to the modelling of the variants were followed.
* Distinct Electrum model for each variant (there are only 4 effectively distinct variants) 
* A single model in pure Electrum under a variability idiom
* A single Colorful Electrum  under an extension for feature annotations.

### History

* The ELS models are described the paper ABZ'20 paper [_Validating Multiple Variants of an Automotive Light System with Electrum_](http://haslab.github.io/TRUST/papers/abz20b.pdf).
* Although these models were initially developed for Electrum 2.0, they have since been updated for Electrum 2.1. Legacy versions are available [here](https://github.com/nmacedo/MSV/tree/06b67901df7bcaad7f874d7c079b0984f60317db/CaseStudies/ELS). The exception is the colorful model, whose prototype extension, available [here](https://github.com/haslab/Electrum/wiki/ELS/colorful-electrum-alpha.jar), has not been bumped to Electrum 2.1.

---

* Language: [[Electrum](https://github.com/nmacedo/MSV/wiki/By-Language#electrum)] [[Colorful Electrum](https://github.com/nmacedo/MSV/wiki/By-Language#colorful-electrum)]
* Theme: [[Industrial](https://github.com/nmacedo/MSV/wiki/By-Theme#industrial)] [[Transportation](https://github.com/nmacedo/MSV/wiki/By-Theme#transportation)] [[Structural](https://github.com/nmacedo/MSV/wiki/By-Theme#rich-structural-model)] [[Behavioral](https://github.com/nmacedo/MSV/wiki/By-Theme#rich-behavioral-model)]
* Venue: [[ABZ20a](https://github.com/nmacedo/MSV/wiki/By-Venue#abz20a)]


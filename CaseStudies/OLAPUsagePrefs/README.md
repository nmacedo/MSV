# OLAP Cube usage preferences

A model for the extraction of OLAP usage preferences based on the association rules retrieved by the OLAP mining process. This work is described in this [paper](https://nmacedo.github.io/pubs.html#confenis17). The process consists of:
* construction of the OLAP cube from the data tables and user parameters
* construction of the mining rules from the OLAP cube
* construction of the strong rules from the mining rules and user preferences
* construction of the preferences from the strong rules

Data in the tables is abstracted away, each rule has a performance field for the selected fields that represents that data.

## History

* This model has been originally developed for the CONFENIS'17 *[Checking the correctness of what-if scenarios](http://nmacedo.github.io/pubs.html#confenis17)* presentation.
* Alloy models have been developed and analyzed under the *Alloy Analyzer 4.2_2015-02-22*.

---

* Language: [[Alloy](https://github.com/nmacedo/MSV/wiki/By-Language#alloy)]
* Theme: [[Data Warehousing](https://github.com/nmacedo/MSV/wiki/By-Theme#data-warehousing)] [[Rich Structure](https://github.com/nmacedo/MSV/wiki/By-Theme#rich-structure)]
* Venue: [[CONFENIS17](https://github.com/nmacedo/MSV/wiki/By-Venue#papers)]

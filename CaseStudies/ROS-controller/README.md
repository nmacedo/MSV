# ROS Controller

Example model generated from a ROS system annotated with HPL specifications, the language provided by the HAROS platform, as described in the paper _Verification of system-wide safety properties of ROS applications_ by Carvalho, Cunha, Macedo & Santos.

### Description

[HAROS]() is a framework for the quality assessment of ROS software, which automatically extracts computation graphs from ROS source code, and provides a user-friendly behavioural specification language (HPL) and a unified reporting interface. The paper cited above proposes an automatic translation into Electrum (now Alloy 6) of the architecture of a ROS system along with the HPL specifications.

The Controller system is the paper's running example, and has the following architecture.

These features are organized according to the following feature model:
![E-commerce feature model](/architecture.png)

Moreoever, the behaviour of the system's nodes are encoded in HPL as follows.

```
Teleop:
  globally: no /tel{val not in 0 to 100}
Base:
  globally: no /dat{val not in [0,1]}
Controller:
  after /dat{val=0} until /dat{val!=1}: no /cmd{val!=0}
  globally: /cmd{val=0} requires /tel{val=0} || /dat{val=0}
  globally: /cmd{val!=0} as m requires /tel{val=$m.val}
  globally: /dat{val=0} causes /cmd{val=0, msg="stop"}
```

Finally, the expected system-wide properties are encoded in HPL as follows.

```
simple:
  globally: no /cmd{val not in 0 to 100}
  globally: /cmd{msg="stop"} requires /dat{val=0}
```

### Development history
* The system model is a running example in the paper _Verification of system-wide safety properties of ROS applications_ by Carvalho, Cunha, Macedo & Santos. The Electrum model is automatically generated from the work there described, with minor changes to improve readability.

---

* Language: [[Electrum](https://github.com/nmacedo/MSV/wiki/By-Language#electrum)]
* Theme: [[Robotics](https://github.com/nmacedo/MSV/wiki/By-Theme#robotics)]
* Venue: [[IROS20](https://github.com/nmacedo/MSV/wiki/By-Venue#iros20)] 

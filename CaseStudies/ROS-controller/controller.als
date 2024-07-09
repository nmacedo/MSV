-- ROS header, architecture

abstract sig Topic, Field, Value {}
sig IntVal, StrVal extends Value {}

abstract sig Node {
  subs       : set Topic,
  advs       : set Topic,
  var inbox  : set Message, 
  var outbox : set Message 
}

sig Message {
  topic : one Topic,
  value : Field -> lone Value 
}

-- Application-specific architecture

one sig tel, dat, cmd extends Topic {}
one sig Teleop, Base, Controller extends Node {}

fact Links {
  advs = Teleop->tel + Base->dat + Controller->cmd
  subs = Controller->(tel + dat) + Base->cmd 
}

one sig tel_val, dat_val, cmd_val, cmd_msg extends Field {}

fact Fields {
  all m: topic.tel {
    m.value in tel_val->IntVal
    m.value in tel_val->one IntVal 
  }
  all m: topic.dat {
    m.value in dat_val->IntVal
    m.value in dat_val->one IntVal 
  }
  all m: topic.cmd {
    m.value in cmd_val->IntVal + cmd_msg->StrVal
    m.value in (cmd_val+cmd_msg)->one (IntVal+StrVal) 
  } 
}

lone sig Int_0, Int_1 in IntVal {}
sig Int_0_10, Int_0_100 in IntVal {}
lone sig Str_stop in StrVal {}

fact Values {
  Int_0 + Int_1 in Int_0_10
  Int_0_10 in Int_0_100 
  no Int_0 & Int_1 
}

-- ROS header, behaviour

fact Messages { 
  no outbox + inbox
  always {
    all n: Node {
      n.inbox.topic in n.subs 
      n.outbox.topic in n.advs 
    }
    all m: Node.outbox {
      all n: m.topic.~subs | eventually m in n.inbox 
      eventually m not in Node.outbox 
    }
    all m: Node.inbox |
      before once m in m.topic.~advs.outbox 
  } 
}

-- Application-specific behaviour

fact NodeBehavior { 
  always {
    no m: Teleop.outbox & topic.tel | m.value[tel_val] not in Int_0_100

    no m: Base.outbox & topic.dat | m.value[dat_val] not in Int_0+Int_1
    
    ((some m: Controller.inbox & topic.dat | m.value[dat_val] = Int_0 and
      no m: Controller.inbox & topic.dat | m.value[dat_val] = Int_1) implies 
        ((always no m0: Controller.outbox & topic.cmd | m0.value[cmd_val] != Int_0) or 
        ((no m0: Controller.outbox & topic.cmd | m0.value[cmd_val] != Int_0) until 
          (some m: Controller.inbox & topic.dat | m.value[dat_val] = Int_1))))

    all m: Controller.outbox & topic.cmd | m.value[cmd_val] = Int_0 implies 
      before once (
        (some m0: Controller.inbox & topic.dat | m0.value[dat_val] = Int_0) or 
        (some m0: Controller.inbox & topic.tel | m0.value[tel_val] = Int_0))
    
    all m: Controller.outbox & topic.cmd | m.value[cmd_val] != Int_0 implies 
      before once some m0: Controller.inbox & topic.tel | m0.value[tel_val] = m.value[cmd_val]
    
    all m: Controller.inbox & topic.dat | m.value[dat_val] = Int_0 implies 
      after eventually some m0: Controller.outbox & topic.cmd |
          m0.value[cmd_val] = Int_0 and m0.value[cmd_msg] = Str_stop 
  } 
}

-- Application-specific expected properties

check {
  always no m: Node.outbox & topic.cmd | cmd_val.(m.value) not in Int_0_100
} for exactly 5 Message, 20 Value

check {
  always (all m0: Node.outbox & topic.cmd | cmd_msg.(m0.value) = Str_stop implies
    before once (some m1: Node.outbox & topic.dat | dat_val.(m1.value) = Int_0))
} for exactly 5 Message, 20 Value


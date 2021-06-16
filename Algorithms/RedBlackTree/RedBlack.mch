MACHINE RedBlack
SETS
 Node={n0,n1,n2,n3,n4};
 Color = {Black, Red}
DEFINITIONS
 Key == 0..4
CONSTANTS left_t, right_t, data, color, root, height
PROPERTIES
 left_t : Node <-> Node & right_t : Node <-> Node & data : Node >->> Key & root : Node & color : Node --> Color  & height : Node --> INTEGER & 

 color(root) = Black &
 !n.(n: (color~)[{Red}] => left_t[{n}] \/ right_t[{n}] <: (color~)[{Black}]) & 
 !n.(n:Node => card({x | x : closure(left_t \/ right_t)[left_t[{n}]] & color(x) = Black}) = card({x|x:closure(left_t \/ right_t)[right_t[{n}]] & color(x) = Black})) 


ASSERTIONS
  not(!nn,mm.(nn: Node & mm : Node & nn : {x | x : Node & (x /: dom(left_t) or x /: dom(right_t))} & nn : {x | x : Node & (x /: dom(left_t) or x /: dom(right_t))} => height(nn) - height(mm) : -1..1))
  
END


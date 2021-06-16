module RedBlackTree

enum Color { BLACK, RED }

sig Node {
  left: lone Node,
  right: lone Node,
  data: one Int,
  color: one Color    
}

one sig Root in Node {}

// facts about node colors
fact rootIsBlack {
  Root.color = BLACK
}

fact redNodeChildrenAreBlack {
  all n: Node |
      n.color = RED =>
          all c: n.(right + left) | c.color = BLACK
}

fact blackHeightIsSameToAllPaths {
  all n: Node |
      #(n.left.(^(right + left) + iden) - color.RED)  = #(n.right.(^(right + left) + iden) - color.RED)
}

fact {
	all n:Node | lt[n.data,10] && gte[n.data,0]
}

fun height [n : Node] : Int {
	#(n.*~(left+right))
}

run {} for 2 but exactly 10 Node, 5 Int

check {
	all n1,n2 : Node | ((no n1.left or no n1.right) and (no n2.left or no n2.right)) => (height[n1]).minus[height[n2]] in {-1 + 0 + 1}
} for 2 but exactly 10 Node, 5 Int


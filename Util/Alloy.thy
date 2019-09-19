(* Author: Mário Eiras *)

theory Alloy
imports Main
begin


(* logical connectives and quantifiers *)

abbreviation not2 :: "bool => bool" ("not _" [40] 40) where
"not x == ~ x"

abbreviation or2 :: "bool => bool => bool" (infixl "||" 30) where
    "l || r == l | r"

abbreviation and2 :: "bool => bool => bool" (infixl "&&" 35) where
    "l && r == l & r"

definition Lone :: "('a => bool) => bool" (binder "LONE" 10) where
"Lone P == ALL x y. P x & P y --> x = y"

definition Blone :: "'a set => 'a set => bool" where
  "Blone A P == (LONE x. x : A & P x)"

syntax
    "_Blone" :: "pttrn => 'a set => bool => bool" ("(3LONE _/ :/ _./ _)" [0, 0, 10] 10)

translations
    "LONE x : A. P" == "CONST Blone A (%x. P)"


(* relation type *)

typedecl atom
type_synonym tuple = "atom list"
type_synonym relation = "tuple set"


(* primitive relations *)

definition univ :: "relation" where
    "univ == {[x] | x. True}"

abbreviation none :: "relation" where
    "none == {}"

definition iden :: "relation" where
    "iden == {[x, x] | x. True}"

(* relational operators *)

abbreviation rel_union :: "relation => relation => relation" (infixl "+" 65) where
    "r + s == r Un s"

abbreviation rel_inter :: "relation => relation => relation" (infixl "&" 70) where
    "r & s == r Int s"

definition comp :: "relation => relation => relation" (infixl "." 85) where
    "l . r == {xs @ ys | xs ys. EX w . (xs @ [w] : l) & (w # ys : r)}"

definition prod :: "relation => relation => relation" (infixl "->" 75) where
    "prod a b == {x @ y | x y. (x : a) & (y : b)}"

definition overr :: "relation => relation => relation" (infixl "++" 100) where
"A ++ B == {x. x : B | (x : A & ~(EX a b c. x = a # b & a # c ~: B))}"

definition doma :: "relation  => relation => relation" (infixl "<:" 80) where
    "R <: S == {x . x : S & (EX y x' . y : R & x = y @ x')}"

definition rang :: "relation  => relation => relation" (infixl ":>" 80) where
    "R :> S == {x . x : R & (EX y x' . y : S & x = x' @ y)}"

definition conv :: "relation => relation" where
    "conv r == {rev x | x . x : r}"

inductive_set tcl :: "relation => relation" for r :: relation where
  base: "[i, j] : r ==> [i, j] : tcl r" |
  step: "[i, j] : r ==> [j, k] : tcl r ==> [i, k] : tcl r"

abbreviation tcl2 :: "relation => relation" ("^_" [99] 99) where
    "^r == tcl r"

inductive_set trcl :: "relation => relation" for r :: relation where
  base: "i : iden ==> i : trcl r" |
  step: "[i, j] : r ==> [j, k] : trcl r ==> [i, k] : trcl r"

abbreviation trcl2 :: "relation => relation" ("*_" [99] 99) where
    "*r == trcl r"


(* predicates *)

definition no :: "relation => bool" where
    "no R == R = {}"

definition lone :: "relation => bool" where
    "lone r == (ALL x y . ((x : r) & (y : r) --> (x = y)))"

definition one :: "relation => bool" where
    "one R == EX! x. x : R"

definition some :: "relation => bool" where
    "some R == EX x. x : R"

definition disj :: "relation => relation => bool" where
    "disj r l == (r & l = {})"

abbreviation in2 :: "relation => relation => bool" ("_/ in _" [50, 51] 50) where
    "r in s == r <= s"

abbreviation nin2 :: "relation => relation => bool" ("_/ !in _" [50, 51] 50) where
    "r !in s == ~(r <= s)"

definition norm_rel :: "relation => bool" where
    "norm_rel r == ALL x y. ((x : r & y : r) --> length x = length y)"


(* arity *)

definition arity :: "relation => nat => bool" where
    "arity r n == ALL x : r. n = length x"

lemma univ_arity:
shows "arity univ 1" by (auto simp add: arity_def univ_def)

lemma iden_arity:
shows "arity iden 2" by (auto simp add: iden_def arity_def)

lemma none_arity:
shows "arity none x" by (auto simp add: arity_def)

lemma prod_arity:
shows "[|arity A a; arity B b|] ==> arity (A -> B) (a + b)" by (auto simp add: prod_def arity_def)

lemma comp_arity:
shows "[|arity A a; arity B b|] ==> arity (A . B) (a + b - 1 - 1)" by (auto simp add: comp_def arity_def)

lemma Un_arity:
shows "[|arity A n; arity B n|] ==> arity (A Un B) n" by (auto simp add: arity_def)

lemma in_arity:
shows "[|arity A n; B <= A|] ==> arity B n" by (auto simp add: arity_def)

lemma arity_tcl:
    shows "arity  (^A) 2"
    proof (auto simp add: arity_def)
        fix x
        assume "x : ^A" thus "length x = 2"
        proof induct
            fix i j
            show "length [i, j] = 2" by auto
        next
            fix i k
            show "length [i, k] = 2" by simp
        qed
    qed

lemma arity_trcl:
    shows "arity (trcl A) 2"
    proof (auto simp add: arity_def)
        fix x
        assume "x : *A" thus "length x = 2"
        proof induct
            fix i
            assume "i : iden" with iden_arity show "length i = 2" by (auto simp add: iden_def) 
        next
            fix i k
            show "length [i, k] = 2" by simp
        qed
    qed

(* lemmas *)

lemma lone_def': "lone r <-> one r || no r "
by (auto simp add: one_def lone_def no_def)

lemma one_def': "one r <-> lone r && some r"
by (auto simp add: one_def lone_def some_def)

lemma comp_distrib_l:
"R . (S + T) = R . S + R . T"
  apply (simp add: comp_def)
  apply auto
done

lemma comp_distrib_r:
"(S + T) . R = S . R + T . R"
  apply (simp add: comp_def)
  apply auto
done

lemma neq_Nil_conv_l:
"[|l ~= []|] ==> (EX y ys. l = [y] @ ys)"
  by (induct l) auto

lemma neq_Nil_conv_r:
"[|l ~= []|] ==> (EX y ys. l = ys @ [y])"
  proof (induct l)
  case Nil then show ?case by simp
next
  case (Cons h t) then show ?case
  apply (induct t)
  apply auto
done
qed

lemma comp_assoc:
  assumes "arity B b"
  assumes "b > 1"
  shows"A . (B . C) = (A . B) . C"
  proof -
    from `arity B b` and `b > 1`
    show ?thesis
    apply (auto simp add: comp_def arity_def)
    apply (frule neq_Nil_conv_l)
    apply (erule exE)
    apply (erule exE)
    apply (rule_tac x = "xs @ ysb" in exI)
    apply (rule_tac x = "ysa" in exI) 
    apply (rule conjI)
    apply simp
    apply (rule_tac x = "wa" in exI)
    apply (rule conjI)
    apply (rule_tac x = "xs" in exI)
    apply (rule_tac x = "ysb @ [wa]" in exI)
    apply (rule conjI)
    apply simp
    apply (rule_tac x = "w" in exI)
    apply simp
    apply simp
    apply (rule_tac x = "xsa" in exI)
    apply (frule neq_Nil_conv_r)
    apply (erule exE)
    apply (erule exE)
    apply (rule_tac x = "ysb @ ys" in exI)
    apply auto
    apply (rule_tac x = "wa" in exI)
    apply auto
    apply (rule_tac x = "wa # ysb" in exI)
    apply auto
  done
qed

lemma doma_eq': "(x @ y : S) = (x @ y : {x} <: S)"
  apply (auto simp add: doma_def)
done

lemma doma_eq: "(R -> S in T) = (R -> S in R <: T)"
  apply (auto simp add: doma_def prod_def doma_eq')
done

lemma no_doma:
  assumes "R <= univ"
  shows "(R . S = {}) = (R <: S = {})"
proof
  show "R <: S = {} ==> R . S = {}"
  proof
    show "R <: S = {} ==> {} <= R . S" by auto
    from `R <= univ`
    show "R <: S = {} ==> R . S <= {}"
      apply (simp only: comp_def)
      apply auto
      apply (subgoal_tac "xs = []")
      prefer 2
      apply (auto simp: univ_def)
      apply (auto simp: doma_def)
      apply (drule_tac x = "w # ys" in spec)
      apply auto
      apply (drule_tac x = "[w]" in spec)
      apply auto
      done
  qed
  show "R . S = {} ==> R <: S = {}"
  proof
    show "R . S = {} ==> {} <= R <: S" by auto
    from `R <= univ`
    show "R . S = {} ==> R <: S <= {}"
      apply (auto simp: doma_def)
      apply (drule_tac c = "y" in subsetD)
      apply (auto simp: univ_def)
      apply (auto simp: comp_def)
      apply (drule_tac x = "[]" in spec)
      apply auto
      done
  qed
qed

lemma prod_assoc:
  shows "A -> (B -> C) = (A -> B) -> C"
  apply (auto simp add: prod_def)
  apply (rule_tac x = "xa @ xb" in exI)
  apply auto
done

lemma prod_Un_dist:
  shows "A -> (B + C) = A -> B + A -> C"
  apply (auto simp add: prod_def)
done

lemma prod_Int_dist:
  shows "arity A x ==> A -> (B & C) = A -> B & A -> C"
  apply (auto simp add: prod_def)
  apply (rule_tac x = xb in exI)
  apply (rule_tac x = ya in exI)
  apply (auto simp add: arity_def Ball_def)
  apply (frule_tac x = xa in spec)
  apply (drule_tac x = xb in spec)
  apply auto
done

lemma comp_prod:
  assumes "A <= univ"
  assumes "B <= univ"
  assumes "X <= (A . (B -> C))"
  shows "X <= C"
  proof -
    from `B <= univ` and `A <= univ` and `X <= (A . (B -> C))`
    show ?thesis
    apply (rule_tac A = "X" in subsetI)
    apply (drule_tac c = "x" and A = "X" and B = "A . (B -> C)" in subsetD)
    apply (auto simp add: comp_def prod_def)
    apply (drule_tac A = "A" and B = "univ" and c = "xs @ [w]" in subsetD)
    apply auto
    apply (drule_tac A = "B" and B = "univ" and c = xa in subsetD)
    apply auto
    apply (auto simp add: univ_def)
    done
  qed


lemma prod_to_comp:
assumes "A <= univ"
assumes "some A"
shows "((A -> B) <= C) ==> (B <= (A . C))"
proof -
    assume "(A -> B) <= C"
    from this and `A <= univ` and `some A`
    show ?thesis
    apply (simp add: some_def)
    apply (erule_tac exE)
    apply (drule_tac A = A and B = univ and c = x in subsetD)
    apply (auto simp add: comp_def univ_def)
    apply (rule_tac x = "[]" in exI)
    apply auto
    apply (rule_tac x = "xb" in exI)
    apply auto
    apply (elim subsetD)
    apply (auto simp add: prod_def)
    apply (rule_tac x = "[xb]" in exI)
    by auto
qed

lemma comp_to_prod:
assumes "{a} <= univ"
shows "(B <= ({a} . C)) ==> (({a} -> B) <= C)"
proof -
    assume "B <= ({a} . C)" from this and `{a} <= univ` show "{a} -> B <= C" by (auto simp add: prod_def comp_def univ_def)
qed

lemma plus_minus:
assumes "no (R & S)"
shows "R Un S - S = R"
proof
    show "R Un S - S <= R" by auto
    from `no (R & S)` show "R <= R Un S - S" by (auto simp add: no_def)
qed

lemma no_prod_in_comp:
assumes "R <= univ"
assumes "no (R . S)"
assumes "X in R"
shows "no (S & (X -> T))"
proof (auto simp add: no_def)
    fix x
    assume in_S: "x : S" and in_p: "x : X -> T"
    with `R <= univ` and `no (R . S)` and `X in R` show "False"
    apply (auto simp add: univ_def no_def comp_def prod_def)
    apply (subgoal_tac "EX t. [t] = x")
    apply auto
    apply (drule_tac x = "[]" in spec)
    apply (drule_tac x = "y" in spec)
    apply (drule_tac x = "t" in spec)
    apply auto
    done
qed

lemma comp_mono_l:
assumes "A <= B"
shows "C . A <= C . B"
proof -
    from `A <= B` show ?thesis by (auto simp add: comp_def)
qed

lemma comp_mono_r:
assumes "A <= B"
shows "A . C <= B . C"
proof -
    from `A <= B` show ?thesis by (auto simp add: comp_def)
qed

lemma comp_doma_eq:
assumes "A <= univ"
shows "A . (A <: B) = A . B"
proof -
    from `A <= univ` show ?thesis
        apply (auto simp add: univ_def comp_def doma_def)
        apply (drule_tac c = "xs @ [w]" in subsetD)
        apply auto
        apply (rule_tac x = "[]" in exI)
        apply (rule_tac x = ys in exI)
        apply auto
        apply (rule_tac x = w in exI)
        by auto
qed        

lemma comp_prod_eq:
  assumes "A <= univ"
  assumes "B <= A"
  assumes "EX x. x : B"
  shows "A . (B -> C) = C"
  proof -
    from `A <= univ` and `B <= A` and `EX x. x : B`
    show ?thesis
    apply (auto simp add: comp_def prod_def)
    apply (frule_tac B = "A" in set_rev_mp)
    apply auto
    apply (frule_tac A = "A" and B = "univ" in set_rev_mp)
    apply auto
    apply (simp only: univ_def)
    apply auto
    apply (rule_tac x = "[]" in exI)
    apply (rule_tac x = "xa" in exI)
    apply auto
    apply (frule_tac B = "A" in set_rev_mp)
    apply auto
    apply (frule_tac A = "A" and B = "univ" in set_rev_mp)
    apply auto
    apply (simp add: univ_def)
    apply (erule exE)
    apply (rule_tac x = "xb" in exI)
    apply (rule conjI)
    apply simp
    apply (rule_tac x = "x" in exI)
    apply (rule_tac x = "xa" in exI)
    apply auto
    done
  qed

(* transitive closure related lemmas *)

lemma trcl_empty:
    shows "trcl {} = iden"
    proof
    show "trcl {} <= iden"
        apply auto
        apply (erule_tac P = "%x. x : iden" in trcl.induct)
        apply auto
        done
    show "iden <= trcl {}"
        apply auto
        apply (rule trcl.base)
        apply auto
        done
    qed

lemma iden_in_trcl:
    shows "iden <= trcl R"
    apply auto
    apply (rule trcl.base)
    apply auto
    done

(* Transitive Closure *)

lemma tcl_in:
assumes "X in univ"
assumes "R in X -> X"
shows "^R in X -> X"
proof
    fix x
    assume "x : ^R"
    from this show "x : X -> X"
    proof induct
        fix i j
        assume "[i, j] : R" with `R in X -> X` show "[i, j] : X -> X" by auto 
    next
        fix i j k
        assume "[i, j] : R" with `R in X -> X` have x: "[i, j] : X -> X" by auto
        assume "[j, k] : X -> X" with x and `X in univ` show "[i, k] : X -> X"
        apply (auto simp add: univ_def prod_def)
        apply (rule_tac x = "[i]" in exI)
        apply (rule_tac x = "[k]" in exI)
        by auto
    qed
qed

lemma tcl_induct [consumes 1, case_names base step, induct set: tcl]:
assumes a: "[i, j] : ^r" 
assumes base: "!!i j. [i, j] : r \<Longrightarrow> P i j"
assumes step: "!!i j k. \<lbrakk>[i, j] : r; [j, k] : ^r; P j k\<rbrakk> \<Longrightarrow> P i k"
shows "P i j"
proof -
    from a show ?thesis
    proof (drule_tac P = "%x => case x of
                                    Nil => True |
                                    Cons a b => case b of
                                        Nil => True |
                                        Cons a' b' => case b' of
                                            Nil => P a a' |
                                            Cons a'' b'' => True" in tcl.induct)
        fix i j
        assume "[i, j] : r" with base have "P i j" by simp
        from this show "case [i, j] of [] \<Rightarrow> True | [a] \<Rightarrow> True | [a, a'] \<Rightarrow> P a a' | a # a' # a'' # b'' \<Rightarrow> True" by simp
    next
        fix i j k
        assume "case [j, k] of [] \<Rightarrow> True | [a] \<Rightarrow> True | [a, a'] \<Rightarrow> P a a' | a # a' # a'' # b'' \<Rightarrow> True" hence P: "P j k" by simp
        assume "[i, j] : r" and "[j, k] : ^r" with P and step show "case [i, k] of [] \<Rightarrow> True | [a] \<Rightarrow> True | [a, a'] \<Rightarrow> P a a' | a # a' # a'' # b'' \<Rightarrow> True" by simp
    next
       assume "case [i, j] of [] \<Rightarrow> True | [a] \<Rightarrow> True | [a, a'] \<Rightarrow> P a a' | a # a' # a'' # b'' \<Rightarrow> True"
       thus "P i j" by simp
    qed
qed


lemma trcl_induct [consumes 1, case_names base step, induct set: trcl]:
assumes a: "[i, j] : *r" 
assumes base: "!!i. P i i"
assumes step: "!!i j k. \<lbrakk>[i, j] : r; [j, k] : *r; P j k\<rbrakk> \<Longrightarrow> P i k"
shows "P i j"
proof -
    from a show ?thesis
    proof (drule_tac P = "%x => case x of
                                    Nil => True |
                                    Cons a b => case b of
                                        Nil => True |
                                        Cons a' b' => case b' of
                                            Nil => P a a' |
                                            Cons a'' b'' => True" in trcl.induct)
        fix i
        assume "i : iden" with base show "case i of [] \<Rightarrow> True | [a] \<Rightarrow> True | [a, a'] \<Rightarrow> P a a' | a # a' # a'' # b'' \<Rightarrow> True" by (auto simp add: iden_def)
    next
        fix i j k
        assume "case [j, k] of [] \<Rightarrow> True | [a] \<Rightarrow> True | [a, a'] \<Rightarrow> P a a' | a # a' # a'' # b'' \<Rightarrow> True" hence P: "P j k" by simp
        assume "[i, j] : r" and "[j, k] : *r" with P and step show "case [i, k] of [] \<Rightarrow> True | [a] \<Rightarrow> True | [a, a'] \<Rightarrow> P a a' | a # a' # a'' # b'' \<Rightarrow> True" by simp
    next
       assume "case [i, j] of [] \<Rightarrow> True | [a] \<Rightarrow> True | [a, a'] \<Rightarrow> P a a' | a # a' # a'' # b'' \<Rightarrow> True"
       thus "P i j" by simp
    qed
qed

lemma trcl_base:
"[i, j] : iden ==> [i, j] : *R" by (auto simp add: iden_def trcl.base)

lemma trcl_base':
"[i, i] : *R" by (auto simp add: iden_def trcl.base)

lemma trcl_step1:
"[i, j] : R ==> [i, j] : *R"
proof -
    have p: "[j, j] : *R" by (auto simp add: trcl_base iden_def)
    assume "[i, j] : R" with p show "[i, j] : *R" by (simp add: trcl.step)
qed

lemma tcl_in_trcl:
"^R in *R"
proof auto
    fix x
    assume "x : ^R" thus "x : *R" by induct (auto simp add: trcl_step1 trcl.step)
qed
        
lemma trans_tcl: 
"[i, j] : ^R ==> [j, k] : ^R ==> [i, k] : ^R"
proof (induct rule: tcl_induct)
    case (base i j) with tcl.step show ?case by simp
next
    case (step i j l) with tcl.step show ?case by simp
qed

lemma trans_trcl: 
"[i, j] : *R ==> [j, k] : *R ==> [i, k] : *R"
proof (induct rule: trcl_induct)
    case (base i) thus ?case by simp
next
    case (step i j l) with trcl.step show ?case by simp
qed

lemma l_tcl_step: "[i, j] : ^R ==> [j, k] : R ==> [i, k] : ^R"
proof (induct rule: tcl_induct)
    case (base i j) with tcl.base and tcl.step show ?case by simp
next
    case (step i j l) with tcl.step show ?case by simp
qed

lemma l_trcl_step: "[i, j] : *R ==> [j, k] : R ==> [i, k] : *R"
proof (induct rule: trcl_induct)
    case (base i) with trcl_step1 show ?case by simp
next
    case (step i j l) with trcl.step show ?case by simp
qed

lemma f_tcl:
assumes "N <= univ"
assumes "L <= univ"
assumes "finite N"
assumes "ALL n : N. EX x : N Un L. n @ x : T"
assumes "~(EX n : N. {n} <= {n} . ^T)"
shows "ALL n : N. EX l : L. (n @ l : ^T)"
proof -
    from `~(EX n : N. {n} <= {n} . ^T)` and `N <= univ` have "ALL n : N. n @ n ~: ^T"
    proof (auto simp add: Bex_def)
        fix n
        assume "\<forall>x. x \<in> N \<longrightarrow> x \<notin> {x} . ^T" and "n \<in> N" and "n @ n \<in> ^T" and "N <= univ"
        then show "False" by (auto simp add: comp_def univ_def)
    qed
    from`finite N` and this and `N <= univ`
    show "!!L. [| ALL n : N. EX x : N Un L. n @ x : T; L <= univ |]
               ==> ALL n : N. EX l : L. n @ l : ^T"
    proof induct
        case empty then show ?case by simp
    next
        case (insert n' N)
        have I: "[| ALL n:N. EX x:N Un ({n'} Un L). n @ x : T; ({n'} Un L) <= univ; ALL n : N. n @ n ~: ^T; N <= univ |]
                    ==> ALL n:N. EX l:({n'} Un L). n @ l : ^T" by fact
        assume P: "ALL n:insert n' N. EX x:insert n' N Un L. n @ x : T"
        hence PN: "ALL n:N. EX x:insert n' N Un L. n @ x : T" by simp
        assume U: "insert n' N <= univ" hence U': "N <= univ" and L'': "n' : univ" by auto
        assume L: "L <= univ" with L'' have L': "({n'} Un L) <= univ" by simp
        assume C: "ALL n : insert n' N. n @ n ~: ^T"
        with I and PN and U' and L' have S: "ALL n:N. EX l:({n'} Un L). n @ l : ^T" by simp
        show ?case
        proof clarify
            fix n
            assume "n : insert n' N"
            with P have In: "n = n' | n : N" and P': "EX x : insert n' N Un L. n @ x : T" by auto
            from In show "EX l : L. n @ l : ^T"
            proof (rule disjE)
                from C have C': "n' @ n' ~: ^T" by auto
                from U have U': "EX i. n' = [i]" by (auto simp add: univ_def)
                assume "n = n'"
                with P' and C' and S show "EX l : L. n @ l : ^T"
                proof auto
                    assume "n' @ n' ~: ^T" and "n' @ n' : T"
                    with U' show "EX l : L. n' @ l : ^T" by (auto simp add: tcl.base)
                next
                    fix x
                    assume "x : N" with U have U'': "EX j. x = [j]" by (auto simp add: univ_def)
                    assume "ALL n:N. n @ n' : ^T | (EX l:L. n @ l : ^T)" and "x : N"
                    hence S': "x @ n' : ^T | (EX l:L. x @ l : ^T)" by simp
                    assume "n' @ n' ~: ^T" and "n' @ x : T"
                    with S' show "EX l : L. n' @ l : ^T"
                    proof auto
                        assume "n' @ x : T" and "x @ n' : ^T" and "n' @ n' ~: ^T"
                        with U' and U'' show "EX l:L. n' @ l : ^T" by (auto simp add: tcl.step)
                    next
                        fix l
                        assume L''': "l : L" with L have L'': "EX k. l = [k]" by (auto simp add: univ_def)
                        assume "n' @ x : T" and "x @ l : ^T"
                        with L'' and U' and U'' have "n' @ l : ^T" by (auto simp add: tcl.step)
                        with L''' show "EX l:L. n' @ l : ^T" by auto
                    qed
                next
                    fix x
                    assume L''': "x : L" with L have L'': "EX k. x = [k]" by (auto simp add: univ_def)
                    assume "n' @ x : T" with L'' and U' have "n' @ x : ^T" by (auto simp add: tcl.base)
                    with L''' show "EX l:L. n' @ l : ^T" by auto
                qed
            next
                from P have P': "EX x:insert n' N Un L. n' @ x : T" by auto
                from U have U': "EX i. n' = [i]" by (auto simp add: univ_def)
                assume "n : N" with U have N: "EX h. n = [h]" by (auto simp add: univ_def)
                assume "n : N"
                with S have "EX x:{n'} Un L. n @ x : ^T" by auto
                from this and P' show "EX l : L. n @ l : ^T"
                proof auto
                    assume "n' @ n' : T" with U' have "n' @ n' : ^T" by (auto simp add: tcl.base)
                    from this and C show "EX l:L. n @ l : ^T" by auto
                next
                    fix x
                    assume "x : N" with U have L'': "EX k. x = [k]" by (auto simp add: univ_def)
                    assume "x : N"
                    with S have P': "EX l:{n'} Un L. x @ l : ^T" by simp
                    assume "n @ n' : ^T" and "n' @ x : T" with P' show "EX l : L. n @ l : ^T"
                    proof auto
                        assume "x @ n' : ^T" and "n' @ x : T"
                        with U' and L'' have T: "n' @ n' : ^T" by (auto simp add: tcl.step)
                        with C show "EX l : L. n @ l : ^T" by auto
                    next
                        fix l 
                        assume "n @ n' : ^T" and "n' @ x : T" with U' and N and L''
                        have T: "n @ x : ^T" by (auto simp add: l_tcl_step)
                        assume "l : L" with L have L': "EX m. l = [m]" by (auto simp add: univ_def)
                        assume "x @ l : ^T"
                        with T and N and L'' and L' have F: "n @ l : ^T"
                        apply auto
                        apply (rule_tac j = "k" in trans_tcl)
                        by auto
                        assume "l : L" with F show "EX l : L. n @ l : ^T" by auto
                    qed
                next
                    fix x
                    assume "x : L" with L have L'': "EX k. x = [k]" by (auto simp add: univ_def)
                    assume "n @ n' : ^T" and "n' @ x : T"
                    with U' and N and L'' have F: "n @ x : ^T" by (auto simp add: l_tcl_step)
                    assume "x : L" with F show "EX l : L. n @ l : ^T" by auto
                qed
            qed
        qed
    qed      
    show "ALL n:N. EX x:N Un L. n @ x : T" by fact
    show "L <= univ" by fact
qed

end

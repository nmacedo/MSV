{*
Model of least-change lenses
 
Demonstrations and properties for the paper:
[1] N. Macedo, H. Pacheco, A. Cunha and J. N. Oliveira. Composing Least-change Lenses, 2013
  
Author: alcino
*}
 
 theory LeastChangeLenses

imports Main

begin

class metricspace =
  fixes dist :: "'a \<Rightarrow> 'a \<Rightarrow> nat" (infix "\<Delta>" 100)
  assumes identityofindiscernibles: "x \<Delta> y = 0 \<longleftrightarrow> x = y"
  assumes symmetry: "x \<Delta> y = y \<Delta> x"
  assumes triangleinequality: "x \<Delta> z \<le> x \<Delta> y + y \<Delta> z"
begin
definition
  ilte :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "ilte y x z = (x \<Delta> y \<le> x \<Delta> z)"
notation
  ilte ("_ \<sqsubseteq>\<^sub>_ _" [51, 51, 51] 50)
lemma reflexivity: "y \<sqsubseteq>\<^sub>x y" by (simp add: ilte_def)
lemma transitivity: "y \<sqsubseteq>\<^sub>x z \<and> z \<sqsubseteq>\<^sub>x w \<Longrightarrow> y \<sqsubseteq>\<^sub>x w" by (simp add: ilte_def)
lemma totality: "y \<sqsubseteq>\<^sub>x z \<or> z \<sqsubseteq>\<^sub>x y" by (auto simp: ilte_def)
lemma stability: "y \<sqsubseteq>\<^sub>x x \<longleftrightarrow> x = y"
  proof
    assume "y \<sqsubseteq>\<^sub>x x" 
    have "x \<Delta> x = 0" by (auto simp: identityofindiscernibles)
    hence "x \<Delta> y = 0" using `y \<sqsubseteq>\<^sub>x x`by (auto simp: ilte_def)
    thus "x = y" by (auto simp: identityofindiscernibles)
  next
    assume "x = y"
    thus "y \<sqsubseteq>\<^sub>x x" by (auto simp: reflexivity)
  qed
lemma smallest: "x \<sqsubseteq>\<^sub>x y"
  proof -
    have "x \<Delta> x = 0" by (auto simp: identityofindiscernibles)
    thus ?thesis by (auto simp: ilte_def)
  qed
definition
  ilt :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "ilt y x z = (\<not>(z \<sqsubseteq>\<^sub>x y))"
notation
  ilt ("_ \<sqsubset>\<^sub>_ _" [51, 51, 51] 50)
end

instantiation nat :: metricspace
begin
definition
  dist_nat: "x \<Delta> y = (x - y) + (y - x)"
instance 
proof
  fix x y :: nat
  show "x \<Delta> y = y \<Delta> x" by (simp add: dist_nat)
next
  fix x y :: nat
  show "x \<Delta> y = 0 \<longleftrightarrow> x = y" by (auto simp: dist_nat)
next
  fix x y z :: nat
  show "x \<Delta> z \<le> x \<Delta> y + y \<Delta> z" by (auto simp: dist_nat)
qed
end

definition 
  sym_diff :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" (infix "\<ominus>" 70) where
  "x \<ominus> y = (x-y) \<union> (y-x)"

lemma sym_diff_in_union: "a \<ominus> b \<subseteq> a \<ominus> c \<union> c \<ominus> b" by (auto simp: sym_diff_def)

instantiation set :: (finite) metricspace
begin
definition
  dist_set: "a \<Delta> b = card (a \<ominus> b)"
instance
proof
  fix x y :: "'a set"
  show "x \<Delta> y = y \<Delta> x" by (auto simp: dist_set Un_commute sym_diff_def)
next
  fix x y :: "'a set"
  show "x \<Delta> y = 0 \<longleftrightarrow> x = y" by (auto simp: dist_set sym_diff_def)
next
  fix x y z :: "'a set"
  have "card (x \<ominus> z) \<le> card (x \<ominus> y \<union> y \<ominus> z)" by (intro card_mono, auto simp: sym_diff_in_union)
  thus "x \<Delta> z \<le> x \<Delta> y + y \<Delta> z" by (simp only: dist_set, subst card_Un_Int, auto)
qed
end

record ('a::metricspace,'b::metricspace) lens = 
  get :: "'a \<Rightarrow> 'b"
  put :: "'a \<Rightarrow> 'b \<Rightarrow> 'a set"

definition getput :: "('a::metricspace,'b::metricspace) lens \<Rightarrow> bool" where
  "getput l \<equiv> \<forall> v s . v = get l s \<longrightarrow> s \<in> put l s v"

definition putget :: "('a::metricspace,'b::metricspace) lens \<Rightarrow> bool" where
  "putget l \<equiv> \<forall> v s s'. s' \<in> put l s v \<longrightarrow> v = get l s'"

definition wblens :: "('a::metricspace,'b::metricspace) lens \<Rightarrow> bool" where
  "wblens l \<equiv> getput l \<and> putget l"

lemma getput:
  "getput l \<Longrightarrow> v = get l s \<Longrightarrow> s \<in> put l s v" by (simp add: getput_def)

lemma putget:
  "putget l \<Longrightarrow> s' \<in> put l s v \<Longrightarrow> v = get l s'" by (simp add: putget_def)

definition comp :: "('b::metricspace,'c::metricspace) lens \<Rightarrow> ('a::metricspace,'b) lens \<Rightarrow> ('a,'c) lens" (infix "\<bullet>" 55) where
  "g \<bullet> f = \<lparr> get = (get g) \<circ> (get f), put = \<lambda> s v . Set.bind (put g (get f s) v) (put f s) \<rparr>"

lemma compwblens:
  assumes "wblens g"
  assumes "wblens f"
  shows "wblens (g \<bullet> f)" using assms by (auto simp:wblens_def putget_def getput_def comp_def)

definition deterministic :: "('a::metricspace,'b::metricspace) lens \<Rightarrow> bool" where
  "deterministic l \<equiv> \<forall> v s s1 s2. s1 \<in> put l s v \<and> s2 \<in> put l s v \<longrightarrow> s1 = s2"

lemma deterministic:
  "deterministic l \<Longrightarrow> s1 \<in> put l s v \<Longrightarrow> s2 \<in> put l s v \<Longrightarrow> s1 = s2" by (auto simp: deterministic_def)

lemma compdeterministic:
  assumes "deterministic g"
  assumes "deterministic f"
  shows "deterministic (g \<bullet> f)" using assms by (auto simp: deterministic_def comp_def, blast)
  
definition leastputget :: "('a::metricspace,'b::metricspace) lens \<Rightarrow> bool" where
  "leastputget l \<equiv> \<forall> v s s'. s' \<in> put l s v \<longrightarrow> v = get l s' \<and> (\<forall> s1 . v = get l s1 \<longrightarrow> s' \<sqsubseteq>\<^sub>s s1)"

lemma leastputget_putget:
  "leastputget f \<Longrightarrow> putget f" using assms by (auto simp: leastputget_def putget_def)

lemma leastputget:
  "leastputget l \<Longrightarrow> a \<in> put l s (get l b) \<Longrightarrow> a \<sqsubseteq>\<^sub>s b" by (auto simp: leastputget_def)

definition wblclens :: "('a::metricspace,'b::metricspace) lens \<Rightarrow> bool" where
  "wblclens l \<equiv> getput l \<and> leastputget l \<and> deterministic l"

definition leastgetput :: "('a::metricspace,'b::metricspace) lens \<Rightarrow> bool" where
  "leastgetput l \<equiv> \<forall> v s s'. v = get l s' \<and> (\<forall> s1 . v = get l s1 \<longrightarrow> s' \<sqsubseteq>\<^sub>s s1) \<longrightarrow> s' \<in> put l s v"

lemma leastgetput:
  "leastgetput l \<Longrightarrow> v = get l s' \<Longrightarrow> (\<forall> s1 . v = get l s1 \<longrightarrow> s' \<sqsubseteq>\<^sub>s s1) \<Longrightarrow> s' \<in> put l s v" by (auto simp: leastgetput_def)

(* The following is essentially proposition 1 *)
lemma leastgetput_getput:
  "leastgetput f \<Longrightarrow> getput f" by (simp only: getput_def, auto, rule leastgetput, auto simp: smallest)

definition wbndlclens :: "('a::metricspace,'b::metricspace) lens \<Rightarrow> bool" where
  "wbndlclens l \<equiv> putget l \<and> leastgetput l"

lemma wblclens_wblens:
  "wblclens l \<Longrightarrow> wblens l" by (auto simp: wblclens_def wblens_def leastputget_putget)

lemma wbndlclens_wblens:
  "wbndlclens l \<Longrightarrow> wblens l" by (auto simp: wbndlclens_def wblens_def leastgetput_getput)
  
lemma injectivelens:
  assumes "wblens l"
  assumes "inj (get l)"
  assumes "x \<in> put l s' (get l s)"
  shows "x = s"
proof (rule injD [OF `inj (get l)`])
  from `wblens l`
  have "putget l" by (simp add: wblens_def)
  thus "get l x = get l s" using `x \<in> put l s' (get l s)` by (simp add: putget_def)
qed

lemma injectivelensisdeterministic:
  assumes "wblens l"
  assumes "inj (get l)"
  shows "deterministic l" 
proof (simp add: deterministic_def, clarify)
  fix s v s1 s2
  assume "s1 \<in> put l s v" and "s2 \<in> put l s v"
  hence "get l s1 = get l s2" using `wblens l` by (auto simp: wblens_def putget_def)
  thus "s1 = s2" by (rule injD [OF `inj (get l)`])
qed

lemma injectivelensislclens:
  assumes "wblens l"
  assumes "inj (get l)"
  shows "wblclens l"
proof -
  have "deterministic l" using assms by (simp add: injectivelensisdeterministic)
  moreover
  have "getput l" using assms by (simp add: wblens_def)
  moreover
  have "leastputget l"
  proof (simp only: leastputget_def, clarify, rule conjI)
    fix v s s'
    assume "s' \<in> put l s v"
    thus "v = get l s'" using `wblens l` by (auto simp: wblens_def putget_def)
  next
    fix v s s'
    assume "s' \<in> put l s v"
    thus "\<forall> s1 . v = get l s1 \<longrightarrow> s' \<sqsubseteq>\<^sub>s s1"
    proof (clarify)
      fix s1
      assume "s' \<in> put l s (get l s1)"
      hence "s' = s1" by (rule injectivelens [OF `wblens l` `inj (get l)`])
      thus " s' \<sqsubseteq>\<^sub>s s1" by (auto simp: reflexivity)
    qed
  qed
  ultimately show ?thesis by (simp add: wblclens_def)
qed

lemma proposition6:
  assumes "wblens g"
  assumes "inj (get g)"
  assumes "wblclens f"
  shows "wblclens (g \<bullet> f)"
proof -
  have "wblens f" by (rule wblclens_wblens [OF `wblclens f`])
  hence "wblens (g \<bullet> f)" by (auto simp: compwblens [OF `wblens g`])  
  hence "getput (g \<bullet> f)" and "putget (g \<bullet> f)" by (auto simp: wblens_def)
  moreover
  hence "leastputget (g \<bullet> f)" using assms by (auto simp: leastputget_def putget_def wblclens_def comp_def injectivelens)
  moreover
  have "deterministic (g \<bullet> f)" using assms by (auto simp: wblclens_def injectivelensisdeterministic compdeterministic)
  ultimately show ?thesis by (simp add: wblclens_def)
qed

definition strictlyincreasing :: "('a::metricspace \<Rightarrow> 'b::metricspace) \<Rightarrow> bool" where
  "strictlyincreasing f \<equiv> (\<forall> s1 s2 s . (f s1) \<sqsubseteq>\<^sub>(f s) (f s2) \<longrightarrow> s1 \<sqsubseteq>\<^sub>s s2)"

lemma strictlyincreasing:
  "strictlyincreasing f \<Longrightarrow> (f a) \<sqsubseteq>\<^sub>(f s) (f b) \<Longrightarrow> a \<sqsubseteq>\<^sub>s b" by (auto simp: strictlyincreasing_def)

lemma strictlyincreasingisinjective:
  assumes "strictlyincreasing f"
  shows "inj f"
proof (rule injI)
  fix x y
  assume "f x = f y"
  hence "f x \<sqsubseteq>\<^sub>(f y) f y" by (auto simp: stability)
  hence "x \<sqsubseteq>\<^sub>y y" by (rule strictlyincreasing [OF `strictlyincreasing f`])
  thus "x = y" by (auto simp: stability)
qed

lemma proposition7:
  assumes "wblclens g"
  assumes "wblens f"
  assumes "strictlyincreasing (get f)"
  shows "wblclens (g \<bullet> f)"
proof -
  have "leastputget g" using assms by (auto simp: wblclens_def)
  have "putget f" using assms by (auto simp: wblens_def)
  have "wblens g" using assms by (auto simp: wblclens_wblens)
  hence "wblens (g \<bullet> f)" using assms by (simp add: compwblens)
  hence "getput (g \<bullet> f)" and "putget (g \<bullet> f)" by (auto simp: wblens_def)
  moreover
  from `strictlyincreasing (get f)` have "inj (get f)" by (rule strictlyincreasingisinjective)
  hence "deterministic f" using `wblens f` by (simp add: injectivelensisdeterministic)
  hence "deterministic (g \<bullet> f)" using assms by (auto simp: wblclens_def compdeterministic)
  moreover
  have "leastputget (g \<bullet> f)"
  proof (simp add: leastputget_def, auto)
    fix v s a
    assume "a \<in> put (g \<bullet> f) s v"
    thus "v = get (g \<bullet> f) a" by (rule putget [OF `putget (g \<bullet> f)`])
  next
    fix s a b
    assume "a \<in> put (g \<bullet> f) s (get (g \<bullet> f) b)"
    then obtain x where "x \<in> put g (get f s) (get g (get f b))" and "a \<in> put f s x" by (auto simp: comp_def)
    hence "get f a \<in> put g (get f s) (get g (get f b))" using `putget f` by (auto simp: putget_def)
    hence "(get f a) \<sqsubseteq>\<^sub>(get f s) (get f b)" using `leastputget g`by (auto simp: leastputget)
    thus "a \<sqsubseteq>\<^sub>s b" using `strictlyincreasing (get f)` by (auto simp: strictlyincreasing)
  qed
  ultimately show ?thesis by (auto simp: wblclens_def)
qed

lemma proposition8:
  assumes "strictlyincreasing g"
  assumes "strictlyincreasing f"
  shows "strictlyincreasing (g \<circ> f)"
proof (auto simp: strictlyincreasing_def)
  fix a b s
  assume "g (f a) \<sqsubseteq>\<^sub>g (f s) g (f b)"
  hence "f a \<sqsubseteq>\<^sub>f s f b" using `strictlyincreasing g` by (simp add: strictlyincreasing)
  thus "a \<sqsubseteq>\<^sub>s b" using `strictlyincreasing f` by (simp add: strictlyincreasing)
qed

definition quasistrictlyincreasing :: "('a::metricspace \<Rightarrow> 'b::metricspace) \<Rightarrow> bool" where
  "quasistrictlyincreasing f \<equiv> (\<forall> a b s . (f a) \<sqsubseteq>\<^sub>(f s) (f b) \<longrightarrow> (\<exists> c . f c = f a \<and> c \<sqsubseteq>\<^sub>s b))"

lemma quasistrictlyincreasing:
  "quasistrictlyincreasing f \<Longrightarrow> (f a) \<sqsubseteq>\<^sub>(f s) (f b) \<Longrightarrow> \<exists> c . f c = f a \<and> c \<sqsubseteq>\<^sub>s b" by (simp add: quasistrictlyincreasing_def)

lemma strictlyincreasingisquasi:
  "strictlyincreasing f \<Longrightarrow> quasistrictlyincreasing f" by (auto simp: strictlyincreasing_def quasistrictlyincreasing_def)

lemma proposition9:
  assumes "wblclens g"
  assumes "wblclens f"
  assumes "quasistrictlyincreasing (get f)"
  shows "wblclens (g \<bullet> f)"
proof -
  have "wblens g" and "wblens f" using assms by (auto simp: wblclens_wblens)
  hence "wblens (g \<bullet> f)" using assms by (simp add: compwblens)
  hence "getput (g \<bullet> f)" and "putget (g \<bullet> f)" by (auto simp: wblens_def)
  moreover
  have "deterministic (g \<bullet> f)" using assms by (auto simp: wblclens_def compdeterministic)
  moreover
  have "putget f" using `wblens f` by (auto simp: wblens_def)
  have "leastputget g" using `wblclens g` by (auto simp: wblclens_def)
  have "leastputget f" using `wblclens f` by (auto simp: wblclens_def)
  have "leastputget (g \<bullet> f)"
  proof (simp add: leastputget_def, auto)
    fix v s a
    assume "a \<in> put (g \<bullet> f) s v"
    thus "v = get (g \<bullet> f) a" by (rule putget [OF `putget (g \<bullet> f)`])
  next
    fix s a b
    assume "a \<in> put (g \<bullet> f) s (get (g \<bullet> f) b)"
    then obtain x where "x \<in> put g (get f s) (get g (get f b))" and "a \<in> put f s x" by (auto simp: comp_def)
    hence "get f a \<in> put g (get f s) (get g (get f b))" and H: "a \<in> put f s (get f a)" using `putget f` by (auto simp: putget_def)
    hence "(get f a) \<sqsubseteq>\<^sub>(get f s) (get f b)" using `leastputget g`by (auto simp: leastputget)
    then obtain c where "get f c = get f a" and "c \<sqsubseteq>\<^sub>s b" using `quasistrictlyincreasing (get f)` by (auto simp: quasistrictlyincreasing_def, blast)
    hence "a \<in> put f s (get f c)" using H by simp
    hence "a \<sqsubseteq>\<^sub>s c \<and> c \<sqsubseteq>\<^sub>s b" using `leastputget f` and `c \<sqsubseteq>\<^sub>s b` by (auto simp: leastputget)
    thus "a \<sqsubseteq>\<^sub>s b" by (rule transitivity)
  qed 
  ultimately show ?thesis by (auto simp: wblclens_def)
qed

lemma proposition10:
  assumes "quasistrictlyincreasing g"
  assumes "quasistrictlyincreasing f"
  assumes "surj f"
  shows "quasistrictlyincreasing (g \<circ> f)"
proof (auto simp: quasistrictlyincreasing_def)
  fix a b s
  assume "g (f a) \<sqsubseteq>\<^sub>g (f s) g (f b)"
  hence "\<exists> x . g x = g (f a) \<and> x \<sqsubseteq>\<^sub>(f s) (f b)" using `quasistrictlyincreasing g` by (simp add: quasistrictlyincreasing)
  then obtain x where "g x = g (f a)" and "x \<sqsubseteq>\<^sub>(f s) (f b)" by auto
  obtain y where "x = f y" using `surj f` by auto
  hence "f y \<sqsubseteq>\<^sub>(f s) (f b)" using `x \<sqsubseteq>\<^sub>(f s) (f b)` by auto
  then obtain c where "f c = f y" and "c \<sqsubseteq>\<^sub>s b" using `quasistrictlyincreasing f` by (simp add: quasistrictlyincreasing_def, blast)
  hence "g (f c) = g (f a)" using `g x = g (f a)` and `x = f y`by auto
  thus "\<exists> c . g (f c) = g (f a) \<and> c \<sqsubseteq>\<^sub>s b" using `c \<sqsubseteq>\<^sub>s b` by auto
qed

definition 
  fork :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<times> 'c" where
  "fork f g \<equiv> (\<lambda> x . (f x, g x))"

lemma fstinvfork:
  "bij (fork f g) \<Longrightarrow> f (the_inv (fork f g) (x,y)) = x"
proof -
  assume "bij (fork f g)"
  hence "inj (fork f g)" by (simp add: bij_def)
  hence "fork f g (the_inv (fork f g) (x, y)) = (x,y)" 
  proof (rule f_the_inv_into_f)
    from `bij (fork f g)`
    have "surj (fork f g)" by (simp add: bij_def)
    thus "(x, y) \<in> range (fork f g)" by auto
  qed
  hence "fst (fork f g (the_inv (fork f g) (x, y))) = x" by simp
  thus ?thesis by (simp add: fork_def)
qed

lemma sndinvfork:
  "bij (fork f g) \<Longrightarrow> g (the_inv (fork f g) (x,y)) = y"
proof -
  assume "bij (fork f g)"
  hence "inj (fork f g)" by (simp add: bij_def)
  hence "fork f g (the_inv (fork f g) (x, y)) = (x,y)" 
  proof (rule f_the_inv_into_f)
    from `bij (fork f g)`
    have "surj (fork f g)" by (simp add: bij_def)
    thus "(x, y) \<in> range (fork f g)" by auto
  qed
  hence "snd (fork f g (the_inv (fork f g) (x, y))) = y" by simp
  thus ?thesis by (simp add: fork_def)
qed

lemma proposition11:
  assumes "bij (fork f g)"
  assumes "\<forall> s a b . (f a) \<sqsubseteq>\<^sub>(f s) (f b) \<and> g a = g b \<longrightarrow> a \<sqsubseteq>\<^sub>s b"
  shows "quasistrictlyincreasing f"
proof (auto simp: quasistrictlyincreasing_def)
  fix a b s
  assume "f a \<sqsubseteq>\<^sub>f s f b"
  show "\<exists>c. f c = f a \<and> c \<sqsubseteq>\<^sub>s b"
  proof (rule_tac x = "(the_inv (fork f g)) (f a, g b)" in exI, auto)
    show "f (the_inv (fork f g) (f a, g b)) = f a" using assms by (auto simp: fstinvfork)
  next
    have "(f a) \<sqsubseteq>\<^sub>(f s) (f b) \<longrightarrow> (the_inv (fork f g) (f a, g b)) \<sqsubseteq>\<^sub>s b" using assms by (auto simp: fstinvfork sndinvfork)
    thus "the_inv (fork f g) (f a, g b) \<sqsubseteq>\<^sub>s b" using `f a \<sqsubseteq>\<^sub>f s f b` by (auto simp: reflexivity)
  qed
qed
    
lemma injectivendlclens:
  assumes "wbndlclens l" (* it suffices for (put l) to be total ... *)
  assumes "inj (get l)"
  shows "s' \<in> put l s (get l s')"
proof (rule leastgetput, auto)
  show "leastgetput l" using `wbndlclens l` by (simp add: wbndlclens_def)
next
  fix s1
  assume "get l s' = get l s1"
  hence "s' = s1" by (rule injD [OF `inj (get l)`])
  thus "s' \<sqsubseteq>\<^sub>s s1" by (simp add: reflexivity)
qed

lemma proposition12:
  assumes "wbndlclens g"
  assumes "inj (get g)"
  assumes "wbndlclens f"
  shows "wbndlclens (g \<bullet> f)"
proof -
  have "wblens f" and "wblens g" using assms by (auto simp: wbndlclens_wblens)
  hence "wblens (g \<bullet> f)" using assms by (auto simp: compwblens)  
  hence "putget (g \<bullet> f)" by (auto simp: wblens_def)
  moreover
  from `wbndlclens f` have "leastgetput f" by (simp add: wbndlclens_def)
  have "leastgetput (g \<bullet> f)"
  proof (simp add: leastgetput_def comp_def, clarify)
    fix s a
    assume H: "\<forall> b . get g (get f a) = get g (get f b) \<longrightarrow> a \<sqsubseteq>\<^sub>s b"
    show "\<exists> x \<in> put g (get f s) (get g (get f a)) . a \<in> put f s x"
    proof (rule bexI [of _ "get f a"])
      show "get f a \<in> put g (get f s) (get g (get f a))" by (rule injectivendlclens [OF `wbndlclens g` `inj (get g)`])
    next
      from H have "\<forall> b . get f a = get f b \<longrightarrow> a \<sqsubseteq>\<^sub>s b" by auto
      thus "a \<in> put f s (get f a)" using `leastgetput f` by (auto simp: leastgetput)
    qed
  qed
  ultimately show ?thesis by (simp add: wbndlclens_def)
qed

definition monotonic :: "('a::metricspace \<Rightarrow> 'b::metricspace) \<Rightarrow> bool" where
  "monotonic f \<equiv> (\<forall> s1 s2 s . s1 \<sqsubseteq>\<^sub>s s2 \<longrightarrow> (f s1) \<sqsubseteq>\<^sub>(f s) (f s2))"

lemma monotonic:
  "monotonic f \<Longrightarrow> a \<sqsubseteq>\<^sub>s b \<Longrightarrow> (f a) \<sqsubseteq>\<^sub>(f s) (f b)" by (auto simp: monotonic_def)

lemma proposition13:
  assumes "wbndlclens g"
  assumes "wbndlclens f"
  assumes "surj (get f)"
  assumes "monotonic (get f)"
  shows "wbndlclens (g \<bullet> f)"
proof -
  have "wblens f" and "wblens g" using assms by (auto simp: wbndlclens_wblens)
  hence "wblens (g \<bullet> f)" using assms by (auto simp: compwblens)  
  hence "putget (g \<bullet> f)" by (auto simp: wblens_def)
  moreover
  from `wbndlclens g` have "leastgetput g" by (simp add: wbndlclens_def)
  from `wbndlclens f` have "leastgetput f" by (simp add: wbndlclens_def)
  have "leastgetput (g \<bullet> f)"
  proof (simp add: leastgetput_def comp_def, auto)
    fix s a
    assume H: "\<forall> b . get g (get f a) = get g (get f b) \<longrightarrow> a \<sqsubseteq>\<^sub>s b"
    have "\<forall> x . get g (get f a) = get g x \<longrightarrow> (get f a) \<sqsubseteq>\<^sub>(get f s) x"
    proof (auto)
      fix x
      assume "get g (get f a) = get g x"
      then obtain b where "x = get f b" and "get g (get f a) = get g (get f b)" using `surj (get f)` by auto
      hence "a \<sqsubseteq>\<^sub>s b" using H by auto
      hence "(get f a) \<sqsubseteq>\<^sub>(get f s) (get f b)" using `monotonic (get f)` by (simp add: monotonic)
      thus "(get f a) \<sqsubseteq>\<^sub>(get f s) x" using `x = get f b` by simp
    qed
    hence A: "get f a \<in> put g (get f s) (get g (get f a))" using `leastgetput g` by (auto simp: leastgetput)
    have "\<forall> y . get f a = get f y \<longrightarrow> a \<sqsubseteq>\<^sub>s y" using H by auto
    hence "a \<in> put f s (get f a)" using `leastgetput f` by (auto simp: leastgetput)
    thus "\<exists> x \<in> put g (get f s) (get g (get f a)) . a \<in> put f s x" by (rule bexI [OF _ A])
  qed
  ultimately show ?thesis by (simp add: wbndlclens_def)
qed

lemma proposition14:
  assumes "monotonic g"
  assumes "monotonic f"
  shows "monotonic (g \<circ> f)"
proof -
  show ?thesis using assms by (auto simp: monotonic_def)
qed

definition quasimonotonic :: "('a::metricspace \<Rightarrow> 'b::metricspace) \<Rightarrow> bool" where
  "quasimonotonic f \<equiv> (\<forall> a b s . (\<forall> c . f b = f c \<longrightarrow> a \<sqsubseteq>\<^sub>s c) \<longrightarrow> (f a) \<sqsubseteq>\<^sub>(f s) (f b))"

lemma quasimonotonic:
  "quasimonotonic f \<Longrightarrow> \<forall> c . f b = f c \<longrightarrow> a \<sqsubseteq>\<^sub>s c \<Longrightarrow> (f a) \<sqsubseteq>\<^sub>(f s) (f b)" by (simp add: quasimonotonic_def)

lemma monotonicisquasi:
  "monotonic f \<Longrightarrow> quasimonotonic f" by (auto simp: monotonic_def quasimonotonic_def)

lemma proposition15:
  assumes "wbndlclens g"
  assumes "wbndlclens f"
  assumes "surj (get f)"
  assumes "quasimonotonic (get f)"
  shows "wbndlclens (g \<bullet> f)"
proof -
  have "wblens f" and "wblens g" using assms by (auto simp: wbndlclens_wblens)
  hence "wblens (g \<bullet> f)" using assms by (auto simp: compwblens)  
  hence "putget (g \<bullet> f)" by (auto simp: wblens_def)
  moreover
  from `wbndlclens g` have "leastgetput g" by (simp add: wbndlclens_def)
  from `wbndlclens f` have "leastgetput f" by (simp add: wbndlclens_def)
  have "leastgetput (g \<bullet> f)"
  proof (simp add: leastgetput_def comp_def, auto)
    fix s a
    assume H: "\<forall> b . get g (get f a) = get g (get f b) \<longrightarrow> a \<sqsubseteq>\<^sub>s b"
    have "\<forall> x . get g (get f a) = get g x \<longrightarrow> (get f a) \<sqsubseteq>\<^sub>(get f s) x"
    proof (auto)
      fix x
      assume "get g (get f a) = get g x"
      then obtain b where "x = get f b" and "get g (get f a) = get g (get f b)" using `surj (get f)` by auto
      hence "\<forall> c . get f b = get f c \<longrightarrow> a \<sqsubseteq>\<^sub>s c" using H by auto
      hence "(get f a) \<sqsubseteq>\<^sub>(get f s) (get f b)" using `quasimonotonic (get f)` by (simp add: quasimonotonic)
      thus "(get f a) \<sqsubseteq>\<^sub>(get f s) x" using `x = get f b` by simp
    qed
    hence A: "get f a \<in> put g (get f s) (get g (get f a))" using `leastgetput g` by (auto simp: leastgetput)
    have "\<forall> y . get f a = get f y \<longrightarrow> a \<sqsubseteq>\<^sub>s y" using H by auto
    hence "a \<in> put f s (get f a)" using `leastgetput f` by (auto simp: leastgetput)
    thus "\<exists> x \<in> put g (get f s) (get g (get f a)) . a \<in> put f s x" by (rule bexI [OF _ A])
  qed
  ultimately show ?thesis by (simp add: wbndlclens_def)
qed

lemma proposition16:
  assumes "quasimonotonic g"
  assumes "quasimonotonic f"
  assumes "surj f"
  shows "quasimonotonic (g \<circ> f)"
proof (auto simp: quasimonotonic_def)
  fix a b s
  assume H: "\<forall>c. g (f b) = g (f c) \<longrightarrow> a \<sqsubseteq>\<^sub>s c"
  have "\<forall>x. g (f b) = g x \<longrightarrow> (f a) \<sqsubseteq>\<^sub>(f s) x"
  proof (auto)
    fix x
    assume "g (f b) = g x"
    then obtain y where "x = f y" and "g (f b) = g (f y)" using `surj f` by auto
    hence "(f a) \<sqsubseteq>\<^sub>(f s) (f y)" using H by (auto simp: quasimonotonic [OF `quasimonotonic f`])
    thus "(f a) \<sqsubseteq>\<^sub>(f s) x" using `x = f y` by simp
  qed
  thus "(g (f a)) \<sqsubseteq>\<^sub>(g (f s)) (g (f b))" by (auto simp: quasimonotonic [OF `quasimonotonic g`])
qed

lemma proposition17:
  assumes A: "bij (fork f g)"
  assumes B: "\<forall> s a b . a \<sqsubseteq>\<^sub>s b \<and> g a = g b \<longrightarrow> (f a) \<sqsubseteq>\<^sub>(f s) (f b)"
  shows "quasimonotonic f"
proof (auto simp: quasimonotonic_def)
  fix a b s
  assume H: "\<forall> c . f b = f c \<longrightarrow> a \<sqsubseteq>\<^sub>s c"
  have C: "g (the_inv (fork f g) (f b, g a)) = g a" using A by (auto simp: sndinvfork)
  have D: "f (the_inv (fork f g) (f b, g a)) = f b" using A by (auto simp: fstinvfork)
  hence "a \<sqsubseteq>\<^sub>s (the_inv (fork f g)) (f b, g a)" using H by auto
  hence "(f a) \<sqsubseteq>\<^sub>(f s) (f (the_inv (fork f g) (f b, g a)))" using B C by simp
  thus "f a \<sqsubseteq>\<^sub>(f s) f b" using D by simp
qed

end

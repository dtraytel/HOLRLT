theory Group_Example
imports MainRLT
begin

(* The original constant and properties, as discussed in Section 3.1. 
The properties labeled (1), (2), (3) are here lemma1, lemma2 and lemma3. *)

thm eq_onp_def
thm perOfSet_def

definition group where
  "group tms e \<longleftrightarrow>
     (\<forall>x y z. tms (tms x y) z = tms x (tms y z)) \<and>
     (\<forall>x. tms x e = x \<and> tms e x = x) \<and>
     (\<forall>x. \<exists>y. tms x y = e \<and> tms y x = e)"

lemma lemma1: "group tms e \<longrightarrow> (\<forall>x y z. tms x y = tms x z \<longrightarrow> y = z)"
  unfolding group_def by metis

lemma lemma2: "group tms e \<longrightarrow> (\<forall>inv inv'. (\<forall>x. tms (inv x) x = e) \<and> (\<forall>x. tms (inv' x) x = e) \<longrightarrow> inv = inv')"
  unfolding group_def fun_eq_iff by metis

lemma lemma3_aux1:
  assumes "group tms e"
  shows "foldl tms x ys = tms x (foldl tms e ys)"
proof (induct ys arbitrary: x)
  case Nil
  with assms show ?case
    unfolding group_def by simp
next
  case (Cons y ys)
  from assms show ?case
    unfolding group_def foldl.simps o_def
    by (subst (1 2) Cons) auto
qed

lemma lemma3_aux2:
  assumes "group tms e"
  shows "foldl tms x (xs @ ys) = tms (foldl tms x xs) (foldl tms e ys)"
  by (induct xs) (auto intro: lemma3_aux1[OF assms])

lemma lemma3: "group tms e \<longrightarrow> (\<forall>xs ys. foldl tms e (xs @ ys) = tms (foldl tms e xs) (foldl tms e ys))"
  by (metis lemma3_aux2)

(* This command, RLTCST, read "relativize constant", 
relativizes a constant -- here, the constat "group", which yields 
the parametric constant "group_rlt":  *)
local_setup \<open>RLCST @{term group}\<close>

(* Here is the definition of group_rlt: *)
thm group_rlt_def

(* We obtain a more readable (and more usable) version of 
this definition after applying some default simplification rules 
for relativized connectives and quantifiers (referred to in the paper as 
Connective & Quantifier Suitability): 
*)

lemma group_rlt_alt:
  "neper R \<Longrightarrow> group_rlt R tms e \<longleftrightarrow>
    (\<forall>x y z. R x x \<and> R y y \<and> R z z \<longrightarrow> R (tms (tms x y) z) (tms x (tms y z))) \<and>
    (\<forall>x. R x x \<longrightarrow> R (tms x e) x \<and> R (tms e x) x) \<and>
    (\<forall>x. R x x \<longrightarrow> (\<exists>y. R y y \<and> R (tms x y) e \<and> R (tms y x) e))"
  unfolding group_rlt_def by auto


(* The notations from Section 3.1 (we use closed0 for constants 
and closed2 for binary operators, whereas the paper uses the same notation for both): *)

definition "closed0 A x = (x \<in> A)"
definition "closed2 A f = (\<forall>x \<in> A. \<forall>y \<in> A. f x y \<in> A)"

(* Each set A gives rise to a PER, the equality of A. 
In our formalization, we call it "perOfSet A", whereas in the paper 
this is denoted by "eqOf A". *)
abbreviation "eqOf A \<equiv> perOfSet A" 

lemma eqOf_alt: "eqOf A = eq_onp (\<lambda>x. x \<in> A)"
  unfolding perOfSet_def eq_onp_def by auto

lemma neper_eq_on: "closed0 A x \<Longrightarrow> neper (eqOf A)"
  by (meson closed0_def neper_def perOfSet_def per_perOfSet)

(* Set-based relativization is a particular case of PER relativization, via the 
"eqOf" view of sets as PERs. This is illustrated next for "group_rlt", as discussed 
in Section 4.3: *)
lemma group_rlt_set:
  assumes "closed0 A e" "closed2 A tms"
  shows "group_rlt (eqOf A) tms e \<longleftrightarrow>
    (\<forall>x \<in> A. \<forall>y \<in> A. \<forall>z \<in> A. tms (tms x y) z = tms x (tms y z)) \<and>
    (\<forall>x \<in> A. tms x e = x \<and> tms e x = x) \<and>
    (\<forall>x \<in> A. \<exists>y \<in> A. tms x y = e \<and> tms y x = e)"
  by (subst group_rlt_alt[OF neper_eq_on[OF assms(1)]])
    (insert assms, unfold closed0_def closed2_def perOfSet_def, meson)

(* This command, RLTTHM, read "relativize constant", 
relativizes a theorem -- here, the theorem is "lemma1", 
and relativization yields the theorem "lemma1_rlt":  *)
local_setup \<open>RLTHM @{binding lemma1_rlt} @{thm lemma1}\<close>

(* Again, the Connective & Quantifier Suitability simplification rules 
are applied for turning it into a readable/usable version:  *)

lemma lemma1_rlt_readable:
  assumes [simp]: "neper R" and "R e e" "rel_fun R (rel_fun R R) tms tms"
  shows "group_rlt R tms e \<longrightarrow>
  (\<forall>x y z. R x x \<and> R y y \<and> R z z \<longrightarrow> R (tms x y) (tms x z) \<longrightarrow> R y z)"
  using lemma1_rlt[OF assms, simplified]
  by blast

(* As noted in the Recoverability (Meta)Theorem, 
the relativized version recovers the original version of the theorem 
as a particular instance, as discussed in Section 4.3: *)
lemmas lemma1_recovered = lemma1_rlt_readable[of "(=)",
  simplified rlt_eq relator_eq neper simp_thms True_implies_equals]

(* ... and it also implies the set-based version, as discussed in Section 4.3: *)
lemma lemma1_rlt_set_readable:
  assumes "closed0 A e" "closed2 A tms"
  shows "group_rlt (eqOf A) tms e \<longrightarrow> (\<forall>x \<in> A. \<forall>y \<in> A. \<forall>z \<in> A. tms x y = tms x z \<longrightarrow> y = z)"
  using lemma1_rlt_readable[OF neper_eq_on[OF assms(1)], of e tms] assms
  by (unfold perOfSet_def rel_fun_def closed2_def closed0_def) blast

(* The relativizaton of lemma2, along the same lines as that for lemma1: *)

local_setup \<open>RLTHM @{binding lemma2_rlt} @{thm lemma2}\<close>

lemma lemma2_rlt_readable:
  assumes [simp]: "neper R" and "R e e" "rel_fun R (rel_fun R R) tms tms"
  shows "group_rlt R tms e \<longrightarrow>
  (\<forall>inv inv'. rel_fun R R inv inv \<longrightarrow> rel_fun R R inv' inv' \<longrightarrow>
     (\<forall>x. R x x \<longrightarrow> R (tms (inv x) x) e) \<and> (\<forall>x. R x x \<longrightarrow> R (tms (inv' x) x) e) \<longrightarrow>
     rel_fun R R inv inv')"
  using lemma2_rlt[OF assms, simplified]
  by blast

(* ... and again the original lemma "recovered": *)

lemmas lemma2_recovered = lemma2_rlt_readable[of "(=)",
  simplified rlt_eq relator_eq neper simp_thms True_implies_equals]

(* ... and (more-generally) the set-based version inferred: *)

abbreviation "fun_set A B \<equiv> {f. pred_fun (\<lambda>x. x \<in> A) (\<lambda>x. x \<in> B) f}"

lemma rel_fun_eq_onp_self: 
  "rel_fun (eq_onp A) (eq_onp B) f f = pred_fun A B f"
  by (auto simp: rel_fun_def eq_onp_def)

lemma lemma2_rlt_set_readable:
  assumes "closed0 A e" "closed2 A tms"
  shows "group_rlt (eqOf A) tms e \<longrightarrow>
    (\<forall>inv \<in> fun_set A A. \<forall>inv' \<in> fun_set A A. (\<forall>x \<in> A. tms (inv x) x = e) \<and> (\<forall>x \<in> A. tms (inv' x) x = e) \<longrightarrow> (\<forall>x \<in> A. inv x = inv' x))"
  using lemma2_rlt_readable[OF neper_eq_on[OF assms(1)], of e tms] assms
  unfolding rel_fun_eq_onp_self
  by (auto simp: rel_fun_def perOfSet_def closed0_def closed2_def)


(* Finally, the same happens for lemma3 where, as discussed in Section 6.1, 
Compatibility and PER-Parametricity ensure that the relativization of the 
already parametric constants such as @ (append) and foldl (fold left) is provably 
equal to th original constants. 
(list_all2 denotes the list relator, for which in the paper we simply write "list".) *)

local_setup \<open>RLTHM @{binding lemma3_rlt} @{thm lemma3}\<close>

lemma lemma3_rlt_readable:
  assumes [simp, THEN list.rrel_neper, simp]: "neper R" and "R e e" "rel_fun R (rel_fun R R) tms tms"
  shows "group_rlt R tms e \<longrightarrow>
  (\<forall>xs ys. list_all2 R xs xs \<longrightarrow> list_all2 R ys ys \<longrightarrow> R (foldl tms e (xs @ ys)) (tms (foldl tms e xs) (foldl tms e ys)))"
  using lemma3_rlt[OF assms, simplified] 
  by (auto simp only: rrel_alt rlt_param neper assms(1))

lemmas lemma3_recovered = lemma3_rlt_readable[of "(=)",
  simplified rlt_eq relator_eq neper simp_thms True_implies_equals]

lemma lists_alt: "lists A = {xs. list_all (\<lambda>x. x \<in> A) xs}"
  by (auto simp: list_all_iff)

lemma lemma3_rlt_set_readable:
  assumes "closed0 A e" "closed2 A tms"
  shows "group_rlt (eqOf A) tms e \<longrightarrow>
    (\<forall>xs \<in> lists A. \<forall>ys \<in> lists A. foldl tms e (xs @ ys) = tms (foldl tms e xs) (foldl tms e ys))"
  using lemma3_rlt_readable[OF neper_eq_on[OF assms(1)], of e tms] assms
  unfolding eqOf_alt list.rel_eq_onp lists_alt 
  by (auto simp: eq_onp_def  closed0_def closed2_def)  

end
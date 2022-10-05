(*  Title:      HOL/Library/Comparator.thy
    Author:     Florian Haftmann, TU Muenchen
*)

theory Comparator
  imports "MainRLT" 
begin

section \<open>Comparators on linear quasi-orders\<close>

subsection \<open>Basic properties\<close>

datatype comp = Less | Equiv | Greater

locale comparator =
  fixes cmp :: "'a \<Rightarrow> 'a \<Rightarrow> comp"
  assumes refl [simp]: "\<And>a. cmp a a = Equiv"
    and trans_equiv: "\<And>a b c. cmp a b = Equiv \<Longrightarrow> cmp b c = Equiv \<Longrightarrow> cmp a c = Equiv"
  assumes trans_less: "cmp a b = Less \<Longrightarrow> cmp b c = Less \<Longrightarrow> cmp a c = Less"
    and greater_iff_sym_less: "\<And>b a. cmp b a = Greater \<longleftrightarrow> cmp a b = Less"
begin

text \<open>Dual properties\<close>

lemma trans_greater:
  "cmp a c = Greater" if "cmp a b = Greater" "cmp b c = Greater"
  using that greater_iff_sym_less trans_less by blast

lemma less_iff_sym_greater:
  "cmp b a = Less \<longleftrightarrow> cmp a b = Greater"
  by (simp add: greater_iff_sym_less)

text \<open>The equivalence part\<close>

lemma sym:
  "cmp b a = Equiv \<longleftrightarrow> cmp a b = Equiv"
  by (metis (full_types) comp.exhaust greater_iff_sym_less)

lemma reflp:
  "reflp (\<lambda>a b. cmp a b = Equiv)"
  by (rule reflpI) simp

lemma symp:
  "symp (\<lambda>a b. cmp a b = Equiv)"
  by (rule sympI) (simp add: sym)

lemma transp:
  "transp (\<lambda>a b. cmp a b = Equiv)"
  by (rule transpI) (fact trans_equiv)

lemma equivp:
  "equivp (\<lambda>a b. cmp a b = Equiv)"
  using reflp symp transp by (rule equivpI)

text \<open>The strict part\<close>

lemma irreflp_less:
  "irreflp (\<lambda>a b. cmp a b = Less)"
  by (rule irreflpI) simp

lemma irreflp_greater:
  "irreflp (\<lambda>a b. cmp a b = Greater)"
  by (rule irreflpI) simp

lemma asym_less:
  "cmp b a \<noteq> Less" if "cmp a b = Less"
  using that greater_iff_sym_less by force

lemma asym_greater:
  "cmp b a \<noteq> Greater" if "cmp a b = Greater"
  using that greater_iff_sym_less by force

lemma asymp_less:
  "asymp (\<lambda>a b. cmp a b = Less)"
  using irreflp_less by (auto intro: asympI dest: asym_less)

lemma asymp_greater:
  "asymp (\<lambda>a b. cmp a b = Greater)"
  using irreflp_greater by (auto intro!: asympI dest: asym_greater)

lemma trans_equiv_less:
  "cmp a c = Less" if "cmp a b = Equiv" and "cmp b c = Less"
  using that
  by (metis (full_types) comp.exhaust greater_iff_sym_less trans_equiv trans_less)

lemma trans_less_equiv:
  "cmp a c = Less" if "cmp a b = Less" and "cmp b c = Equiv"
  using that
  by (metis (full_types) comp.exhaust greater_iff_sym_less trans_equiv trans_less)

lemma trans_equiv_greater:
  "cmp a c = Greater" if "cmp a b = Equiv" and "cmp b c = Greater"
  using that by (simp add: sym [of a b] greater_iff_sym_less trans_less_equiv)

lemma trans_greater_equiv:
  "cmp a c = Greater" if "cmp a b = Greater" and "cmp b c = Equiv"
  using that by (simp add: sym [of b c] greater_iff_sym_less trans_equiv_less)

lemma transp_less:
  "transp (\<lambda>a b. cmp a b = Less)"
  by (rule transpI) (fact trans_less)

lemma transp_greater:
  "transp (\<lambda>a b. cmp a b = Greater)"
  by (rule transpI) (fact trans_greater)

text \<open>The reflexive part\<close>

lemma reflp_not_less:
  "reflp (\<lambda>a b. cmp a b \<noteq> Less)"
  by (rule reflpI) simp

lemma reflp_not_greater:
  "reflp (\<lambda>a b. cmp a b \<noteq> Greater)"
  by (rule reflpI) simp

lemma quasisym_not_less:
  "cmp a b = Equiv" if "cmp a b \<noteq> Less" and "cmp b a \<noteq> Less"
  using that comp.exhaust greater_iff_sym_less by auto

lemma quasisym_not_greater:
  "cmp a b = Equiv" if "cmp a b \<noteq> Greater" and "cmp b a \<noteq> Greater"
  using that comp.exhaust greater_iff_sym_less by auto

lemma trans_not_less:
  "cmp a c \<noteq> Less" if "cmp a b \<noteq> Less" "cmp b c \<noteq> Less"
  using that by (metis comp.exhaust greater_iff_sym_less trans_equiv trans_less)

lemma trans_not_greater:
  "cmp a c \<noteq> Greater" if "cmp a b \<noteq> Greater" "cmp b c \<noteq> Greater"
  using that greater_iff_sym_less trans_not_less by blast

lemma transp_not_less:
  "transp (\<lambda>a b. cmp a b \<noteq> Less)"
  by (rule transpI) (fact trans_not_less)

lemma transp_not_greater:
  "transp (\<lambda>a b. cmp a b \<noteq> Greater)"
  by (rule transpI) (fact trans_not_greater)

text \<open>Substitution under equivalences\<close>

lemma equiv_subst_left:
  "cmp z y = comp \<longleftrightarrow> cmp x y = comp" if "cmp z x = Equiv" for comp
proof -
  from that have "cmp x z = Equiv"
    by (simp add: sym)
  with that show ?thesis
    by (cases comp) (auto intro: trans_equiv trans_equiv_less trans_equiv_greater)
qed

lemma equiv_subst_right:
  "cmp x z = comp \<longleftrightarrow> cmp x y = comp" if "cmp z y = Equiv" for comp
proof -
  from that have "cmp y z = Equiv"
    by (simp add: sym)
  with that show ?thesis
    by (cases comp) (auto intro: trans_equiv trans_less_equiv trans_greater_equiv)
qed

end

typedef 'a comparator = "{cmp :: 'a \<Rightarrow> 'a \<Rightarrow> comp. comparator cmp}"
  morphisms compare Abs_comparator
proof -
  have "comparator (\<lambda>_ _. Equiv)"
    by standard simp_all
  then show ?thesis
    by auto
qed

setup_lifting type_definition_comparator

global_interpretation compare: comparator "compare cmp"
  using compare [of cmp] by simp

lift_definition flat :: "'a comparator"
  is "\<lambda>_ _. Equiv" by standard simp_all

instantiation comparator :: (linorder) default
begin

lift_definition default_comparator :: "'a comparator"
  is "\<lambda>x y. if x < y then Less else if x > y then Greater else Equiv"
  by standard (auto split: if_splits)

instance ..

end

text \<open>A rudimentary quickcheck setup\<close>

instantiation comparator :: (enum) equal
begin

lift_definition equal_comparator :: "'a comparator \<Rightarrow> 'a comparator \<Rightarrow> bool"
  is "\<lambda>f g. \<forall>x \<in> set Enum.enum. f x = g x" .

instance
  by (standard; transfer) (auto simp add: enum_UNIV)

end

lemma [code]:
  "HOL.equal cmp1 cmp2 \<longleftrightarrow> Enum.enum_all (\<lambda>x. compare cmp1 x = compare cmp2 x)"
  by transfer (simp add: enum_UNIV)

lemma [code nbe]:
  "HOL.equal (cmp :: 'a::enum comparator) cmp \<longleftrightarrow> True"
  by (fact equal_refl)

instantiation comparator :: ("{linorder, typerep}") full_exhaustive
begin

definition full_exhaustive_comparator ::
  "('a comparator \<times> (unit \<Rightarrow> term) \<Rightarrow> (bool \<times> term list) option)
    \<Rightarrow> natural \<Rightarrow> (bool \<times> term list) option"
  where "full_exhaustive_comparator f s =
    Quickcheck_Exhaustive.orelse
      (f (flat, (\<lambda>u. Code_Evaluation.Const (STR ''Comparator.flat'') TYPEREP('a comparator))))
      (f (default, (\<lambda>u. Code_Evaluation.Const (STR ''HOL.default_class.default'') TYPEREP('a comparator))))"

instance ..

end


subsection \<open>Fundamental comparator combinators\<close>

lift_definition reversed :: "'a comparator \<Rightarrow> 'a comparator"
  is "\<lambda>cmp a b. cmp b a"
proof -
  fix cmp :: "'a \<Rightarrow> 'a \<Rightarrow> comp"
  assume "comparator cmp"
  then interpret comparator cmp .
  show "comparator (\<lambda>a b. cmp b a)"
    by standard (auto intro: trans_equiv trans_less simp: greater_iff_sym_less)
qed

lift_definition key :: "('b \<Rightarrow> 'a) \<Rightarrow> 'a comparator \<Rightarrow> 'b comparator"
  is "\<lambda>f cmp a b. cmp (f a) (f b)"
proof -
  fix cmp :: "'a \<Rightarrow> 'a \<Rightarrow> comp" and f :: "'b \<Rightarrow> 'a"
  assume "comparator cmp"
  then interpret comparator cmp .
  show "comparator (\<lambda>a b. cmp (f a) (f b))"
    by standard (auto intro: trans_equiv trans_less simp: greater_iff_sym_less)
qed


subsection \<open>Direct implementations for linear orders on selected types\<close>

definition comparator_bool :: "bool comparator"
  where [simp, code_abbrev]: "comparator_bool = default"

lemma compare_comparator_bool [code abstract]:
  "compare comparator_bool = (\<lambda>p q.
    if p then if q then Equiv else Greater
    else if q then Less else Equiv)"
  by (auto simp add: fun_eq_iff) (transfer; simp)+

definition raw_comparator_nat :: "nat \<Rightarrow> nat \<Rightarrow> comp"
  where [simp]: "raw_comparator_nat = compare default"

lemma default_comparator_nat [simp, code]:
  "raw_comparator_nat (0::nat) 0 = Equiv"
  "raw_comparator_nat (Suc m) 0 = Greater"
  "raw_comparator_nat 0 (Suc n) = Less"
  "raw_comparator_nat (Suc m) (Suc n) = raw_comparator_nat m n"
  by (transfer; simp)+

definition comparator_nat :: "nat comparator"
  where [simp, code_abbrev]: "comparator_nat = default"

lemma compare_comparator_nat [code abstract]:
  "compare comparator_nat = raw_comparator_nat"
  by simp

definition comparator_linordered_group :: "'a::linordered_ab_group_add comparator"
  where [simp, code_abbrev]: "comparator_linordered_group = default"

lemma comparator_linordered_group [code abstract]:
  "compare comparator_linordered_group = (\<lambda>a b.
    let c = a - b in if c < 0 then Less
    else if c = 0 then Equiv else Greater)"
proof (rule ext)+
  fix a b :: 'a
  show "compare comparator_linordered_group a b =
    (let c = a - b in if c < 0 then Less
       else if c = 0 then Equiv else Greater)"
    by (simp add: Let_def not_less) (transfer; auto)
qed


(**********************)
(* The comparator type has a wide definition *)

(* *)
lemma comparator_aux: "comparator = comparator" ..
local_setup \<open>RLTHM @{binding comparator_rlt_neper_param} @{thm comparator_aux}\<close>
thm comparator_rlt_neper_param

thm comparator_def[no_vars]


lemma comparator_rlt_simp[simp]: 
"neper R \<Longrightarrow> 
 comparator_rlt R cmp \<longleftrightarrow> 
  (\<forall>a. R a a \<longrightarrow> cmp a a = Equiv) \<and> 
  (\<forall>a b c. R a a \<and> R b b \<and> R c c \<and> cmp a b = Equiv \<and> cmp b c = Equiv \<longrightarrow> cmp a c = Equiv) \<and>
  (\<forall>a b c. R a a \<and> R b b \<and> R c c \<and> cmp a b = Less \<and> cmp b c = Less \<longrightarrow> cmp a c = Less) \<and>
  (\<forall>b a. R b b \<and> R a a \<longrightarrow> (cmp b a = Greater) = (cmp a b = Less))"
unfolding comparator_rlt_def apply simp unfolding rrel_eq unfolding fun_eq_iff 
by (smt (verit, best) Equiv_rlt_eq Greater_rlt_eq Less_rlt_eq)

(* *)

definition gg :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> comp) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> comp" 
where "gg R \<equiv> \<lambda>cmp a b. cmp (getRepr' R a) (getRepr' R b)"

lemma getRepr'_refl: "neper R \<Longrightarrow> R (getRepr' R a) (getRepr' R a)"
unfolding getRepr'_def 
using getRepr_neper neper_Some neper_classes_eq by fastforce

lemma getRepr': "neper R \<Longrightarrow> R a b \<Longrightarrow> R (getRepr' R a) (getRepr' R b)"
unfolding getRepr'_def by (smt (verit, best) geterRepr_related neper_per per_def)

lemma bij_upto_gg: 
assumes R: "neper R" 
shows 
"bij_upto
 (restr (rel_fun R (rel_fun R (=))) comparator)
 (restr (rel_fun R (rel_fun R (=))) (comparator_rlt R)) (gg R)"
apply(rule bij_uptoI)
  subgoal apply(rule neper_restr)
    subgoal using R by simp
    subgoal apply(rule exI[of _ "\<lambda>a b. Equiv"], safe)
      subgoal using R by simp
      subgoal using R unfolding rel_fun_def by (simp add: neper_Some) . .
  subgoal for f f' unfolding restr_def apply safe
    subgoal using R unfolding rel_fun_def gg_def 
    	by (smt (verit, best) getRepr'_def geterRepr_related neper_per per_def)
    subgoal using R unfolding comparator_def[of f]  
    unfolding gg_def rel_fun_def 
    by (smt (verit, best) comparator_rlt_simp) 
    subgoal using R unfolding comparator_def[of f']  
    unfolding gg_def rel_fun_def 
    by (smt (verit, best) comparator_rlt_simp) .
  subgoal for f f' unfolding restr_def apply safe
    unfolding rel_fun_def gg_def 
    by (smt (z3) R getRepr'_def getRepr_neper mem_Collect_eq neper_classes_eq neper_getRepr_eq)
  subgoal for g apply(rule exI[of _ "gg R g"], unfold restr_def, safe)
     subgoal using R unfolding comparator_def gg_def restr_def rel_fun_def 
     by (smt (verit, best) getRepr'_def getRepr_neper neper_getRepr_eq neper_per per_def) 
     subgoal using R unfolding comparator_def gg_def comparator_rlt_simp[OF R] rel_fun_def 
     by (meson getRepr'_refl)+
     subgoal using R unfolding comparator_def gg_def comparator_rlt_simp[OF R] rel_fun_def 
     by (meson getRepr'_refl)+
     subgoal using R unfolding rel_fun_def gg_def  
     	 by (smt (verit, del_insts) getRepr'_def getReprOn getReprOn_UNIV neper_getRepr_eq 
        neper_per per_def)
     subgoal using R unfolding gg_def comparator_rlt_simp[OF R]  
     	 by (smt (z3) getRepr'_def getReprOn getReprOn_UNIV geterRepr_related neper_getRepr_eq) . .

definition rel_comparator where 
"rel_comparator R = inv_imagep (rel_fun R (rel_fun R (=))) compare" 

thm bij_upto_transportFromRaw[OF type_definition_comparator rel_comparator_def bij_upto_gg]

wide_typedef comparator rel: rel_comparator rep: "\<lambda>R. gg R \<circ> compare"
  subgoal for R unfolding rel_comparator_def
  apply(rule neper_inv_imagep[of _ _ "Abs_comparator (\<lambda>a b. Equiv)"])
     subgoal by simp
     subgoal unfolding rel_fun_def  by (metis flat.abs_eq flat.rep_eq) .
  subgoal unfolding rel_comparator_def unfolding inv_imagep_def fun_eq_iff  
    by (simp add: compare_inject)
  subgoal using bij_upto_transportFromRaw[OF type_definition_comparator rel_comparator_def bij_upto_gg]
    unfolding comparator_rlt_def rrel_eq .
  subgoal unfolding gg_def fun_eq_iff getRepr'_def by auto .

end

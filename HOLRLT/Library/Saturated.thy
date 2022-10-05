(*  Title:      HOL/Library/Saturated.thy
    Author:     Brian Huffman
    Author:     Peter Gammie
    Author:     Florian Haftmann
*)

section \<open>Saturated arithmetic\<close>

theory Saturated
imports Numeral_Type Type_Length
begin

subsection \<open>The type of saturated naturals\<close>

typedef (overloaded) ('a::len) sat = "{.. LENGTH('a)}"
  morphisms nat_of Abs_sat
  by auto

lemma sat_eqI:
  "nat_of m = nat_of n \<Longrightarrow> m = n"
  by (simp add: nat_of_inject)

lemma sat_eq_iff:
  "m = n \<longleftrightarrow> nat_of m = nat_of n"
  by (simp add: nat_of_inject)

lemma Abs_sat_nat_of [code abstype]:
  "Abs_sat (nat_of n) = n"
  by (fact nat_of_inverse)

definition Abs_sat' :: "nat \<Rightarrow> 'a::len sat" where
  "Abs_sat' n = Abs_sat (min (LENGTH('a)) n)"

lemma nat_of_Abs_sat' [simp]:
  "nat_of (Abs_sat' n :: ('a::len) sat) = min (LENGTH('a)) n"
  unfolding Abs_sat'_def by (rule Abs_sat_inverse) simp

lemma nat_of_le_len_of [simp]:
  "nat_of (n :: ('a::len) sat) \<le> LENGTH('a)"
  using nat_of [where x = n] by simp

lemma min_len_of_nat_of [simp]:
  "min (LENGTH('a)) (nat_of (n::('a::len) sat)) = nat_of n"
  by (rule min.absorb2 [OF nat_of_le_len_of])

lemma min_nat_of_len_of [simp]:
  "min (nat_of (n::('a::len) sat)) (LENGTH('a)) = nat_of n"
  by (subst min.commute) simp

lemma Abs_sat'_nat_of [simp]:
  "Abs_sat' (nat_of n) = n"
  by (simp add: Abs_sat'_def nat_of_inverse)

instantiation sat :: (len) linorder
begin

definition
  less_eq_sat_def: "x \<le> y \<longleftrightarrow> nat_of x \<le> nat_of y"

definition
  less_sat_def: "x < y \<longleftrightarrow> nat_of x < nat_of y"

instance
  by standard
    (auto simp add: less_eq_sat_def less_sat_def not_le sat_eq_iff min.coboundedI1 mult.commute)

end

instantiation sat :: (len) "{minus, comm_semiring_1}"
begin

definition
  "0 = Abs_sat' 0"

definition
  "1 = Abs_sat' 1"

lemma nat_of_zero_sat [simp, code abstract]:
  "nat_of 0 = 0"
  by (simp add: zero_sat_def)

lemma nat_of_one_sat [simp, code abstract]:
  "nat_of 1 = min 1 (LENGTH('a))"
  by (simp add: one_sat_def)

definition
  "x + y = Abs_sat' (nat_of x + nat_of y)"

lemma nat_of_plus_sat [simp, code abstract]:
  "nat_of (x + y) = min (nat_of x + nat_of y) (LENGTH('a))"
  by (simp add: plus_sat_def)

definition
  "x - y = Abs_sat' (nat_of x - nat_of y)"

lemma nat_of_minus_sat [simp, code abstract]:
  "nat_of (x - y) = nat_of x - nat_of y"
proof -
  from nat_of_le_len_of [of x] have "nat_of x - nat_of y \<le> LENGTH('a)" by arith
  then show ?thesis by (simp add: minus_sat_def)
qed

definition
  "x * y = Abs_sat' (nat_of x * nat_of y)"

lemma nat_of_times_sat [simp, code abstract]:
  "nat_of (x * y) = min (nat_of x * nat_of y) (LENGTH('a))"
  by (simp add: times_sat_def)

instance
proof
  fix a b c :: "'a::len sat"
  show "a * b * c = a * (b * c)"
  proof(cases "a = 0")
    case True thus ?thesis by (simp add: sat_eq_iff)
  next
    case False show ?thesis
    proof(cases "c = 0")
      case True thus ?thesis by (simp add: sat_eq_iff)
    next
      case False with \<open>a \<noteq> 0\<close> show ?thesis
        by (simp add: sat_eq_iff nat_mult_min_left nat_mult_min_right mult.assoc min.assoc min.absorb2)
    qed
  qed
  show "1 * a = a"
    by (simp add: sat_eq_iff min_def not_le not_less)
  show "(a + b) * c = a * c + b * c"
  proof(cases "c = 0")
    case True thus ?thesis by (simp add: sat_eq_iff)
  next
    case False thus ?thesis
      by (simp add: sat_eq_iff nat_mult_min_left add_mult_distrib min_add_distrib_left min_add_distrib_right min.assoc min.absorb2)
  qed
qed (simp_all add: sat_eq_iff mult.commute)

end

instantiation sat :: (len) ordered_comm_semiring
begin

instance
  by standard
    (auto simp add: less_eq_sat_def less_sat_def not_le sat_eq_iff min.coboundedI1 mult.commute)

end

lemma Abs_sat'_eq_of_nat: "Abs_sat' n = of_nat n"
  by (rule sat_eqI, induct n, simp_all)

abbreviation Sat :: "nat \<Rightarrow> 'a::len sat" where
  "Sat \<equiv> of_nat"

lemma nat_of_Sat [simp]:
  "nat_of (Sat n :: ('a::len) sat) = min (LENGTH('a)) n"
  by (rule nat_of_Abs_sat' [unfolded Abs_sat'_eq_of_nat])

lemma [code_abbrev]:
  "of_nat (numeral k) = (numeral k :: 'a::len sat)"
  by simp

context
begin

qualified definition sat_of_nat :: "nat \<Rightarrow> ('a::len) sat"
  where [code_abbrev]: "sat_of_nat = of_nat"

lemma [code abstract]:
  "nat_of (sat_of_nat n :: ('a::len) sat) = min (LENGTH('a)) n"
  by (simp add: sat_of_nat_def)

end

instance sat :: (len) finite
proof
  show "finite (UNIV::'a sat set)"
    unfolding type_definition.univ [OF type_definition_sat]
    using finite by simp
qed

instantiation sat :: (len) equal
begin

definition "HOL.equal A B \<longleftrightarrow> nat_of A = nat_of B"

instance
  by standard (simp add: equal_sat_def nat_of_inject)

end

instantiation sat :: (len) "{bounded_lattice, distrib_lattice}"
begin

definition "(inf :: 'a sat \<Rightarrow> 'a sat \<Rightarrow> 'a sat) = min"
definition "(sup :: 'a sat \<Rightarrow> 'a sat \<Rightarrow> 'a sat) = max"
definition "bot = (0 :: 'a sat)"
definition "top = Sat (LENGTH('a))"

instance
  by standard
    (simp_all add: inf_sat_def sup_sat_def bot_sat_def top_sat_def max_min_distrib2,
      simp_all add: less_eq_sat_def)

end

instantiation sat :: (len) "{Inf, Sup}"
begin

global_interpretation Inf_sat: semilattice_neutr_set min \<open>top :: 'a sat\<close>
  defines Inf_sat = Inf_sat.F
  by standard (simp add: min_def)

global_interpretation Sup_sat: semilattice_neutr_set max \<open>bot :: 'a sat\<close>
  defines Sup_sat = Sup_sat.F
  by standard (simp add: max_def bot.extremum_unique)

instance ..

end

instance sat :: (len) complete_lattice
proof 
  fix x :: "'a sat"
  fix A :: "'a sat set"
  note finite
  moreover assume "x \<in> A"
  ultimately show "Inf A \<le> x"
    by (induct A) (auto intro: min.coboundedI2)
next
  fix z :: "'a sat"
  fix A :: "'a sat set"
  note finite
  moreover assume z: "\<And>x. x \<in> A \<Longrightarrow> z \<le> x"
  ultimately show "z \<le> Inf A" by (induct A) simp_all
next
  fix x :: "'a sat"
  fix A :: "'a sat set"
  note finite
  moreover assume "x \<in> A"
  ultimately show "x \<le> Sup A"
    by (induct A) (auto intro: max.coboundedI2)
next
  fix z :: "'a sat"
  fix A :: "'a sat set"
  note finite
  moreover assume z: "\<And>x. x \<in> A \<Longrightarrow> x \<le> z"
  ultimately show "Sup A \<le> z" by (induct A) auto
next
  show "Inf {} = (top::'a sat)"
    by (auto simp: top_sat_def)
  show "Sup {} = (bot::'a sat)"
    by (auto simp: bot_sat_def)
qed


(********************************************************)
(* sat has a conditionally wide type definition *)
(* There's also an explanation why sat does not have a wide type definition, 
by going for the "copy" route that essentially takes advantage of the 
cardinality and showing why that fails. And if that fails, that type 
cannot be wide.  
*)

definition isSat where 
"isSat (a::'a::len) i \<equiv> i \<le> LENGTH('a)"

lemma atLeastLessThan_Collect_sat: 
"{..LENGTH('a::len)} = Collect (isSat (a::'a))"
unfolding isSat_def by auto

lemma sat_type_definition: 
"type_definition 
   (nat_of::('a::len) sat \<Rightarrow> nat) Abs_sat 
   (Collect (isSat (a::'a)))"
unfolding atLeastLessThan_Collect_sat[symmetric]  
using type_definition_sat by blast

(* *)

lemma len_of_aux: "len_of = len_of" ..
local_setup \<open>RLTHM @{binding len_rlt_neper_param} @{thm len_of_aux}\<close>
thm len_rlt_neper_param

lemma type_aux: "Pure.type = Pure.type " ..
local_setup \<open>RLTHM @{binding type_rlt_neper_param} @{thm type_aux}\<close>
thm type_rlt_neper_param

lemma isSat_aux: "isSat = isSat" ..
local_setup \<open>RLTHM @{binding isSat_rlt_neper_param} @{thm isSat_aux}\<close>
thm isSat_rlt_neper_param


lemma type_rlt_simp[simp]: 
"neper (R::'a::len\<Rightarrow>'a\<Rightarrow>bool) \<Longrightarrow> type_rlt R = Pure.type"
unfolding type_rlt_def fun_eq_iff Unity_rlt_def  apply simp
unfolding Abs_itself_rlt_def Rep_itself_rlt_def
unfolding rlt_eq by (simp add: Abs_itself_qdef type_qdef)

lemma isSat_rlt_simp[simp]: "neper (R::'a::len\<Rightarrow>'a\<Rightarrow>bool) \<Longrightarrow> 
 isSat_rlt R zlen a = (\<lambda>i. i \<le> zlen Pure.type)"
unfolding isSat_rlt_def rlt_eq by simp


thm len_rlt_def

lemma aux1: "Rep_Nat (SOME a. Rep_Nat a = Zero_Rep) = Zero_Rep"
	by (meson Nat_Abs_Nat_inverse Zero_RepI someI_ex) 

lemma aux2: "(SOME a. Rep_Nat a = Suc_Rep Zero_Rep) = 1" 
	by (simp add: Abs_Nat_qdef INV_def Nat.Suc_def Zero_nat_def aux1)
	

lemma len_rlt_simp: "neper (R::'a::len\<Rightarrow>'a\<Rightarrow>bool) \<Longrightarrow> 
  len_rlt R zlen \<longleftrightarrow> 0 < zlen TYPE('a)"
unfolding len_rlt_def apply simp unfolding less_nat_rlt_def 
less_eq_Suc_le_raw_rlt_def zero_nat_rlt_def
ord_nat_inst.less_eq_nat_rlt_def Suc_rlt_def Zero_nat_rlt_def 
Abs_Nat_rlt_def rlt_eq fun_eq_iff INV_def aux1 aux2 apply simp 
	using Nat.less_eq_nat_rlt_eq ord_nat_inst.less_eq_nat_rlt_def ord_nat_inst.less_eq_nat_rlt_eq 
by presburger

(* *)
hide_const surj
(* *)
definition surjf :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"surjf i j \<equiv> \<lambda>u. if u \<le> j then u else j"

lemma surjf_le: "0 < j \<Longrightarrow> j \<le> i \<Longrightarrow> u \<le> i \<Longrightarrow> 
  surjf i j u \<le> j"
unfolding surjf_def by fastforce

lemma surjf_surj: "0 < j \<Longrightarrow> j \<le> i \<Longrightarrow> 
  u \<le> j \<Longrightarrow> 
  \<exists>v. v \<le> i \<and> u = surjf i j v"
unfolding surjf_def by fastforce

lemma surj_surjf: "0 < j \<Longrightarrow> j \<le> i \<Longrightarrow> surjf i j ` {..i} = {..j}"
unfolding surjf_def by fastforce

definition hh :: "('a::len \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a itself \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where 
"hh \<equiv> \<lambda>R::'a::len\<Rightarrow>'a\<Rightarrow>bool. \<lambda>zlen::'a itself \<Rightarrow> nat. 
    surjf (LENGTH('a)) 
          (zlen (TYPE('a)))"

definition sat_rel :: "('a::len \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a itself \<Rightarrow> nat) \<Rightarrow> 'a sat \<Rightarrow> 'a sat \<Rightarrow> bool" 
where "sat_rel R zlen \<equiv> 
inv_imagep 
  (restr (inv_imagep (restr (=) (isSat_rlt R zlen (undefined::'a))) (hh R zlen)) 
         (isSat (undefined::'a))) 
  nat_of"

thm bij_upto_criterion
(* If this "copy" route fails, than the type is not wide: *)
thm bij_upto_criterion[OF sat_type_definition, of "(=)" "undefined::'a::len" 
"isSat_rlt R zlen (undefined::'a)" 
"hh R zlen",simped, unfolded sat_rel_def[symmetric]]

thm sat_rel_def[symmetric]

lemma bij_upto_hh: 
assumes R: "neper (R::'a::len\<Rightarrow>'a\<Rightarrow>bool)"  and l: "len_rlt R zlen" 
(* and zlen: "rel_fun (=) (=) zlen zlen" (* this is trivially true *) *)
and (* condition: *) c: "zlen TYPE('a) \<le> LENGTH('a)"
shows "bij_upto (sat_rel R zlen) (restr (=) (isSat_rlt R zlen undefined)) (hh R zlen \<circ> nat_of)"
apply(rule bij_upto_criterion[OF sat_type_definition, of "(=)" "undefined::'a::len" 
"isSat_rlt R zlen (undefined::'a)" 
"hh R zlen",simped, unfolded sat_rel_def[symmetric]])
(* Cannot be proved wide without the condition c...
since we cannot prove that there exists a surjection 
between {0,...,len_of TYPE('a)} and {0,...,zlen Type} for some variable zlen. 
Indeed, we cannot guarantee that zlen TYPE('a) \<le> len_of Type . 
Incidentally, we can guarantee that any instance 
of this type obtained by specifying len_of, via an instance definition L,  
is wide: this is because then zlen will be instantiated to the relativization of 
L, which can only be equal to L since L must be parametric parametric (as any function 
from a singleton type to nat is).
NB: "len_of TYPE('a)" is denoted by LENGTH('a) 
*)
  subgoal for i using l unfolding len_rlt_simp[OF R] isSat_def isSat_rlt_simp[OF R]
    unfolding hh_def apply - apply(rule surjf_le) using l c unfolding len_rlt_simp[OF R] by auto
  subgoal for j using l unfolding len_rlt_simp[OF R] isSat_def isSat_rlt_simp[OF R] 
    unfolding hh_def apply - apply(rule surjf_surj) using l c unfolding len_rlt_simp[OF R] by auto . 


(* *)
term "\<lambda>(R::'a \<Rightarrow> 'a \<Rightarrow> bool) z. z (TYPE('a::len)) \<le> LENGTH('a)"

wide_typedef sat rel: sat_rel rep: "\<lambda>R z. hh R z \<circ> nat_of" 
cond: "\<lambda>(R::'a \<Rightarrow> 'a \<Rightarrow> bool) z. z (TYPE('a::len)) \<le> LENGTH('a)"
  subgoal unfolding sat_rel_def apply(rule neper_inv_imagep[of _ _ "Abs_sat 0"])
    subgoal apply(rule neper_restr)
      subgoal apply(rule neper_inv_imagep[of _ _ "0"])
        subgoal apply(rule neper_restr)
          subgoal by auto
            subgoal apply(rule exI[of _ 0]) by auto .
          subgoal unfolding restr_def hh_def surjf_def by auto .
        subgoal apply(rule exI[of _ 0]) unfolding restr_def hh_def surjf_def isSat_def by auto .
      subgoal unfolding restr_def inv_imagep_def restr_def hh_def surjf_def isSat_def by auto .      
  subgoal unfolding sat_rel_def inv_imagep_def restr_def fun_eq_iff hh_def surjf_def isSat_def 
  by (simp add: sat_eq_iff)
  subgoal for R zlen
  unfolding rlt_eq apply simp 
  unfolding isSat_rlt_simp[of R zlen undefined, symmetric]
  using bij_upto_hh by metis
  subgoal unfolding hh_def surjf_def by auto
  subgoal by auto .

local_setup \<open>RLTHM @{binding sat_eq_iff_rlt} @{thm sat_eq_iff}\<close>
local_setup \<open>RLTHM @{binding sat_eqI_rlt} @{thm sat_eqI}\<close>
local_setup \<open>RLTHM @{binding nat_of_sat_rlt} @{thm nat_of_Sat}\<close>

end

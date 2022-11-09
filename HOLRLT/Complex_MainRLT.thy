section \<open>Comprehensive Complex Theory\<close>

theory Complex_MainRLT
imports
  Complex
  MacLaurin
begin

local_setup \<open>RLTHM @{binding Cantors_paradox_rlt} @{thm Cantors_paradox}\<close>
thm Cantors_paradox
thm Cantors_paradox_rlt

local_setup \<open>RLTHM @{binding binomial_ring_rlt} @{thm binomial_ring}\<close>
thm binomial_ring
thm binomial_ring_rlt

local_setup \<open>RLTHM @{binding hull_redundant_rlt} @{thm hull_redundant}\<close>
thm hull_redundant
thm hull_redundant_rlt

local_setup \<open>RLTHM @{binding Complex_in_Reals_rlt} @{thm Complex_in_Reals}\<close>
thm Complex_in_Reals
thm Complex_in_Reals_rlt

local_setup \<open>RLTHM @{binding Maclaurin_lemma_rlt} @{thm Maclaurin_lemma}\<close>
thm Maclaurin_lemma
thm Maclaurin_lemma_rlt

(* Relativization of the is_filter predicate *)
lemma aux_is_filter: "is_filter = is_filter" ..

local_setup \<open>RLTHM @{binding aux_is_filter_rlt} @{thm aux_is_filter}\<close>
find_theorems is_filter_def_rlt

lemma is_filter_rlt_simp[simp]: 
"neper R \<Longrightarrow> 
 is_filter_rlt R F \<longleftrightarrow> 
 (F (\<lambda>x. True) 
 \<and>
 (\<forall>p pa. rel_fun R (=) p p \<and> rel_fun R (=) pa pa  \<and> F p \<and> F pa \<longrightarrow> F (\<lambda>x. p x \<and> pa x)) 
 \<and>
 (\<forall>p pa. rel_fun R (=) p p \<and> rel_fun R (=) pa pa \<and> (\<forall>xb. R xb xb \<and> p xb \<longrightarrow> pa xb) \<and> F p \<longrightarrow> F pa))"
unfolding is_filter_rlt_def rlt_eq by simp meson

(*********************)

lemma neper_rel_filter:
"neper R \<Longrightarrow> neper (rel_filter R)"
apply (simp add: neper_def per_def)
apply safe
apply (metis rel_filter_conversep symp_conv_conversep_eq symp_def)
   apply (rule rel_filter_mono[THEN predicate2D])
    apply (rule transp_relcompp_less_eq)
    apply (metis transpI)
   apply (rule rel_filter_distr[of R R, THEN predicate2_eqD, THEN iffD1])
  apply (erule (1) relcomppI)
using bot_filter_parametric by blast

(* More palatable definition of rel_filter: *)

lemma rel_filter_iff:  "rel_filter R F G \<longleftrightarrow>
(\<exists>H. Rep_filter H (\<lambda>(x, y). R x y) \<and>
   (F = Abs_filter (\<lambda>p. Rep_filter H (\<lambda>(x,y). p x \<and> R x y)))
   \<and>
   (G = Abs_filter (\<lambda>q. Rep_filter H (\<lambda>(x,y). q y \<and> R x y))))"
proof-
  have aux: "\<And>P. ((\<lambda>x. P (fst x) \<and> x \<in> {(x, y). R x y})) = (\<lambda>(x,y). P x \<and> R x y)"
    "\<And>P. ((\<lambda>x. P (snd x) \<and> x \<in> {(x, y). R x y})) = (\<lambda>(x,y). P y \<and> R x y)"
  by auto
  show ?thesis unfolding rel_filter.simps map_filter_on_def eventually_def
  unfolding aux by blast
qed

lemma is_filter_conjL:
assumes H: "is_filter H" and HR: "H (\<lambda>(x, y). R x y)"
shows "is_filter (\<lambda>p. H (\<lambda>(x,y). p x \<and> R x y))"
unfolding is_filter_def apply safe
  subgoal using assms unfolding is_filter_def by auto
  subgoal premises prems for P Q using
    H[unfolded is_filter_def, THEN conjunct2, THEN conjunct1, rule_format,
        of "\<lambda>(x, y). P x \<and> R x y" "\<lambda>(x, y). Q x \<and> R x y"]
    apply (rule is_filter.mono[OF H, rotated])
    apply (rule prems)
    apply (rule prems)
    apply auto
    done
  subgoal for P Q
    apply (rule is_filter.mono[OF H, rotated])
    apply auto
    done
  .

lemma is_filter_conjR:
assumes H: "is_filter H" and HR: "H (\<lambda>(x, y). R x y)"
shows "is_filter (\<lambda>q. H (\<lambda>(x,y). q y \<and> R x y))"
unfolding is_filter_def apply safe
  subgoal using assms unfolding is_filter_def by auto
  subgoal premises prems for P Q using
    H[unfolded is_filter_def, THEN conjunct2, THEN conjunct1, rule_format,
        of "\<lambda>(x, y). P y \<and> R x y" "\<lambda>(x, y). Q y \<and> R x y"]

    apply (rule is_filter.mono[OF H, rotated])
    apply (rule prems)
    apply (rule prems)
    apply auto
    done
  subgoal for P Q
    apply (rule is_filter.mono[OF H, rotated])
    apply auto
    done
  .

lemma Rep_filter_Abs_filter_conjL:
assumes HR: "Rep_filter Z (\<lambda>(x, y). R x y)"
shows "Rep_filter (Abs_filter (\<lambda>p. Rep_filter Z (\<lambda>(x,y). p x \<and> R x y))) =
       (\<lambda>p. Rep_filter Z (\<lambda>(x,y). p x \<and> R x y))"
using Abs_filter_inverse' assms is_filter_Rep_filter is_filter_conjL by blast

lemma Rep_filter_Abs_filter_conjR:
assumes HR: "Rep_filter Z (\<lambda>(x, y). R x y)"
shows "Rep_filter (Abs_filter (\<lambda>q. Rep_filter Z (\<lambda>(x,y). q y \<and> R x y))) =
       (\<lambda>q. Rep_filter Z (\<lambda>(x,y). q y \<and> R x y))"
using Abs_filter_inverse' assms is_filter_Rep_filter is_filter_conjR by blast

lemma rel_filter_def2: "rel_filter R F G \<longleftrightarrow>
(\<exists>H. Rep_filter H (\<lambda>(x, y). R x y) \<and>
     Rep_filter F = (\<lambda>p. Rep_filter H (\<lambda>(x, y). p x \<and> R x y)) \<and>
     Rep_filter G = (\<lambda>q. Rep_filter H (\<lambda>(x, y). q y \<and> R x y)))"
unfolding rel_filter_iff
apply safe 
  subgoal for H apply(rule exI[of _ H]) apply safe  
using Rep_filter_Abs_filter_conjL Rep_filter_Abs_filter_conjR by blast+
  subgoal for H apply(rule exI[of _ H]) apply safe
  by (metis Rep_filter_inverse)+ .

(* *)

(* Counterpart of rel_filter on the raw type: *)
definition 
rrel_filter :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> (('a \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> (('b \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> bool"
where "rrel_filter R F G \<equiv>
(\<exists>H. is_filter H \<and> H (\<lambda>(x, y). R x y) \<and>
     F = (\<lambda>p. H (\<lambda>(x, y). p x \<and> R x y)) \<and>
     G = (\<lambda>q. H (\<lambda>(x, y). q y \<and> R x y)))"

lemma rel_filter_rrel_filter:
"rel_filter R = inv_imagep (rrel_filter R) Rep_filter"
unfolding rrel_filter_def rel_filter_def2 inv_imagep_def fun_eq_iff apply safe
  subgoal for _ _ H
  apply(rule exI[of _ "Rep_filter H"]) 
  	using is_filter_Rep_filter by blast
  subgoal for _ _ H
  apply(rule exI[of _ "Abs_filter H"]) 
  	by (simp add: eventually_Abs_filter) .

(* The above alternative definition makes the neper properties trivial: *)

lemmas filter.Rep_filter_inject[simp]
lemmas is_filter_Rep_filter[simp]
lemma inj_Rep_filter[simp,intro]: "inj Rep_filter"
unfolding inj_on_def by auto

lemma neper_inv_imagep2: 
"neper (inv_imagep R f) \<Longrightarrow> inj f \<Longrightarrow> Collect t = range f \<Longrightarrow> neper (restr R t)"
  unfolding inv_imagep_def neper_def per_def inj_on_def restr_def set_eq_iff mem_Collect_eq image_iff apply safe
  subgoal by metis
  subgoal by (metis (full_types))
  subgoal by blast
  .

lemma neper_restr_rrel_filter_is_filter: "neper R \<Longrightarrow> neper (restr (rrel_filter R) is_filter)"
apply(frule neper_rel_filter) unfolding rel_filter_rrel_filter 
apply(rule neper_inv_imagep2[where f = Rep_filter]) 
by auto (metis Abs_filter_inverse' range_eqI)  


(* More elementary characterisation of rrel_filter *)

lemma rrel_filter_def2: 
assumes iF: "is_filter F" and iG: "is_filter G"
shows 
"rrel_filter R F G \<longleftrightarrow> 
 (\<forall>p q p'. F p \<and> G q \<and> (\<forall>x y. p x \<and> R x y \<and> q y \<longrightarrow> p' x) \<longrightarrow> F p') \<and> 
 (\<forall>p q q'. F p \<and> G q \<and> (\<forall>x y. p x \<and> R x y \<and> q y \<longrightarrow> q' y) \<longrightarrow> G q')"
proof safe
  fix p q p' q'
  assume "rrel_filter R F G" and Fp: "F p" and Gq: "G q"
  then obtain H where H: "is_filter H" "H (\<lambda>(x, y). R x y)"
  and FH: "F = (\<lambda>p. H (\<lambda>(x, y). p x \<and> R x y))" and GH: "G = (\<lambda>q. H (\<lambda>(x, y). q y \<and> R x y))" 
  unfolding rrel_filter_def by auto
  have 1: "H (\<lambda>(x, y). p x \<and> R x y)" "H (\<lambda>(x, y). q y \<and> R x y)" using Fp FH Gq GH by auto
  {assume 0: "\<forall>x y. p x \<and> R x y \<and> q y \<longrightarrow> p' x"   
   have "H (\<lambda>(x, y). p x \<and> R x y \<and> q y)" 
     using is_filter.conj[OF H(1), of "\<lambda>(x, y). p x \<and> R x y", OF 1]
     by (auto elim!: is_filter.mono[OF H(1), rotated])
  hence "H (\<lambda>(x, y). p' x \<and> R x y)"
    using 0 by (auto elim!: is_filter.mono[OF H(1), rotated])
   with FH show "F p'" unfolding fun_eq_iff by auto
  }
  {assume 0: "\<forall>x y. p x \<and> R x y \<and> q y \<longrightarrow> q' y" 
   have "H (\<lambda>(x, y). p x \<and> R x y \<and> q y)" 
   using is_filter.conj[OF H(1), of "\<lambda>(x, y). p x \<and> R x y", OF 1]
     by (auto elim!: is_filter.mono[OF H(1), rotated])
   hence "H (\<lambda>(x, y). q' y \<and> R x y)" using is_filter.mono[OF H(1)] 
   	 using 0 by (auto elim!: is_filter.mono[OF H(1), rotated])
   with GH show "G q'" unfolding fun_eq_iff by auto
  }
next
  assume F: "\<forall>p q p'. F p \<and> G q \<and> (\<forall>x y. p x \<and> R x y \<and> q y \<longrightarrow> p' x) \<longrightarrow> F p'"
  and G: "\<forall>p q q'. F p \<and> G q \<and> (\<forall>x y. p x \<and> R x y \<and> q y \<longrightarrow> q' y) \<longrightarrow> G q'"
  (* This is the filter generated by the desired projections: *)
  define H where "H \<equiv> \<lambda>pq. \<exists>p q. F p \<and> G q \<and> (\<forall>x y. p x \<and> R x y \<and> q y \<longrightarrow> pq (x,y))"

  show "rrel_filter R F G"
  unfolding rrel_filter_def proof(rule exI[of _ H], safe)
    show "is_filter H"
    unfolding is_filter_def proof safe
      show "H (\<lambda>x. True)" using iF iG unfolding H_def apply(intro exI[of _ "\<lambda>_.True"]) by (auto intro: is_filter.True)
    next
      fix P Q assume "H P" "H Q"
      thus "H (\<lambda>x. P x \<and> Q x)" unfolding H_def apply safe
        subgoal for p pa q qa
        apply(rule exI[of _ "\<lambda>x. p x \<and> pa x"]) apply(rule exI[of _ "\<lambda>y. q y \<and> qa y"])
        using iF iG by (auto intro: is_filter.conj) .
    next
      fix pq pq' assume "\<forall>x. pq x \<longrightarrow> pq' x" and "H pq"
      thus "H pq'" unfolding H_def apply safe subgoal for p q
      apply(rule exI[of _ p]) apply(rule exI[of _ q]) by auto .
    qed
  next
    show "H (\<lambda>(x, y). R x y)" unfolding H_def apply(intro exI[of _ "\<lambda>_.True"]) using iF iG by (auto intro: is_filter.True)
  next
    show "F = (\<lambda>p. H (\<lambda>(x, y). p x \<and> R x y))"
    unfolding fun_eq_iff apply safe
      subgoal for p unfolding H_def   
      apply(rule exI[of _ p]) apply(rule exI[of _ "\<lambda>_.True"]) using iG by (auto intro: is_filter.True)
      subgoal for p unfolding H_def apply safe using F by auto .
  next
    show "G = (\<lambda>q. H (\<lambda>(x, y). q y \<and> R x y))"
    unfolding fun_eq_iff apply safe
      subgoal for q unfolding H_def   
      apply(rule exI[of _ "\<lambda>_.True"]) apply(rule exI[of _ q])  using iF by (auto intro: is_filter.True)
      subgoal for q unfolding H_def apply safe using G by auto . 
  qed
qed

(* *)

definition ff where 
"ff R F \<equiv> \<lambda>p. F (\<lambda>x. \<forall>x'. R x x' \<longrightarrow> p x')"

lemma rel_fun_ff:
"neper R \<Longrightarrow> rrel_filter R F G \<Longrightarrow>
 rel_fun (rel_fun R (=)) (=) (ff R F) (ff R G)"
unfolding inv_imagep_def
unfolding rrel_filter_def ff_def apply safe
  subgoal premises prems for H unfolding rel_fun_def fun_eq_iff using prems(1)
    apply (auto elim!: is_filter.mono[rotated 2, of H] simp: prems(2))
    apply (metis neper_sym)
    .
  done

lemma is_filter_ff:
"neper R \<Longrightarrow> is_filter F \<Longrightarrow> is_filter (ff R F)"
  unfolding is_filter_def[of "ff R F"] unfolding  ff_def
  by (auto intro: is_filter.True simp: eventually_Abs_filter[of F, symmetric]
    elim: eventually_elim2 eventually_mono)

lemma is_filter_rlt_ff:
"neper R \<Longrightarrow> is_filter F \<Longrightarrow> is_filter_rlt R (ff R F)"
  unfolding is_filter_def[of "ff R F"] unfolding  ff_def
  apply (auto intro: is_filter.True simp: eventually_Abs_filter[of F, symmetric]
    elim: eventually_elim2)
  apply (erule eventually_mono)
  by (metis neper_sym neper_trans)

lemma rrel_filter_upwards: 
assumes R: "neper R" and F: "is_filter F" and FF: "rrel_filter R F F" and 
Fp: "F p" and 0: "\<forall>x. R x x \<and> p x \<longrightarrow> p' x"
shows "F p'" 
apply(rule FF[unfolded rrel_filter_def2[OF F F], 
   THEN conjunct1, rule_format, folded atomize_conjL, OF Fp Fp]) 
using 0 R by (metis neper_per per_def) 

lemma ff_rrel_filter: 
assumes R: "neper R" and F: "is_filter F" and G: "is_filter G" 
and rFF: "rrel_filter R F F" and rGG: "rrel_filter R G G"
and FG: "rel_fun (rel_fun R (=)) (=) (ff R F) (ff R G)"
shows "rrel_filter R F G"
unfolding rrel_filter_def2[OF F G] proof safe
  fix p q p' assume Fp: "F p" and Gq: "G q" and 0: "\<forall>x y. p x \<and> R x y \<and> q y \<longrightarrow> p' x"
  have FF: "rel_fun (rel_fun R (=)) (=) (ff R F) (ff R F)"
    using FG R rFF rel_fun_ff by blast
  have "G (\<lambda>x. \<exists>y. R x y \<and> q y)"
  apply(rule rGG[unfolded rrel_filter_def2[OF G G], 
   THEN conjunct1, rule_format, folded atomize_conjL, OF Gq Gq]) by auto
  hence 1: "G (\<lambda>x. \<forall>x'. R x x' \<longrightarrow> (\<exists>y. R x' y \<and> q y))"
    by (rule is_filter.mono[OF G, rotated]) (metis R neper_sym_eq neper_trans)
  have "F (\<lambda>x. \<forall>x'. R x x' \<longrightarrow> (\<exists>y. R x' y \<and> q y))" using FG[unfolded rel_fun_def[of "rel_fun R (=)"] ff_def, 
     rule_format, of "\<lambda>x. \<exists>y. R x y \<and> q y" "\<lambda>x. \<exists>y. R x y \<and> q y"] 
  using 1 unfolding rel_fun_def by (metis R neper_def per_def)
  hence 2: "F (\<lambda>x. \<exists>y. R x y \<and> q y)"
    using F R rFF rrel_filter_upwards by fastforce
  show "F p'" using 2 Fp
    unfolding eventually_Abs_filter[OF F, symmetric, of p]
              eventually_Abs_filter[OF F, symmetric, of p']
              eventually_Abs_filter[OF F, symmetric, of "\<lambda>x. \<exists>y. R x y \<and> q y"]
    by (rule eventually_elim2) (blast intro: 0[rule_format])
next
  fix p q q' assume Fp: "F p" and Gq: "G q" and 0: "\<forall>x y. p x \<and> R x y \<and> q y \<longrightarrow> q' y"
  have GG: "rel_fun (rel_fun R (=)) (=) (ff R G) (ff R G)"
    by (simp add: R rGG rel_fun_ff)
  have "F (\<lambda>y. \<exists>x. p x \<and> R x y)"
  apply(rule rFF[unfolded rrel_filter_def2[OF F F], 
   THEN conjunct1, rule_format, folded atomize_conjL, OF Fp Fp])  
    by (meson R neper_per per_def) 
  hence 1: "F (\<lambda>y. \<forall>y'. R y y' \<longrightarrow> (\<exists>x. p x \<and> R x y'))"
    by (rule is_filter.mono[OF F, rotated]) (meson R neper_trans)
  have "G (\<lambda>y. \<forall>y'. R y y' \<longrightarrow> (\<exists>x. p x \<and> R x y'))" using FG[unfolded rel_fun_def[of "rel_fun R (=)"] ff_def, 
     rule_format, of "\<lambda>y. \<exists>x. p x \<and> R x y" "\<lambda>y. \<exists>x. p x \<and> R x y"] 
  using 1 unfolding rel_fun_def by (metis R neper_def per_def)
  hence 2: "G (\<lambda>y. \<exists>x. p x \<and> R x y)"
    using G R rGG rrel_filter_upwards by fastforce
  show "G q'" using 2 Gq
    unfolding eventually_Abs_filter[OF G, symmetric, of q]
              eventually_Abs_filter[OF G, symmetric, of q']
              eventually_Abs_filter[OF G, symmetric, of "\<lambda>y. \<exists>x. p x \<and> R x y"]
    by (rule eventually_elim2) (blast intro: 0[rule_format])
qed

(* *)

definition Rep_filter' where
"Rep_filter' R F \<equiv> (\<lambda>p. Rep_filter F (\<lambda>x. \<forall>y. R x y \<longrightarrow> p y))"

lemma ex_ff_rrel_filter_rel_fun: 
assumes R: "neper R" and rFF: "is_filter_rlt R FF" and FF: "rel_fun (rel_fun R (=)) (=) FF FF"
shows "\<exists> F. is_filter F \<and> rrel_filter R F F \<and> rel_fun (rel_fun R (=)) (=) FF (ff R F)" 
proof-
  have FF1: "FF (\<lambda>x. True)" and 
  FF2: "\<And>p pa. rel_fun R (=) p p \<Longrightarrow> rel_fun R (=) pa pa \<Longrightarrow> FF p \<Longrightarrow> FF pa 
                \<Longrightarrow> FF (\<lambda>x. p x \<and> pa x)" and 
  FF3: "\<And>p pa. rel_fun R (=) p p \<Longrightarrow> rel_fun R (=) pa pa \<Longrightarrow> (\<forall>xb. R xb xb \<and> p xb \<longrightarrow> pa xb) 
          \<Longrightarrow> FF p \<Longrightarrow> FF pa" 
  using rFF[unfolded is_filter_rlt_simp[OF R]] by auto
  define F where "F \<equiv> \<lambda>p. FF (\<lambda>x. \<forall>y. R x y \<longrightarrow> p y)"

  show ?thesis proof(rule exI[of _ F], safe)
    show iF: "is_filter F" unfolding is_filter_def 
    proof safe
      show "F (\<lambda>x. True)" unfolding F_def using FF1 by auto
    next
      fix P Q assume 1: "F P" "F Q"
      have 2: "FF (\<lambda>x. (\<forall>y. R x y \<longrightarrow> P y) \<and> (\<forall>y. R x y \<longrightarrow> Q y))" 
      apply(rule FF2) using 1 unfolding rel_fun_def F_def  
      by (meson R neper_per per_def)+
      show "F (\<lambda>x. P x \<and> Q x)" unfolding F_def apply(rule FF3[OF _ _ _ 2])
      unfolding rel_fun_def by (meson R neper_per per_def)+
    next
      fix P Q assume 1: "\<forall>x. P x \<longrightarrow> Q x" and FP: "F P"
      show "F Q" unfolding F_def apply(rule FF3[OF _ _ _ FP[unfolded F_def]])
      using 1 unfolding rel_fun_def by (metis R neper_per per_def)+
    qed
  (* *)
    show "rrel_filter R F F"
    unfolding rrel_filter_def2[OF iF iF] proof safe
      fix p q p' assume Fp: "F p" and Fq: "F q" and 0: "\<forall>x y. p x \<and> R x y \<and> q y \<longrightarrow> p' x"
      have 1: "FF (\<lambda>x. (\<forall>y. R x y \<longrightarrow> p y) \<and> (\<forall>y. R x y \<longrightarrow> q y))"
      apply(rule FF2) using Fp Fq unfolding rel_fun_def F_def  
      by (meson R neper_per per_def)+
      show "F p'" unfolding F_def apply(rule FF3[OF _ _ _ 1])
      using 0 unfolding rel_fun_def by (meson R neper_per per_def)+
    next
      fix p q q' assume Fp: "F p" and Fq: "F q" and 0: "\<forall>x y. p x \<and> R x y \<and> q y \<longrightarrow> q' y"
      have 1: "FF (\<lambda>x. (\<forall>y. R x y \<longrightarrow> p y) \<and> (\<forall>y. R x y \<longrightarrow> q y))"
      apply(rule FF2) using Fp Fq unfolding rel_fun_def F_def  
      by (meson R neper_per per_def)+
      show "F q'" unfolding F_def apply(rule FF3[OF _ _ _ 1])
      using 0 unfolding rel_fun_def by (meson R neper_per per_def)+
    qed
  (* *)
    show "rel_fun (rel_fun R (=)) (=) FF (ff R F)"
    unfolding rel_fun_def[of "rel_fun R (=)"] proof clarify
      fix p q :: "'a \<Rightarrow> bool" assume pq: "rel_fun R (=) p q"
      show "FF p = ff R F q" unfolding ff_def F_def 
      apply(rule FF[unfolded rel_fun_def[of "rel_fun R (=)"], rule_format])
      using pq unfolding rel_fun_def by (metis R neper_per per_def)
    qed
  qed
qed

lemma bij_upto_ff: 
"neper R \<Longrightarrow> 
 bij_upto 
   (restr (rrel_filter R) is_filter) 
   (restr (rel_fun (rel_fun R (=)) (=)) (is_filter_rlt R))
   (ff R)"
apply(intro bij_uptoI)
  subgoal apply(rule neper_restr)
    subgoal by auto
    subgoal apply(rule exI[of _ "\<lambda>_. True"]) by auto .
  subgoal for F F' unfolding restr_def  
  	using is_filter_rlt_ff rel_fun_ff by blast
  subgoal for F F' unfolding restr_def  
  	using ff_rrel_filter by blast
  subgoal unfolding restr_def  
  	using ex_ff_rrel_filter_rel_fun is_filter_rlt_ff by blast .

lemma bij_upto_ff_Rep_filter: 
"neper R \<Longrightarrow> 
 bij_upto 
   (rel_filter R) 
   (restr (rel_fun (rel_fun R (=)) (=)) (is_filter_rlt R))
   (ff R o Rep_filter)"
apply(rule bij_upto_transportFromRaw[OF filter.type_definition_filter rel_filter_rrel_filter])
using bij_upto_ff .

lemma ff_eq[simp]: "ff (=) = id"
unfolding ff_def by auto
    
wide_typedef filter rel: rel_filter rep: "\<lambda>R. ff R o Rep_filter"
  subgoal using neper_rel_filter .
  subgoal using rel_filter_eq .
  subgoal using bij_upto_ff_Rep_filter . 
  subgoal using ff_eq by simp .

(* *)

local_setup \<open>RLTHM @{binding Maclaurin_lemma2_rlt} @{thm Maclaurin_lemma2}\<close>
thm Maclaurin_lemma2
thm Maclaurin_lemma2_rlt
thm Maclaurin_lemma2_rlt[simplified rlt_eq rrel_eq, OF refl refl refl refl refl]

local_setup \<open>RLTHM @{binding Taylor_rlt} @{thm Taylor}\<close>
thm Taylor
thm Taylor_rlt
thm Taylor_rlt[simplified rlt_eq rrel_eq, OF refl refl refl refl refl refl refl]
  
   

(*****************)
(* Default relativization applied to the type "filter" (I keep it here just for documentation: *)

definition fff :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> (('a \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
where 
"fff R F \<equiv> (\<lambda>p. F (\<lambda>x. \<forall>y. R x y \<longrightarrow> p y))"

lemma fff_eq[simp]: "fff (=) = id"
unfolding fff_def by auto

lemma is_filter_rlt_fff:
assumes R: "neper R" and F: "is_filter F"
shows "is_filter_rlt R (fff R F)"
proof-
  define FF where "FF = Abs_filter F"
  have 0: "F = Rep_filter FF"   
  	by (simp add: Abs_filter_inverse' F FF_def)
  show ?thesis unfolding fff_def 0
  unfolding is_filter_rlt_simp[OF R] apply auto
  unfolding eventually_def 
	using R
	 apply (auto elim: eventually_elim2) []
	apply (unfold 0[symmetric])
	apply (erule is_filter.mono[OF F, rotated])
	by (metis R neper_sym_eq neper_trans)
qed

lemma rel_fun_fff:
assumes R: "neper R" and F: "is_filter F"
shows "rel_fun (rel_fun R (=)) (=) (fff R F) (fff R F)"
  unfolding fff_def rel_fun_def
  by (auto elim!: is_filter.mono[OF F, rotated]) (metis R neper_sym_eq neper_trans)+

lemma fff_surj_upto: 
assumes R: "neper R" 
and FF: "is_filter_rlt R FF" "rel_fun (rel_fun R (=)) (=) FF FF"
shows "\<exists>F. is_filter F \<and> rel_fun (rel_fun R (=)) (=) FF (fff R F)"
proof-
  define F where "F \<equiv> (\<lambda>p. \<exists>p'\<le>p. rel_fun R (=) p' p' \<and> FF p')" 
  show ?thesis proof(rule exI[of _ F], safe)
    show "is_filter F"
    unfolding is_filter_def proof safe
      show "F (\<lambda>x. True)" unfolding F_def using R assms(2) by auto
    next
      fix P Q assume "F P" "F Q"
      then obtain P' Q' where P': "P'\<le>P \<and> rel_fun R (=) P' P' \<and> FF P'"
      and Q': "Q'\<le>Q \<and> rel_fun R (=) Q' Q' \<and> FF Q'"
      unfolding F_def by auto
      hence "FF (\<lambda>x. P' x \<and> Q' x)" using R assms(2) by auto
      moreover have "rel_fun R (=) (\<lambda>x. P' x \<and> Q' x) (\<lambda>x. P' x \<and> Q' x)"
      using P' Q' unfolding rel_fun_def by auto
      moreover have "(\<lambda>x. P' x \<and> Q' x) \<le> (\<lambda>x. P x \<and> Q x)"
      using P' Q' by auto
      ultimately show "F (\<lambda>x. P x \<and> Q x)" unfolding F_def by blast
    next
      fix P Q assume 0: "\<forall>x. P x \<longrightarrow> Q x"
      and FP: "F P"
      then obtain P' where P': "P'\<le>P \<and> rel_fun R (=) P' P' \<and> FF P'"
      unfolding F_def by auto
      thus "F Q" using 0 unfolding F_def by auto
    qed
  next
    show "rel_fun (rel_fun R (=)) (=) FF (fff R F)"
    unfolding rel_fun_def[of "rel_fun R (=)"] proof clarify
      fix P Q :: "'a \<Rightarrow> bool" assume PQ: "rel_fun R (=) P Q" 
      hence PP: "rel_fun R (=) P P" and QQ: "rel_fun R (=) Q Q"
        by (metis R neper_eq neper_rel_fun neper_sym_eq neper_trans)+
      show "FF P = fff R F Q" unfolding fff_def F_def apply safe
        subgoal apply(rule exI[of _ "\<lambda>x. \<forall>y. R x y \<longrightarrow> Q y"], safe)
          subgoal using QQ unfolding rel_fun_def  
          	by (metis R mem_Collect_eq neper_classes_eq)
          subgoal
            using is_filter_rlt_simp[OF R, THEN iffD1, OF assms(2),
                THEN conjunct2, THEN conjunct2, rule_format, of P "(\<lambda>p'. \<forall>y. R p' y \<longrightarrow> Q y)"] PP PQ
              \<open>FF P \<Longrightarrow> rel_fun R (=) (\<lambda>p'. \<forall>y. R p' y \<longrightarrow> Q y) (\<lambda>p'. \<forall>y. R p' y \<longrightarrow> Q y)\<close>
              rel_funD[of "R" "(=)"]
            by blast .
        subgoal for P'
          using is_filter_rlt_simp[OF R, THEN iffD1, OF assms(2),
              THEN conjunct2, THEN conjunct2, rule_format, of P' P] PP PQ rel_funD2
          by fastforce .
      qed
  qed
qed

context fixes R :: "'a\<Rightarrow>'a\<Rightarrow>bool"
begin

definition 
"rrrel_filter \<equiv> 
 inv_imagep (restr (inv_imagep (restr (rel_fun (rel_fun R (=)) (=)) 
   (is_filter_rlt R)) (fff R)) is_filter)
   Rep_filter" 

definition "ggg \<equiv> fff R \<circ> Rep_filter"

lemmas bij_uptoC = 
  bij_upto_criterion[OF type_definition_filter, 
   of "rel_fun (rel_fun R (=)) (=)" "is_filter_rlt R" "fff R",
   unfolded rrel_filter_def[symmetric] ggg_def[symmetric]]

lemmas neperC = neper_criterion[OF type_definition_filter, 
   of "rel_fun (rel_fun R (=)) (=)" "is_filter_rlt R" "fff R",
   unfolded rrel_filter_def[symmetric] ggg_def[symmetric]]

end

lemmas eqC = eq_criterion[OF type_definition_filter, 
   of "is_filter", unfolded rrel_filter_def[symmetric, of "(=)", simplified] ] 


(* The below fail now because the type is already registered as wide, but 
would work if one comments away the previous wide_typedef *)
(* 
wide_typedef filter rel: rrrel_filter rep: ggg
  unfolding rrrel_filter_def rrel_eq rlt_eq fff_eq
  subgoal for R apply(rule neperC) 
    apply force
    using is_filter_Rep_filter apply blast
    using is_filter_rlt_fff rel_fun_fff by blast
  subgoal apply(rule eqC) by auto
  subgoal for R apply(rule bij_uptoC)
    apply force
    using is_filter_rlt_fff rel_fun_fff apply blast
    using fff_surj_upto by blast
  subgoal unfolding ggg_def by auto .
*)

(* The type of bijections: *)

(* Prefer this to the bij abbreviation: *)
definition "biject (f::'a\<Rightarrow>'a) \<equiv> (\<forall>a a'. f a = f a' \<longrightarrow> a = a') \<and> (\<forall>b. \<exists>a. f a = b)"

local_setup \<open> RLCST @{term biject} \<close>

lemma biject_rlt_simp[simp]: "neper R \<Longrightarrow> 
biject_rlt R f \<longleftrightarrow>  
(\<forall>x xa. R x x \<and> R xa xa \<and> R (f x) (f xa) \<longrightarrow> R x xa) \<and>
(\<forall>x. R x x \<longrightarrow> (\<exists>xa. R xa xa \<and> R (f xa) x))"
  unfolding biject_rlt_def by auto

lemma biject_rlt_eq[simp]: "biject_rlt (=) = biject"
  unfolding biject_rlt_def biject_def by auto

typedef 'a biject = "{f::'a\<Rightarrow>'a. biject f}" 
  unfolding biject_def by auto

definition makeCompat :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)" where 
  "makeCompat R f \<equiv> if biject_rlt R (\<lambda>a. f (getRepr R a)) then (\<lambda>a. f (getRepr R a)) else id"

lemma biject_rlt_id: "neper R \<Longrightarrow> biject_rlt R id"  
	by auto

lemma makeCompat_biject_biject_rlt: 
  assumes R: "neper R" and f: "biject f"
  shows "biject_rlt R (makeCompat R f)"
  apply(cases "biject_rlt R (\<lambda>a. f (getRepr R a))")
  apply (simp add: makeCompat_def) 
  by (metis R biject_rlt_id makeCompat_def)

definition makeCompat1 :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a biject \<Rightarrow> ('a \<Rightarrow> 'a)" where 
  "makeCompat1 R f \<equiv> makeCompat R (Rep_biject f)"

lemma makeCompat1_biject_biject_rlt: 
  assumes R: "neper R" 
  shows "biject_rlt R (makeCompat1 R f)" 
  by (metis assms biject_rlt_id makeCompat1_def makeCompat_def)

term "inv_imagep (rel_fun R R) (makeCompat1 R)"

lemma Abs_biject_inverse_id[simp]: "Rep_biject (Abs_biject id) = id"
  by (simp add: Abs_biject_inverse biject_def)

lemma biject_rlt_getRepr: "neper R \<Longrightarrow> biject_rlt R (getRepr R)"
  by simp (metis getRepr_neper neper_def per_def)

lemma rel_fun_getRepr: "neper R \<Longrightarrow> rel_fun R R (getRepr R) (getRepr R)"
  unfolding rel_fun_def by (metis geterRepr_related neper_sym neper_trans)

lemma makeCompat_eq[simp]: "makeCompat (=) f = (if biject f then f else id)"
  unfolding makeCompat_def by simp

lemma makeCompat1_eq[simp]: "makeCompat1 (=) = Rep_biject"
  unfolding makeCompat1_def using Rep_biject by force

lemma rel_fun_makeCompat1_id: 
  "neper R \<Longrightarrow> rel_fun R R (makeCompat1 R (Abs_biject id)) (makeCompat1 R (Abs_biject id))"
  unfolding makeCompat1_def 
  by (auto simp: biject_rlt_getRepr makeCompat_def rel_fun_getRepr)

lemma rel_fun_makeCompat: 
  "neper R \<Longrightarrow> rel_fun R R f f \<Longrightarrow> 
  rel_fun R R (makeCompat R f) (makeCompat R f)"
  unfolding makeCompat_def
  using rel_fun_getRepr[of R]
  by (auto simp only: rel_fun_def simp_thms id_apply split: if_splits)

context includes cardinal_syntax begin
lemma card_eq_minus:
assumes "{a,a'} \<subseteq> A"
shows "|A - {a}| =o |A - {a'}|"
  using assms
  by (intro card_of_ordIsoI[where f="if a = a' then id else (\<lambda>x. if x = a' then a else if x = a then a' else x)"])
    (auto simp: bij_betw_def inj_on_def)

lemma bij_betw_combine3: 
"bij_betw f A1 B1 \<Longrightarrow> bij_betw f A2 B2 \<Longrightarrow> bij_betw f A3 B3 \<Longrightarrow> 
 B1 \<inter> B2 = {} \<Longrightarrow> B1 \<inter> B3 = {} \<Longrightarrow> B2 \<inter> B3 = {} \<Longrightarrow> 
 bij_betw f (A1 \<union> A2 \<union> A3) (B1 \<union> B2 \<union> B3)" 
by (simp add: bij_betw_combine inf_sup_distrib2)

lemma biject_rlt_ex_getRepr: 
assumes R: "neper R" and f: "biject_rlt R f" "rel_fun R R f f"
shows "\<exists>g. biject g \<and> 
   (\<forall>a. R a a \<longrightarrow> g (getRepr R a) = f (getRepr R a)) \<and>
   biject_rlt R (\<lambda>a. g (getRepr R a))"
proof-
  define A where A: "A \<equiv> {a. R a a \<and> a = getRepr R a}"
  have "inj_on f A"
  unfolding inj_on_def A proof safe 
    fix a b assume a: "R a a" "a = getRepr R a" 
    and b: "R b b" "b = getRepr R b"
    and fab: "f a = f b" 
    have "R (f a) (f b)" unfolding fab using R f by (simp add: b(1) rel_funD2)
    hence "R a b" using R a(1) b(1) biject_rlt_simp f(1) by blast
    show "a = b" by (metis R \<open>R a b\<close> a(2) b(2) neper_getRepr_eq)
  qed

  have "|A| =o |f ` A|" 
  	by (metis \<open>inj_on f A\<close> card_of_image ordIso_iff_ordLeq the_inv_into_onto)

  define K11 where K11: "K11 \<equiv> \<lambda>a. {a'. R a a'} - {a}" 
  define K1 where K1: "K1 \<equiv> (\<Union> {K11 a | a. a \<in> A})"
  have 1: "UNIV = {a. \<not> R a a} \<union> A \<union> K1"
  unfolding K1 K11 using A
  by auto
    (metis (no_types, lifting) CollectI R getRepr_neper geterRepr_related insertE insert_Diff neper_getRepr_eq neper_trans)

  have 21: "f ` A \<subseteq> {a. R a a}"
  	using A f(2) rel_funE by fastforce

  have f0: "(\<forall>x xa. R x x \<and> R xa xa \<and> R (f x) (f xa) \<longrightarrow> R x xa) \<and> 
         (\<forall>x. R x x \<longrightarrow> (\<exists>xa. R xa xa \<and> R (f xa) x))" using R f(1)  
    by (metis biject_rlt_simp)

  have 22: "{a'. R a' a'} \<subseteq> {a'. \<exists>a\<in>f ` A. R a a'}"
  proof auto 
   fix x assume "R x x"
   then obtain a' where "R a' a'" and "R (f a') x"  
   	 using f0 by blast
   thus "\<exists>a\<in>A. R (f a) x"
     apply(intro bexI[of _ "getRepr R a'"])
      apply (metis R f(2) geterRepr_related neper_per per_def rel_funE)
     unfolding A mem_Collect_eq
     by (metis R getRepr_inject getRepr_neper rel_funE rel_fun_getRepr)
  qed
  
  have 2: "UNIV = {a. \<not> R a a} \<union> f ` A \<union> (\<Union> {{a'. R a a' \<and> a' \<noteq> a} | a. a \<in> f ` A})"
  using 21 22 apply auto using imageI by blast

  have "\<forall>a\<in>A. \<exists>aa\<in>A. R a (f aa)" unfolding A Ball_def Bex_def mem_Collect_eq
    apply safe
    subgoal for x
      apply (frule f0[THEN conjunct2, rule_format, of x])
      apply (erule exE conjE)+
      subgoal for y
        apply (rule exI[of _ "getRepr R y"])
        apply safe
          apply (metis R rel_funD rel_fun_getRepr)
         apply (meson R getRepr_neper neper_getRepr_eq)
        apply (metis R f(2) getRepr_neper neper_sym_eq neper_trans rel_funE)
        done
      done
    done

  then obtain hh where hh: "\<forall>a\<in>A. hh a \<in> A \<and> R a (f (hh a))"  
  	by metis

  have getRepr_hh: "\<forall>a\<in>A. hh a = getRepr R (hh a)" 
  using A hh by blast

  define K22 where K22: "K22 \<equiv> \<lambda>a. {a'. R a a'} - {f (hh a)}" 
  define K2 where K2: "K2 \<equiv> (\<Union> {K22 a | a. a \<in> A})"

  have K2': "(\<Union> {{a'. R a a' \<and> a' \<noteq> a} | a. a \<in> f ` A}) = K2"
    unfolding K2 K22 apply(rule arg_cong[of _ _ Union], safe)
    subgoal for _ _ b
      apply(rule exI[of _ "getRepr R (f b)"])
      using hh f(2) unfolding A mem_Collect_eq Ball_def rel_fun_def
      apply -
      apply (drule spec[of _ "getRepr R (f b)"])
      apply auto
                       apply (metis R rel_funE rel_fun_getRepr)
                      apply (metis R rel_funE rel_fun_getRepr)
                     apply (metis R rel_funE rel_fun_getRepr)
                    apply (metis R rel_funE rel_fun_getRepr)
                   apply (metis R rel_funE rel_fun_getRepr)
                  apply (metis R getRepr_neper neper_getRepr_eq)
                 apply (metis R getRepr_neper neper_getRepr_eq)
                apply (metis R getRepr_neper neper_getRepr_eq)
               apply (metis R getRepr_neper neper_getRepr_eq)
              apply (metis R neper_getRepr_eq)
             apply (metis R getRepr_neper neper_getRepr_eq)
            apply (metis R getRepr_neper neper_getRepr_eq)
           apply (metis R geterRepr_related neper_sym neper_trans)
          apply (metis R f0 neper_getRepr_eq)
         apply (metis R getRepr_neper neper_trans)
        apply (metis R f0 neper_getRepr_eq neper_sym neper_trans)
       apply (metis R neper_sym neper_trans)
      apply (metis R getRepr_neper neper_getRepr_eq)
      done
    subgoal for _ a apply(rule exI[of _ "f (hh a)"])
    using R hh neper_classes_eq by fastforce+ .

  hence 2: "UNIV = {a. \<not> R a a} \<union> f ` A \<union> K2"
  using 2 by auto

  {fix a assume "a \<in> A"
   have "|K11 a| =o |K22 a|" unfolding K11 K22
   by (metis (no_types, lifting) A \<open>a \<in> A\<close> bot.extremum card_eq_minus hh insert_subset mem_Collect_eq)
   hence "\<exists>uu. bij_betw uu (K11 a) (K22 a)"
   using card_of_ordIso by blast
  }
  then obtain uu where uu: "\<And>a. a\<in>A \<Longrightarrow> bij_betw (uu a) (K11 a) (K22 a)"
  by metis
  hence uu': "\<And>a. a\<in>A \<Longrightarrow>  uu a ` (K11 a) = K22 a" unfolding bij_betw_def by auto

  define u where "u \<equiv> \<lambda>a'. uu (getRepr R a') a'"

  have u: "bij_betw u K1 K2"  
  unfolding bij_betw_def inj_on_def proof safe
    fix x y assume x: "x \<in> K1" and y: "y \<in> K1" and "u x = u y"
    hence uuxy: "uu (getRepr R x) x = uu (getRepr R y) y" 
    unfolding u_def K1 
	  using R neper_classes_eq by auto

    have Rxy: "R x x" "R y y" using x y unfolding K1 K11 A  
    	using R neper_classes_eq by fastforce+

    hence xA: "getRepr R x \<in> A" unfolding A apply auto  
    	apply (metis R rel_funE rel_fun_getRepr)  
    	by (meson R getRepr_neper neper_getRepr_eq)

    have xy: "x \<in> K11 (getRepr R x)" "y \<in> K11 (getRepr R y)" using x y unfolding K1 A 
    	by (simp,metis Diff_iff K11 R mem_Collect_eq neper_getRepr_eq)+

    show "x = y"
    proof(cases "R x y")
      case True
      hence 0: "getRepr R x = getRepr R y"  
      	by (simp add: R neper_getRepr_eq)
      thus ?thesis 
      using uu[of "getRepr R x"] uuxy xA xy unfolding bij_betw_def inj_on_def by auto
    next
      case False
      hence False using uuxy xy R uu'[of "getRepr R x"] uu'[of "getRepr R y"]
        unfolding K11 K22 A mem_Collect_eq
        by (metis (no_types, opaque_lifting) Diff_iff image_eqI mem_Collect_eq neper_classes_eq neper_getRepr_eq neper_sym)
      thus ?thesis by simp
    qed
  next
    fix a assume "a \<in> K1" 
    thus "u a \<in> K2"
    unfolding u_def K1 K2 using uu[of "getRepr R a"] unfolding bij_betw_def 
    by simp (metis (mono_tags, lifting) A DiffE K11 R image_eqI mem_Collect_eq neper_getRepr_eq)
  next
    fix b2 assume "b2 \<in> K2" 
    then obtain a2 where "b2 \<in> K22 a2" and "a2 \<in> A" unfolding K2 by auto
    then obtain a1 where "a1 \<in> K11 a2" and "uu a2 a1 = b2"
    by (metis imageE uu')

    thus "b2 \<in> u ` K1" unfolding K1 image_def u_def  
    by simp (metis (mono_tags, lifting) A DiffE K11 R \<open>a2 \<in> A\<close> mem_Collect_eq neper_getRepr_eq)
  qed

  define g where "g \<equiv> \<lambda>a. if \<not> R a a then a else if a \<in> A then f a else u a"
  have g[simp]: "\<And>a. \<not> R a a \<Longrightarrow> g a = a"
  "\<And>a. a \<in> A \<Longrightarrow> g a = f a"
  "\<And>a. a \<in> K1 \<Longrightarrow> g a = u a"
  unfolding g_def  
  unfolding A K1 K11 apply auto  
  apply (simp add: R neper_getRepr_eq) 
  apply (metis R neper_getRepr_eq) 
  using R neper_classes_eq by fastforce

  have g: "bij_betw g UNIV UNIV"
  apply(subst 1) apply(subst 2)
  apply(rule bij_betw_combine3)
    subgoal unfolding bij_betw_def inj_on_def by auto
    subgoal using \<open>inj_on f A\<close> unfolding bij_betw_def inj_on_def by auto  
    subgoal using u unfolding bij_betw_def inj_on_def by auto 
  subgoal using "21" by auto
  subgoal unfolding K2 K22 by auto (metis R mem_Collect_eq neper_classes_eq)
  subgoal unfolding K2'[symmetric] 
  	by auto (metis (mono_tags, lifting) A R f0 mem_Collect_eq neper_getRepr_eq) .

  have gf_getRepr: "\<And>x. R x x \<Longrightarrow> g (getRepr R x) = f (getRepr R x)"
    using A R g_def getRepr_inject getRepr_neper rel_funD rel_fun_getRepr by fastforce

  show ?thesis apply(rule exI[of _ g])
    using g unfolding bij_betw_def biject_def apply auto 
    apply (meson inj_eq)  
    apply (metis surjD) 
    using gf_getRepr apply blast
    using R apply simp apply safe  
     apply (metis (full_types) biject_rlt_getRepr biject_rlt_simp f(1) gf_getRepr rel_funE rel_fun_getRepr)
  proof -
    fix x :: 'a
    assume a1: "neper R"
    assume a2: "R x x"
    have f3: "per R"
      using a1 neper_per by blast
    have f4: "R x (getRepr R x)"
      using a2 a1 by (simp add: getRepr_neper)
    then have f5: "getRepr R (getRepr R x) = getRepr R x"
      using a1 by (metis (no_types) neper_getRepr_eq)
    have f6: "R (getRepr R x) x"
      using f4 f3 by (meson per_def)
    have f7: "\<And>a. \<not> R a x \<or> R a (getRepr R x)"
      using f4 f3 by (metis (no_types) per_def)
    obtain aa :: "'a \<Rightarrow> 'a" where
      f8: "\<And>a. (a \<notin> A \<or> aa a \<in> A) \<and> (a \<notin> A \<or> R a (f (aa a)))"
      using \<open>\<forall>a\<in>A. \<exists>aa\<in>A. R a (f aa)\<close> by moura
    then have "getRepr R x \<notin> A \<or> R (f (aa (getRepr R x))) x"
      using f6 f3 by (metis (no_types) per_def)
    then show "\<exists>a. R a a \<and> R (g (getRepr R a)) x"
      using f8 f7 f6 f5 A by fastforce
  qed
qed

end

lemma biject_rlt_ex_makeCompat: 
assumes R: "neper R" and f: "biject_rlt R f" "rel_fun R R f f"
shows "\<exists>g. biject g \<and> rel_fun R R f (makeCompat R g)"
proof-
  from biject_rlt_ex_getRepr[OF R f] 
  obtain g where bg: "biject g" and g: "\<forall>a. R a a \<longrightarrow> g (getRepr R a) = f (getRepr R a)"  
  and b: "biject_rlt R (\<lambda>a. g (getRepr R a))" by auto 
  have "rel_fun R R f (makeCompat R g)" unfolding makeCompat_def using b apply simp
  using g R unfolding rel_fun_def  
  by (metis (no_types, lifting) f(2) getRepr_neper neper_per per_def rel_fun_def)
  thus ?thesis using bg by auto
qed
  
wide_typedef biject
  rel: "\<lambda>R. inv_imagep (rel_fun R R) (makeCompat1 R)" 
  rep: makeCompat1 via type_definition_biject
  subgoal for R
    apply(rule neper_inv_imagep[of _ _ "Abs_biject id"])
    by (auto simp: rel_fun_makeCompat1_id)
  subgoal apply simp unfolding inv_imagep_def  
    by (simp add: Rep_biject_inject)
  subgoal for R unfolding bij_upto_def restr_def apply safe 
    subgoal unfolding inv_imagep_def .
    subgoal using makeCompat1_biject_biject_rlt by blast
    subgoal using makeCompat1_biject_biject_rlt by blast
    subgoal unfolding inv_imagep_def .
    subgoal for f unfolding inv_imagep_def makeCompat1_def  
    by (metis (no_types, lifting) Abs_biject_inverse biject_rlt_ex_makeCompat 
      makeCompat_biject_biject_rlt mem_Collect_eq neper_per per_def per_rel_fun)
    subgoal by (metis neper_def per_def per_rel_fun) .
  subgoal by simp
  done

end
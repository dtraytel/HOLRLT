theory Counterexample
  imports MainRLT 
begin

lemma bij_upto_surjE:
  "bij_upto P Q f \<Longrightarrow> Q y y \<Longrightarrow> \<exists>x. P x x \<and> Q y (f x)"
  unfolding bij_upto_def by blast

(* Next is a formalization of the paper's Example 6, 
showing a type definition of a type \<tau> that, not being wide, cannot support 
a suitable relativization infrastructure on the defined type. 

As explained in the paper, the root cause for this 
is that the defining predicate t has smaller cardinality than 
its relativized version t_rlt, even after quotienting t_rlt to the 
PER relational interpretation on the host type 'a \<sigma>.  

To exhibit this problem, we take 'a \<sigma> to be ind\<Rightarrow>'a and we prove that,
for a large enough instance of 'a, namely ind\<Rightarrow>bool and a small
enough PER R on 'a (one given by a small enough set A), we have the following:
-- t is a singleton, whereas
-- the set of RIN(ind\<Rightarrow>bool)-classes that satisfy t_rlt has at least
two elements.*)

definition t :: "(ind \<Rightarrow> 'a) \<Rightarrow> bool" where
  "t \<equiv> \<lambda>f. (\<forall>x. \<exists>i. f i = x) \<or> (\<forall>i. f i = (SOME x. True))"

typedef 'a \<tau> = "{f::ind \<Rightarrow>'a. t f}"
  unfolding t_def by auto

(* The extension of the predicate t is a singleton for large enough types 'a, 
for example taking 'a to be ind\<Rightarrow>bool: *)
lemma t_singl:
  fixes f::"ind\<Rightarrow>(ind\<Rightarrow>bool)"
  shows "t f \<longleftrightarrow> f = (\<lambda>i. (SOME x. True))"
proof -
  { assume "\<forall>x. \<exists>i. f i = x"
    then have "range (Collect \<circ> f) = Pow UNIV"
      unfolding image_def by auto (metis Collect_mem_eq)
    then have False using Cantors_paradox by blast
  }
  thus ?thesis unfolding t_def by auto
qed


(* Hence the newly defined type is also a singleton for that instance: *)

lemma \<tau>_singl: "(x :: (ind\<Rightarrow>bool) \<tau>) = Abs_\<tau> (\<lambda>i. SOME f. True)"
  by (cases x) (auto simp: t_singl)

(* We use the RLCST command to perform the relativization of t: *)
local_setup \<open>RLCST @{term t}\<close>

lemma t_rlt_alt: "neper R \<Longrightarrow> t_rlt R f \<longleftrightarrow> (\<forall>x. R x x \<longrightarrow> (\<exists>i. R (f i) x) \<or> (\<forall>x. R (f x) (SOME a. R a a)))"
  unfolding t_rlt_def by (auto simp: Eps_rlt_True)

(* Now we are ready to show that \<tau> cannot have a relational interpretation 
in such a way that a basic sanity property is satisfied:
the relativized version of the typedef theorem holds. *)

(* Indeed, let us assume that such a relational interpretation rel_\<tau> existed: *)
consts rel_\<tau> :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<tau> \<Rightarrow> 'a \<tau> \<Rightarrow> bool" 
(* ... and satisfied the aforementioned property: *)
axiomatization where
  bij_upto_\<tau>: "\<And>R. neper R \<Longrightarrow> \<exists>f. bij_upto (rel_\<tau> R) (restr (rel_fun (=) R) (t_rlt R)) (f R)"

(* That would yield a contradiction (a proof of False). The proof encodes 
the aforementioned cardinality mismatch argument, after instantiating 'a to ind\<Rightarrow>bool  *)
lemma False
proof -
  define T where "T \<equiv> (\<lambda>_ :: ind. True)"
  define F where "F \<equiv> (\<lambda>_ :: ind. False)"
  define A where "A \<equiv> {T,F}"

  define R where "R \<equiv> perOfSet A" 
  let ?RLT = "restr (rel_fun (=) R) (t_rlt R)"
  have neper[simp]: "neper R"
    unfolding R_def A_def
    by (meson insertI1 neper_def perOfSet_def per_perOfSet)
  from bij_upto_\<tau>[OF neper] obtain f where bij_upto: "bij_upto (rel_\<tau> R) ?RLT (f R)"
    by blast
  note surjE = bij_upto_surjE[where Q = ?RLT, OF bij_upto]

  have [simp]: "(SOME a. a \<in> A) \<in> A"  
  	 by (metis A_def insertI1 someI)

  have 0: "rel_fun (=) R u u' \<longleftrightarrow> (u = u' \<and> (\<forall> i::ind. u i \<in> A))" for u u' 
    unfolding  rel_fun_def R_def perOfSet_def by auto
    
  have 1: "?RLT u u' \<longleftrightarrow> u = u' \<and> (range u = A \<or> u = (\<lambda>i. SOME a. a \<in> A))" for u u'
    unfolding 0 unfolding t_rlt_alt[OF neper] unfolding R_def restr_def perOfSet_def image_def 
    by fastforce

  have disj: "Eps (\<lambda>a. a \<in> A) = T \<or> Eps (\<lambda>a. a \<in> A) = F"
    unfolding A_def by (metis insert_iff singletonD some_in_eq)
  then have "?RLT (\<lambda>_. Eps (\<lambda>a. a \<in> A)) (\<lambda>_. Eps (\<lambda>a. a \<in> A))"
    unfolding restr_def t_rlt_alt[OF neper] unfolding R_def rel_fun_def perOfSet_def by auto
  from surjE[OF this] obtain x where "rel_\<tau> R x x" "f R x = (\<lambda>_. Eps (\<lambda>a. a \<in> A))"
    by (auto simp: 1)

  moreover

  let ?u = "\<lambda>z. if z = Zero_Rep then T else F" 
  from Suc_Rep_not_Zero_Rep have "?RLT ?u ?u"
    unfolding t_rlt_alt[OF neper] unfolding restr_def R_def A_def rel_fun_def perOfSet_def by auto
  from surjE[OF this] obtain y where "rel_\<tau> R y y" "f R y = ?u"
    by (auto simp: 1)

  moreover from disj Suc_Rep_not_Zero_Rep have "?u \<noteq> (\<lambda>_. Eps (\<lambda>a. a \<in> A))"
    by (auto simp: fun_eq_iff T_def F_def)

  ultimately show False
    by (auto simp: eq_onp_def \<tau>_singl[of x] \<tau>_singl[of y])
qed

end
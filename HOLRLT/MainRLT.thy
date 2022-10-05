section \<open>Main HOL\<close>

text \<open>
  Classical Higher-order Logic -- only ``Main'', excluding real and
  complex numbers etc.
\<close>

theory MainRLT
  imports
    Predicate_Compile
    Quickcheck_Narrowing
    Mirabelle
    Extraction
    Nunchaku
    BNF_Greatest_Fixpoint
    Filter
    Conditionally_Complete_Lattices
    Binomial
    GCD
begin

subsection \<open>Namespace cleanup\<close>

hide_const (open)
  czero cinfinite cfinite csum cone ctwo Csum cprod cexp image2 image2p vimage2p Gr Grp collect
  fsts snds setl setr convol pick_middlep fstOp sndOp csquare relImage relInvImage Succ Shift
  shift proj id_bnf

hide_fact (open) id_bnf_def type_definition_id_bnf_UNIV


subsection \<open>Syntax cleanup\<close>

no_notation
  ordLeq2 (infix "<=o" 50) and
  ordLeq3 (infix "\<le>o" 50) and
  ordLess2 (infix "<o" 50) and
  ordIso2 (infix "=o" 50) and
  card_of ("|_|") and
  BNF_Cardinal_Arithmetic.csum (infixr "+c" 65) and
  BNF_Cardinal_Arithmetic.cprod (infixr "*c" 80) and
  BNF_Cardinal_Arithmetic.cexp (infixr "^c" 90) and
  BNF_Def.convol ("\<langle>(_,/ _)\<rangle>")

bundle cardinal_syntax
begin

notation
  ordLeq2 (infix "<=o" 50) and
  ordLeq3 (infix "\<le>o" 50) and
  ordLess2 (infix "<o" 50) and
  ordIso2 (infix "=o" 50) and
  card_of ("|_|") and
  BNF_Cardinal_Arithmetic.csum (infixr "+c" 65) and
  BNF_Cardinal_Arithmetic.cprod (infixr "*c" 80) and
  BNF_Cardinal_Arithmetic.cexp (infixr "^c" 90)

alias cinfinite = BNF_Cardinal_Arithmetic.cinfinite
alias czero = BNF_Cardinal_Arithmetic.czero
alias cone = BNF_Cardinal_Arithmetic.cone
alias ctwo = BNF_Cardinal_Arithmetic.ctwo

end


subsection \<open>Lattice syntax\<close>

bundle lattice_syntax
begin

notation
  bot ("\<bottom>") and
  top ("\<top>") and
  inf  (infixl "\<sqinter>" 70) and
  sup  (infixl "\<squnion>" 65) and
  Inf  ("\<Sqinter> _" [900] 900) and
  Sup  ("\<Squnion> _" [900] 900)

syntax
  "_INF1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Sqinter>_./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sqinter>_\<in>_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Squnion>_./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Squnion>_\<in>_./ _)" [0, 0, 10] 10)

end

bundle no_lattice_syntax
begin

no_notation
  bot ("\<bottom>") and
  top ("\<top>") and
  inf  (infixl "\<sqinter>" 70) and
  sup  (infixl "\<squnion>" 65) and
  Inf  ("\<Sqinter> _" [900] 900) and
  Sup  ("\<Squnion> _" [900] 900)

no_syntax
  "_INF1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Sqinter>_./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sqinter>_\<in>_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Squnion>_./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Squnion>_\<in>_./ _)" [0, 0, 10] 10)

end

unbundle no_lattice_syntax

hide_type (open) rel


(**********************************************)
(* Relativization of the "finite" predicate  *)

lemma finite_aux: "finite = finite" ..
local_setup \<open>RLTHM @{binding finite_rlt_neper_param} @{thm finite_aux}\<close>
thm finite_rlt_neper_param

lemma insert_compr_raw_rlt_simp[simp]: 
"neper R \<Longrightarrow> 
 insert_compr_raw_rlt R a A = {x. R x a \<or> (\<exists>a'. a' \<in> A \<and> R a' x)}"
unfolding insert_compr_raw_rlt_def  
by simp (metis neper_per per_def)

thm bot_set_inst.bot_set_rlt_def[unfolded Set.bot_set_rlt_def]

(* I am using __ to account for . in the original (qualified) name *)
lemma bot_set_inst__bot_set_rlt_def_simp[simp]: 
"neper R \<Longrightarrow> bot_set_inst.bot_set_rlt R = {}" 
unfolding bot_set_inst.bot_set_rlt_def Set.bot_set_rlt_def 
bot_fun_inst.bot_fun_rlt_def bot_bool_inst.bot_bool_rlt_def
Orderings.bot_fun_rlt_def Orderings.bot_bool_rlt_def
by simp 

(* NB: Induction rules are relativized into induction rules: *)
thm finite_induct
local_setup \<open>RLTHM @{binding finite_rlt_induct'} @{thm finite_induct}\<close>
lemmas finite_rlt_induct = 
  finite_rlt_induct'[simped, consumes 3, induct pred: finite_rlt, case_names mp Ins]

thm finite.intros
local_setup \<open>RLTHM @{binding finite_rlt_empty'} @{thm finite.intros(1)}\<close>
local_setup \<open>RLTHM @{binding finite_rlt_insert'} @{thm finite.intros(2)}\<close>
lemmas finite_rlt_empty = finite_rlt_empty'[simped,intro!,simp]
lemmas finite_rlt_insert = finite_rlt_insert'[simped]

thm finite_subset 
local_setup \<open>RLTHM @{binding finite_rlt_subset'} @{thm finite_subset}\<close>
lemmas finite_rlt_subset = finite_rlt_subset'[simped]

lemma finite_imp_finite_rlt: 
assumes R: "neper R" and A: "finite A"
shows "finite_rlt R {x \<in> A. R x x}"
using A proof induct
  case empty
  thus ?case by (simp add: R finite_rlt_empty)
next
  case (insert a A) 
  show ?case proof(cases "R a a")
    case False
    thus ?thesis using insert(3)  
    	by simp (smt (z3) Collect_cong)
  next
    case True
    show ?thesis 
    apply(rule finite_rlt_subset[OF R _ _ _ finite_rlt_insert[OF R True _ insert(3)]])
    using True unfolding rel_set_def 
    by auto (metis R conversepI neper_conversep)+
  qed
qed

thm finite_Un
local_setup \<open>RLTHM @{binding finite_rlt_Un'} @{thm finite_Un}\<close>

lemma finite_rlt_Un: 
"neper R \<Longrightarrow>
rel_set R A A \<Longrightarrow> closed R A \<Longrightarrow> 
rel_set R B B \<Longrightarrow> closed R B \<Longrightarrow> 
finite_rlt R (A \<union> B) \<longleftrightarrow> finite_rlt R A \<and> finite_rlt R B" 
apply(subst finite_rlt_Un'
[unfolded sup_set_inst.sup_set_rlt_def Set.sup_set_rlt_def sup_fun_inst.sup_fun_rlt_def
Lattices.sup_fun_rlt_def sup_bool_inst.sup_bool_rlt_def Boolean_Algebras.sup_bool_rlt_def, simped, 
symmetric])
apply (force,force,force)
apply(rule arg_cong[of _ _ "finite_rlt R"])
apply safe
unfolding closed_def 
	using neper_rel_set_iff apply fastforce 
  apply (meson rel_setD2)
	using neper_rel_set_iff apply fastforce
  apply (meson rel_setD2)
  apply blast
  by blast

thm finite_rlt_Un[no_vars]

declare empty_transfer[simp,intro!] 

lemma finite_rlt_singl: 
"neper R \<Longrightarrow> R a a \<Longrightarrow> finite_rlt R {x. R x a}"
apply(rule finite_rlt_insert[OF _ _ _ finite_rlt_empty, simped]) 
by auto

lemma finite_getRepr_imp_finite_rlt: 
assumes R: "neper R" and fA: "finite {getRepr R a | a.  a \<in> A}" 
and A: "rel_set R A A" and AA: "closed R A"
shows "finite_rlt R A" 
proof-
  define B where "B = {getRepr R a | a.  a \<in> A}"
  show ?thesis using fA[unfolded B_def[symmetric]] using B_def A AA
  proof (induct arbitrary: A)
    case empty
    then show ?case using R by auto 
  next
    case (insert b B)
    define A1 A2 where "A1 = {a \<in> A. getRepr R a = b}"
    and "A2 = {a \<in> A. getRepr R a \<noteq> b}"

    have rA1: "rel_set R A1 A1" and rA2: "rel_set R A2 A2"
    using insert(5) unfolding rel_set_def A1_def A2_def 
      by auto (metis R neper_getRepr_eq)+

    have AA1: "closed R A1" and AA2: "closed R A2"
    using insert(6) unfolding closed_def A1_def A2_def 
    using R neper_getRepr_eq by fastforce+


    have AA12: "A = A1 \<union> A2"
    unfolding A1_def A2_def by auto
    have BA2: "B = {getRepr R a |a. a \<in> A2}"
    using insert(2,4) unfolding A2_def by auto
    have fA2: "finite_rlt R A2" using insert(3)[OF BA2 rA2 AA2] .

    have Rb: "R b b"  
    by (smt (verit, best) R getRepr_neper insert.prems(1) 
       insert.prems(2) insertI1 mem_Collect_eq neper_classes_eq rel_setD2)
    have 0: "{a \<in> A. getRepr R a = b} = {x. R x b}"
    apply auto  
   	 using R getRepr_neper insert.prems(2) neper_rel_set_iff apply fastforce
     apply (smt (verit, del_insts) A1_def Ball_Collect R closed_def getRepr_neper insert.prems(1) 
       insert.prems(3) insertI1 mem_Collect_eq neper_per neper_rel_set_iff per_def rA1)
    by (smt (verit, del_insts) Ball_Collect R getRepr_neper insert.prems(1) insert.prems(2) 
    insertCI mem_Collect_eq neper_getRepr_eq neper_rel_set_iff)
    
    have fA1: "finite_rlt R A1" unfolding A1_def 
    using finite_rlt_singl[OF R Rb] unfolding 0 .
       
    show ?case unfolding AA12 using fA1 fA2 rA1 AA1 rA2 AA2 R  
    	using finite_rlt_Un by blast
  qed
qed 

thm finite_rlt_induct
(* NB: I can't prove that "finite_rlt R A" implies "closed R A" using finite_rlt_induct
because the predicate "closed R" is not neper-parametric. *)

lemma finite_rlt_imp_finite_getRepr: 
assumes R: "neper R" and fA: "finite_rlt R A" and A: "rel_set R A A"
shows "finite {getRepr R a | a.  a \<in> A}"
proof- 
  let ?P = "\<lambda>A. finite {getRepr R a | a.  a \<in> A}"
  have 0: "rel_fun (rel_set R) (=) ?P ?P"
  using A unfolding rel_fun_def  
  by (auto simp: R rel_set_getRepr closed_def)
  show ?thesis proof(induct rule: finite_rlt_induct[OF R 0 A fA]) 
    show "finite {getRepr R a |a. a \<in> {}}" by auto
  next
    fix A xa
    assume 1: "rel_set R A A"
    "R xa xa"
    "finite_rlt R A"
    "finite {getRepr R a |a. a \<in> A}"
    have "{getRepr R a |a. R a xa \<or> (\<exists>a'. a' \<in> A \<and> R a' a)} \<subseteq> 
       insert (getRepr R xa) {getRepr R a |a. a \<in> A}" 
    by auto (metis R neper_getRepr_eq)+
    hence "finite {getRepr R a |a. R a xa \<or> (\<exists>a'. a' \<in> A \<and> R a' a)}" 
    by (simp add: "1"(4) finite_subset)
    thus "finite {getRepr R a |a. a \<in> {xb. R xb xa \<or> (\<exists>a'. a' \<in> A \<and> R a' xb)}}"
    by simp 
  qed
qed

(* It seems that this is the strongest iff characterization of finite_rlt 
that I can reach. I cannot get rid of the "closed" assumption.  *)
lemma finite_rlt_simp[simp]: 
assumes R: "neper R" and A: "rel_set R A A" "closed R A"
shows "finite_rlt R A \<longleftrightarrow> finite {getRepr R a | a.  a \<in> A}"
using R A finite_getRepr_imp_finite_rlt finite_rlt_imp_finite_getRepr by blast

lemma finite_rlt_closure[simp]: 
"neper R \<Longrightarrow> rel_set R A A \<Longrightarrow> finite_rlt R (closure R A) \<longleftrightarrow> finite_rlt R A"
using finite_rlt_neper_param  
by (metis (mono_tags) rel_funE rel_set_closure)

lemma finite_rlt_induct_closure: 
assumes R: "neper R" 
and 1: "rel_fun (rel_set R) (=) \<phi> \<phi>" "rel_set R A A" "finite_rlt R A" 
and \<phi>: "\<phi> {}"
and 2: "\<And>a A. 
   R a a \<Longrightarrow> rel_set R A A \<Longrightarrow> finite_rlt R A \<Longrightarrow> closure R {a} \<inter> closure R A = {} \<Longrightarrow> 
   \<phi> A \<Longrightarrow> \<phi> (closure R {a} \<union> closure R A)"
shows "\<phi> A" 
apply(rule finite_rlt_induct[of R \<phi> A])  
using R 1 \<phi> apply safe 
  subgoal for a A
  using 2[of a A] unfolding closure_def Int_def Un_def  
  by auto (smt (verit, ccfv_SIG) Collect_cong neper_per per_def) .


(* Relativization of UNIV: *)

lemma UNIV_aux: "UNIV = UNIV" ..
local_setup \<open>RLTHM @{binding UNIV_rlt_neper_param'} @{thm UNIV_aux}\<close>
definition "UNIV_rlt \<equiv> top_set_inst.top_set_rlt"

lemmas UNIV_rlt_neper_param = UNIV_rlt_neper_param'[unfolded UNIV_rlt_def[symmetric]]

lemma UNIV_rlt_eq[simp]: "UNIV_rlt (=) = UNIV"
unfolding UNIV_rlt_def rlt_eq ..

lemma UNIV_rlt[simp]: "neper R \<Longrightarrow> UNIV_rlt R = {x. R x x}"
unfolding UNIV_rlt_def by auto

(* *)
lemma finite_rlt_UNIV_rlt2:
"neper (R::'a::finite\<Rightarrow>'a\<Rightarrow>bool) \<Longrightarrow> finite_rlt R (UNIV_rlt R)"  
by force


(* Relativization of the cardinality function *)

(* *)
lemma card_aux: "card = card" ..
local_setup \<open>RLTHM @{binding card_rlt_neper_param} @{thm card_aux}\<close>
thm card_rlt_neper_param

local_setup \<open>RLTHM @{binding card_rlt_empty'} @{thm card.empty}\<close>
lemmas card_rlt_empty = 
  card_rlt_empty'[unfolded rlt_eq bot_set_rlt_def Set.bot_set_rlt_def bot_fun_rlt_def
  Orderings.bot_fun_rlt_def, simped, simp]

local_setup \<open>RLTHM @{binding card_rlt_insert_disjoint'} @{thm card_insert_disjoint}\<close>
lemma card_rlt_insert_disjoint: 
"neper R \<Longrightarrow> R x x \<Longrightarrow> rel_set R A A \<Longrightarrow> finite_rlt R A \<Longrightarrow>
 \<forall>a'. a' \<in> A \<longrightarrow> \<not> R a' x \<Longrightarrow>
 card_rlt R {xa. R xa x \<or> (\<exists>a'. a' \<in> A \<and> R a' xa)} = Suc (card_rlt R A)"
apply(subst card_rlt_insert_disjoint'[unfolded rlt_eq bot_set_rlt_def Set.bot_set_rlt_def bot_fun_rlt_def
  Orderings.bot_fun_rlt_def insert_compr_raw_rlt_def, simped, of R x A, symmetric])
by auto (metis neper_per per_def)

lemma card_rlt_insert: 
"neper R \<Longrightarrow> R x x \<Longrightarrow> rel_set R A A \<Longrightarrow> finite_rlt R A \<Longrightarrow> closed R A \<Longrightarrow> 
 closure R {x} \<inter> A = {} \<Longrightarrow>
 card_rlt R (closure R {x} \<union> A) = Suc (card_rlt R A)"
apply(subst card_rlt_insert_disjoint[symmetric])
apply auto[] apply auto[] apply auto[] apply auto[] apply auto[] 
	apply (simp add: Int_commute closed_def closure_def disjoint_iff)
  apply(rule arg_cong[of _ _ "card_rlt R"])
  unfolding closure_def closed_def apply safe
  apply (meson neper_per per_def)
  apply (meson rel_setD2)
  apply (meson insertI1 neper_def per_def)
  by blast

lemma card_rlt_closure[simp]: 
"neper R \<Longrightarrow> rel_set R A A \<Longrightarrow> card_rlt R (closure R A) = card_rlt R A"
using card_rlt_neper_param  
by (metis (mono_tags) rel_funE rel_set_closure)

lemma card_rlt_simp: 
assumes R: "neper R" and A: "rel_set R A A" "finite_rlt R A" 
shows "card_rlt R A = card {getRepr R a | a. a \<in> A}"
proof-
  let ?\<phi> = "\<lambda>A. card_rlt R A = card {getRepr R a | a. a \<in> A}"
  have 0: "rel_fun (rel_set R) (=) ?\<phi> ?\<phi>"
  unfolding rel_fun_def apply clarify
  subgoal for A B apply(subst rel_set_getRepr[of R B A])  
  	using R apply blast 
  	apply (meson R neper_per per_def per_rel_set)  
  	by (smt (verit, ccfv_threshold) R card_rlt_neper_param empty_iff empty_transfer 
       mem_Collect_eq neper_def rel_fun_def rel_set_closure) .
  show ?thesis 
  proof(induction rule: finite_rlt_induct_closure[OF R 0 A])
  	case 1
  	then show ?case using R by simp
  next
  	case (2 a A)

    have g: "{getRepr R aa |aa. aa \<in> closure R {a} \<or> aa \<in> closure R A} =
          insert (getRepr R a) {getRepr R aa |aa. aa \<in> closure R A}"
    apply auto
    apply (simp add: R closure_def neper_getRepr_eq)+
    using "2.IH"(1) by force
    have gg: "getRepr R a \<notin> {getRepr R aa |aa. aa \<in> closure R A}"
    by auto (smt (verit, best) "2.IH"(1) "2.IH"(4) CollectD Int_Collect assms(1) 
     bex_empty closure_def geterRepr_related inf_sup_aci(1) insertI1 neper_classes_eq)

    have "finite_rlt R (closure R A)" 
    	using "2.IH"(2) "2.IH"(3) R finite_rlt_closure by blast
    hence ggg: "finite {getRepr R aa |aa. aa \<in> closure R A}"
    using 2 R by auto
        
    show ?case using R apply simp 
    apply(subst card_rlt_insert) 
     using 2 apply (auto simp: Int_def)
       subgoal  
       	 using finite_rlt_closure finite_rlt_imp_finite_getRepr rel_set_imp_closure by blast
       subgoal unfolding g card_insert_disjoint[OF ggg gg]  
       	 by (simp add: rel_set_getRepr_closure) .       
  qed
qed

(* *)

corollary card_rlt_UNIV_rlt: 
"finite (UNIV::('a::finite)set) \<Longrightarrow> neper (R::'a\<Rightarrow>'a\<Rightarrow>bool) \<Longrightarrow> 
 card_rlt R (UNIV_rlt R) = card {getRepr R a | a. R a a}" 
using card_rlt_simp[of R "UNIV_rlt R"] by auto

corollary card_rlt_UNIV_rlt_simp[simp]: 
"finite (UNIV::('a::finite)set) \<Longrightarrow> neper (R::'a\<Rightarrow>'a\<Rightarrow>bool) \<Longrightarrow> 
 card_rlt R {x. R x x} = card {getRepr R a | a. R a a}" 
using card_rlt_simp[of R "UNIV_rlt R"] by auto


(* Relativization of some list predicates *)



(* *)
local_setup \<open>RLTHM @{binding list_induct_rlt_neper_param} @{thm list.induct}\<close>
thm list_induct_rlt_neper_param

declare Nil_rlt_param[simp] Cons_rlt_param[simp]
lemmas list_induct_rlt = list_induct_rlt_neper_param[unfolded rrel_alt, simped]

lemma distinct_aux: "distinct = distinct" ..
local_setup \<open>RLTHM @{binding distinct_rlt_neper_param} @{thm distinct_aux}\<close>
thm distinct_rlt_neper_param


local_setup \<open>RLTHM @{binding distinct_rlt_Nil'} @{thm distinct.simps(1)}\<close>
lemmas distinct_rlt_Nil = distinct_rlt_Nil'[simped,simp]

local_setup \<open>RLTHM @{binding distinct_rlt_Cons'} @{thm distinct.simps(2)}\<close>
lemmas distinct_rlt_Cons = distinct_rlt_Cons'[unfolded rrel_alt, simped,simp]

lemma neper_getRepr_eq_imp:
"neper R \<Longrightarrow> R a a \<Longrightarrow> R b b \<Longrightarrow> getRepr R a = getRepr R b \<Longrightarrow> R a b"
	by (metis geterRepr_related neper_def per_def)

lemma neper_getRepr_eq_iff:
"neper R \<Longrightarrow> R a a \<Longrightarrow> R b b \<Longrightarrow> getRepr R a = getRepr R b \<longleftrightarrow> R a b"
	by (metis geterRepr_related neper_def neper_getRepr_eq per_def)

lemma distinct_rlt_simp[simp]: "neper R \<Longrightarrow>
rrel_list R xs xs \<Longrightarrow> distinct_rlt R xs = distinct (map (getRepr R) xs)"
unfolding rrel_alt  apply safe
  subgoal apply(induct xs)
    subgoal by auto
    subgoal for x xs apply (auto simp: list_all2_same neper_getRepr_eq_iff set_rlt_param)
      by (metis neper_per per_def)
    done
  subgoal apply(induct xs)
    subgoal by auto
    subgoal apply (auto simp: list_all2_same neper_getRepr_eq_iff set_rlt_param)
    	by (metis image_iff neper_getRepr_eq) . .
  

lemma distinct_rlt_imp_distinct: 
"neper R \<Longrightarrow> rrel_list R xs xs \<Longrightarrow> distinct_rlt R xs \<Longrightarrow> distinct xs"
by (simp add: distinct_map)


end

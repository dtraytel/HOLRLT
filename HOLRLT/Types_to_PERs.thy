theory Types_to_PERs
  imports String 
  (* "HOLRLT-Eisbach.Eisbach" (* Ato D: I hope this is OK *) *)
  keywords
    "wide_typedef" :: thy_goal_defn
begin

(* PRELIMINARIRES *)

(* Copied from Syntax_Independent_Logic.Prelim *)
ML \<open>
exception TAC of term

val simped = Thm.rule_attribute [] (fn context => fn thm =>
  let
    val ctxt = Context.proof_of context;
    val (thm', ctxt') = yield_singleton (apfst snd oo Variable.import false) thm ctxt;
    val full_goal = Thm.prop_of thm';
    val goal = Goal.prove ctxt' [] [] full_goal (fn {context = ctxt, prems = _} =>
      HEADGOAL (asm_full_simp_tac ctxt THEN' TRY o SUBGOAL (fn (goal, _) => raise (TAC goal))))
      |> K (HOLogic.mk_Trueprop @{term True})
      handle TAC goal => goal;
    val thm = Goal.prove ctxt' [] [] goal (fn {context = ctxt, prems = _} =>
      HEADGOAL (Method.insert_tac ctxt [thm'] THEN' asm_full_simp_tac ctxt))
      |> singleton (Variable.export ctxt' ctxt);
  in thm end)

val _ = Theory.setup
  (Attrib.setup \<^binding>\<open>simped\<close> (pair simped) "simped rule");
\<close>

lemma type_definition_inj: "type_definition Rep Abs (Collect t) \<Longrightarrow> inj Rep" 
unfolding type_definition_def inj_on_def  
	by metis

definition "INV f b = (SOME a. f a = b)"

lemma INV_alt: "INV = inv"
  unfolding INV_def inv_into_def by auto

lemma rel_fun_True: "rel_fun R (=) (\<lambda>_. True) (\<lambda>_. True)"
  by auto

lemma remdups_Cons: 
"remdups ys = x # xs \<Longrightarrow> 
\<exists>ys1 ys2. ys = ys1 @ x # ys2 \<and> 
          (\<forall>i<length ys1. ys1!i \<in> set (drop (Suc i) ys1) \<union> {x} \<union> set ys2) \<and>
          remdups ys2 = xs"  
proof(induct ys arbitrary: x xs rule: measure_induct[of length])
  case (1 ys x xs)
  note ih = 1(1)[rule_format]
  show ?case
  proof(cases ys)
  	case Nil
    hence False using 1(2) by auto
  	then show ?thesis by auto
  next
  	case (Cons y' ys') note ys = Cons
  	show ?thesis proof(cases "y' \<in> set ys'")
  		case True
      hence "remdups ys' = x # xs" using 1(2) unfolding ys by auto
      from ih[OF _ this, unfolded ys] obtain ys1 ys2 where 0: 
      "ys' = ys1 @ x # ys2 \<and> 
      (\<forall>i<length ys1. ys1 ! i \<in> set (drop (Suc i) ys1) \<union> {x} \<union> set ys2) \<and> remdups ys2 = xs" by auto
  		show ?thesis apply(rule exI[of _ "y' # ys1"], rule exI[of _ "ys2"])
      using 0 True unfolding ys using less_Suc_eq_0_disj by auto
  	next
  		case False
      hence r: "y' = x \<and> remdups ys' = xs" using 1(2) unfolding ys by auto
  		show ?thesis apply(rule exI[of _ "[]"], rule exI[of _ "ys'"])
      using r False unfolding ys by auto
  	qed
  qed   
qed

lemma remdups_append: "set xs \<subseteq> set ys \<Longrightarrow> remdups (xs @ ys) = remdups ys"
by (induct xs, auto)

lemma remdups_map_inj_on: "inj_on f (set xs) \<Longrightarrow> remdups (map f xs) = map f (remdups xs)"
  by (induct xs) (auto simp: inj_on_def)


(* PERs, NEPERs, etc. *)

type_synonym 'a rel = "'a \<Rightarrow> 'a \<Rightarrow> bool" 

definition per :: "'a rel \<Rightarrow> bool" where 
  "per r \<equiv> (\<forall>a b. r a b \<longrightarrow> r b a) \<and> (\<forall>a b c. r a b \<and> r b c \<longrightarrow> r a c)"

definition neper :: "'a rel \<Rightarrow> bool" where
  "neper r \<equiv> per r \<and> (\<exists>a. r a a)"

definition perOfPred :: "('a \<Rightarrow> bool) \<Rightarrow> 'a rel" where 
  "perOfPred t \<equiv> \<lambda>a a'. a = a' \<and> t a"

lemma per_perOfPred: "per (perOfPred t)"
  unfolding per_def perOfPred_def by auto

lemma per_rel_fun: "per Rsigma \<Longrightarrow> per Rtau \<Longrightarrow> per (rel_fun Rsigma Rtau)"
  unfolding rel_fun_def per_def by meson

lemma ex_rel_fun: "Rtau y y \<Longrightarrow> \<exists>f. rel_fun Rsigma Rtau f f"
  apply(intro exI[of _ "\<lambda>_ . y"])
  unfolding rel_fun_def by auto

named_theorems neper
named_theorems rrel_eq
named_theorems rrel_alt
named_theorems bij_upto
named_theorems rlt_eq
named_theorems rlt_param
named_theorems rep_eq
named_theorems cond_eq
named_theorems quasidef

lemma neper_rel_fun[neper]: "neper Rsigma \<Longrightarrow> neper Rtau \<Longrightarrow> neper (rel_fun Rsigma Rtau)"
  by (metis ex_rel_fun neper_def per_rel_fun)

declare fun.rel_eq[simp,intro!,rrel_eq]


(* Sometimes more intuitive to build PERs from sets:  *)
definition perOfSet :: "'a set \<Rightarrow> 'a rel" where 
  "perOfSet A \<equiv> \<lambda>a a'. a = a' \<and> a \<in> A"

lemma per_perOfSet: "per (perOfSet A)"
  unfolding per_def perOfSet_def by auto

definition restr :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "restr R P x y = (R x y \<and> P x \<and> P y)"

lemma per_restr: "per R \<Longrightarrow> per (restr R A)"
  unfolding per_def restr_def by blast

lemma restr_eq: "restr (=) = eq_onp"
  unfolding restr_def eq_onp_def by auto

lemma neper_restr: "neper R \<Longrightarrow> (\<exists>x. A x \<and> R x x) \<Longrightarrow> neper (restr R A)"
  by (metis neper_def per_restr restr_def)

lemma per_eq[simp,intro!]: "per (=)" unfolding per_def by auto
lemma neper_eq[simp,intro!,neper]: "neper (=)" 
  by (simp add: neper_def per_def)

lemma neper_per[simp]: "neper R \<Longrightarrow> per R"
  unfolding neper_def by blast

lemma neper_eq_onp[simp]: "\<exists>x. P x \<Longrightarrow> neper (eq_onp P)"
unfolding neper_def per_def eq_onp_def by auto

lemma restr_leq: "restr R P \<le> restr R Q \<Longrightarrow> restr (restr R P) Q = restr R P" 
unfolding restr_def by auto 

(* More reusable infrastructure for NEPERs *)

definition getRepr :: "'a rel \<Rightarrow> 'a \<Rightarrow> 'a" where 
  "getRepr R a \<equiv> SOME a'. a' \<in> {a' . R a a'}"

lemma getRepr_neper: 
"neper R \<Longrightarrow> R a a \<Longrightarrow> R a (getRepr R a)"
	by (simp add: getRepr_def tfl_some)

lemma getRepr_eq[simp]: "getRepr (=) = id"
  unfolding getRepr_def by auto

lemma neper_classes_eq: "neper R \<Longrightarrow> R a b \<Longrightarrow> {a'. R a a'} = {a'. R b a'}"
	by (metis neper_per per_def)

lemma neper_getRepr_eq: "neper R \<Longrightarrow> R a b \<Longrightarrow> getRepr R a = getRepr R b"
unfolding getRepr_def  by (simp add: neper_classes_eq)

lemma getRepr_inject: 
"neper R \<Longrightarrow> R a a \<Longrightarrow> R b b \<Longrightarrow> R (getRepr R a) (getRepr R b) \<Longrightarrow> getRepr R a = getRepr R b"
	by (metis getRepr_neper neper_getRepr_eq)

lemma geterRepr_related: "neper R \<Longrightarrow> R a a \<Longrightarrow> R (getRepr R a) a"
	by (metis getRepr_neper neper_per per_def)

lemma per_inv_imagep: "per R \<Longrightarrow> per (inv_imagep R f)"
  unfolding neper_def per_def inv_imagep_def by blast

lemma neper_inv_imagep: "neper R \<Longrightarrow> R (f a) (f a) \<Longrightarrow> neper (inv_imagep R f)"
  unfolding neper_def per_def inv_imagep_def by blast

lemma rel_set_getRepr: 
"neper R \<Longrightarrow> rel_set R A B \<Longrightarrow> {getRepr R a | a.  a \<in> A} = {getRepr R a | a.  a \<in> B}"
unfolding rel_set_def 
apply auto by (metis neper_getRepr_eq)+

lemma rel_fun_getRepr_eq: 
"neper R \<Longrightarrow> rel_fun R (=) (f \<circ> getRepr R) (f \<circ> getRepr R)"
unfolding rel_fun_def by (simp add: neper_getRepr_eq)

lemma ne_getRepr: "neper R \<Longrightarrow> {getRepr R a |a. R a a} \<noteq> {}"
apply auto using neper_def by blast

lemma neper_rel_set_domain[simp]: "neper R \<Longrightarrow> rel_set R {x. R x x} {x. R x x}"
unfolding rel_set_def using neper_classes_eq by fastforce

lemma ne_rel_set: "\<exists>x. rel_set R x x"
  unfolding rel_set_def by auto

lemma per_rel_set: "per R \<Longrightarrow> per (rel_set R)"
  unfolding per_def rel_set_def by meson

lemma neper_rel_set: "per R \<Longrightarrow> neper (rel_set R)"
  by (simp add: ne_rel_set neper_def per_rel_set)

declare neper_rel_set[simp] neper_rel_fun[simp]

declare rel_set_eq[simp,intro!]

lemma neper_Some: "neper R \<Longrightarrow> R (SOME x. R x x) (SOME x. R x x)"
by (meson neper_def someI_ex)


(* A slightly better behaved getRepr, which avoids bad behavior outside the 
relation's domain *)
definition "getRepr' R \<equiv> \<lambda>a. if R a a then getRepr R a else (SOME a'. R a' a')"

lemma inRel_getRepr': "neper R \<Longrightarrow> R x y \<Longrightarrow> R (getRepr' R x) (getRepr' R y)"
by (metis (no_types, lifting) getRepr'_def geterRepr_related neper_per per_def)

lemma getRepr'_iff_inRel: "neper R \<Longrightarrow> R x x \<Longrightarrow> R y y \<Longrightarrow> R (getRepr' R x) (getRepr' R y) \<longleftrightarrow> R x y"
	by (metis (mono_tags, lifting) getRepr'_def getRepr_neper mem_Collect_eq neper_classes_eq)


(* Picking equiv-classes representatives from a preferred set, if possible: *)
definition "getReprOn A R \<equiv> 
  \<lambda>a. if (\<exists>b. b \<in> A \<and> R a b) then (SOME b. b \<in> A \<and> R a b) else getRepr R a"

lemma getReprOn_in: 
"neper R \<Longrightarrow> b \<in> A \<Longrightarrow> R a b \<Longrightarrow> getReprOn A R a \<in> A \<and> R a (getReprOn A R a)"
by (metis (no_types, lifting) getReprOn_def someI_ex)

lemma getReprOn_in': 
"neper R \<Longrightarrow> \<exists>b \<in> A. R a b \<Longrightarrow> getReprOn A R a \<in> A \<and> R a (getReprOn A R a)"
by (metis (no_types, lifting) getReprOn_def someI_ex)

lemma getReprOn: 
"neper R \<Longrightarrow> R a b \<Longrightarrow> R a (getReprOn A R a)"
by (metis (mono_tags, lifting) CollectD CollectI getReprOn_def 
     getReprOn_in getRepr_neper neper_classes_eq neper_getRepr_eq)

lemma getReprOn_eq[simp]: "a \<in> A \<Longrightarrow> getReprOn A (=) a = a"
  unfolding getReprOn_def by (simp add: some_equality)

lemma neper_getReprOn_eq: 
"neper R \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> R a b \<Longrightarrow> getReprOn A R a = getReprOn A R b"
  unfolding getReprOn_def using neper_classes_eq[of R a b]
  by (auto intro!: Eps_cong)

lemma neper_getReprOn_eq_strong: 
"neper R \<Longrightarrow> R a b \<Longrightarrow> getReprOn A R a = getReprOn A R b"
  unfolding getReprOn_def using neper_classes_eq[of R] neper_getRepr_eq[of R]
  by (intro if_cong Eps_cong) fastforce+

lemma neper_trans: "neper R \<Longrightarrow> R a b \<Longrightarrow> R b c \<Longrightarrow> R a c"
  unfolding neper_def per_def by blast

lemma neper_sym: "neper R \<Longrightarrow> R a b \<Longrightarrow> R b a"
  unfolding neper_def per_def by blast

lemma getReprOn_inject: 
"neper R \<Longrightarrow> a' \<in> A \<Longrightarrow> b' \<in> A \<Longrightarrow> R a a' \<Longrightarrow> R b b' \<Longrightarrow> 
 R (getReprOn A R a) (getReprOn A R b) \<Longrightarrow> getReprOn A R a = getReprOn A R b"
  using neper_classes_eq[of R a b, OF _ neper_trans[of R, OF _ getReprOn[of R _ a' A] neper_sym[of R,
    OF _ neper_trans[of R, OF _ getReprOn[of R _ b' A] neper_sym[of R]]]]]
  by (auto simp: getReprOn_def intro: Eps_cong)

lemma geterReprOn_related: 
"neper R \<Longrightarrow> a' \<in> A \<Longrightarrow> R a a' \<Longrightarrow> R (getReprOn A R a) a"
by (metis getReprOn_in neper_def per_def)

lemma getReprOn_UNIV: "neper R \<Longrightarrow> getReprOn UNIV R = getRepr R"
unfolding getReprOn_def getRepr_def by auto

lemma rel_fun_getReprOn_eq: 
  assumes "neper R"
  shows "rel_fun R (=) (f \<circ> getReprOn A R) (f \<circ> getReprOn A R)"
  by (auto simp: rel_fun_def dest: neper_getReprOn_eq_strong[OF assms, of _ _ A])

(* *)

definition closed where "closed R A \<equiv> \<forall>a\<in>A. \<forall>b. R a b \<longrightarrow> b\<in>A"

lemma closed_emp[simp,intro!]: "closed R {}"
unfolding closed_def by auto

lemma closed_Un: "closed R A \<Longrightarrow> closed R B \<Longrightarrow> closed R (A \<union> B)"
unfolding closed_def by auto

definition closure :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a set" where 
"closure R A \<equiv> {x. \<exists>a. a \<in> A \<and> R a x}"

lemma closure_empty[simp]: "closure R {} = {}"
unfolding closure_def by auto

lemma closed_iff_eq_closure: "rel_set R A A \<Longrightarrow> closed R A \<longleftrightarrow> closure R A = A"
unfolding closed_def closure_def by auto (meson rel_setD2)

lemma closure_Un: "closure R (A \<union> B) = closure R A \<union> closure R B"
unfolding closure_def by auto

lemma closure_ext: "rel_set R A A \<Longrightarrow> A \<subseteq> closure R A"
unfolding rel_set_def closure_def by auto

lemma closure_idem[simp]: "neper R \<Longrightarrow> closure R (closure R A) = closure R A"
unfolding rel_set_def closure_def using neper_classes_eq by fastforce

lemma closure_idem_Un[simp]: 
"neper R \<Longrightarrow> closure R (closure R {a} \<union> closure R A) = closure R {a} \<union> closure R A"
by (simp add: closure_Un)

lemma rel_set_closure: "rel_set R A A \<Longrightarrow> rel_set R A (closure R A)"
unfolding rel_set_def closure_def by blast

lemma rel_set_imp_closure: "neper R \<Longrightarrow> rel_set R A B \<Longrightarrow> rel_set R (closure R A) (closure R B)"
unfolding rel_set_def closure_def  
by simp (metis neper_def per_def)

lemma rel_set_closure_iff[simp]: 
"neper R \<Longrightarrow> rel_set R A A \<Longrightarrow> rel_set R B B \<Longrightarrow> 
 rel_set R (closure R A) (closure R B) \<longleftrightarrow> rel_set R A B"
  by (metis neper_per per_def per_rel_set rel_set_closure)

lemma closed_closure[simp]: "neper R \<Longrightarrow> rel_set R A A \<Longrightarrow> closed R (closure R A)"
  by (auto simp: closed_iff_eq_closure)

lemma rel_set_getRepr_closure: 
"neper R \<Longrightarrow> rel_set R A A \<Longrightarrow> {getRepr R a |a. a \<in> closure R A} = {getRepr R a |a. a \<in> A}"
using rel_set_closure rel_set_getRepr by blast

lemma neper_closed_domain[simp]: "neper R \<Longrightarrow> closed R {x. R x x}"
unfolding closed_def using neper_classes_eq by fastforce

lemma rel_set_closure': "neper R \<Longrightarrow> rel_set R (closure R A) (closure R A)"
unfolding rel_set_def closure_def apply simp  
	by (metis CollectD CollectI neper_classes_eq)

lemma rel_set_closure_eq: "neper R \<Longrightarrow> rel_set R A B \<Longrightarrow> closure R A = closure R B"
unfolding rel_set_def closure_def  
	using neper_classes_eq by fastforce 

lemma eq_closure_iff: "neper R \<Longrightarrow> R a a \<Longrightarrow> R b b \<Longrightarrow> closure R {a} = closure R {b} \<longleftrightarrow> R a b"
unfolding closure_def apply auto
	using neper_classes_eq by fastforce+

lemma rel_set_closure_iff': 
"neper R \<Longrightarrow> R a a \<Longrightarrow> R b b \<Longrightarrow> rel_set R (closure R {a}) (closure R {b}) \<longleftrightarrow> R a b"
unfolding closure_def by (auto simp: rel_set_def dest: neper_sym neper_trans)

lemma rel_set_closure_rel_conj: 
assumes Q: "neper (rel_conj R Q)" and R: "neper R" and r: "rel_conj R Q a a" "rel_conj R Q b b"
and rc: "rel_set R (closure (rel_conj R Q) {a}) (closure (rel_conj R Q) {b})"
shows "rel_conj R Q a b"
using assms 
  unfolding closure_def rel_set_def OO_def apply (auto)
  by (meson neper_trans)

lemma closure_relcompp2: 
"neper Q \<Longrightarrow> neper (restr R (\<lambda>i. Q i i)) \<Longrightarrow> closure (rel_conj Q R) (closure Q A) = closure (Q OO R OO Q) A"
  unfolding closure_def restr_def apply auto  
  using neper_trans apply fastforce
	using neper_classes_eq apply fastforce
  done

lemma closure_singl: "neper R \<Longrightarrow> closure R {xa} = {x. R x xa}"
unfolding closure_def 
by simp (metis CollectD CollectI geterReprOn_related neper_classes_eq)+

lemma quotient_closure: "quotient A {(x, y). Q x y} = {closure Q {a} | a . a \<in> A}" 
unfolding quotient_def closure_def by auto


(* *)

(**************)
(* Used to show that relators preserve neper's: *)

lemma neper_conversep: "neper R \<Longrightarrow> R = conversep R"
	by (metis neper_def per_def symp_conv_conversep_eq symp_def)

lemma neper_relcompp_leq: "neper R \<Longrightarrow> R OO R = R"
  apply (rule antisym)
  apply(metis neper_per per_def transp_def transp_relcompp_less_eq)
	by (metis (mono_tags, lifting) OO_def mem_Collect_eq neper_classes_eq predicate2I)

lemma closure_relcompp: "neper R \<Longrightarrow> neper Q \<Longrightarrow> closure (Q OO R) (closure Q A) = closure (Q OO R) A"
unfolding closure_def apply auto 
	apply (metis neper_relcompp_leq relcomppI)
  by (metis mem_Collect_eq neper_classes_eq relcompp.simps)

lemma relator_pres_neper: 
assumes cm: "\<And>R1 R2. G (R1 OO R2) = G R1 OO G R2"
and cv: "\<And>R. G (conversep R) = conversep (G R)"
and ne: "\<exists>x. G R x x"
and R: "neper R"
shows "neper (G R)"
  using cm[of R R] cv[of R] ne R neper_relcompp_leq[OF R]
  unfolding neper_def per_def conversep_iff relcompp_apply
  by (metis (full_types) R conversep_iff cv neper_conversep)


(* BIJECTIONS UP-TO *)

definition bij_upto :: "'a rel \<Rightarrow> 'b rel \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where 
  "bij_upto P Q f \<equiv> 
   ((\<forall>x x'. P x x' \<longrightarrow> Q (f x) (f x')) \<and>
    (\<forall>x x'. P x x \<and> P x' x' \<longrightarrow> Q (f x) (f x') \<longrightarrow> P x x') \<and>
    (\<forall>y. Q y y \<longleftrightarrow> (\<exists>x. P x x \<and> Q y (f x))))"

(* *)
(* Compared with unfolding the definition, this 
avoids rechecking a redundan bit in the last conjunct *)
lemma bij_uptoI: 
assumes "neper Q"
and "\<And>x x'. P x x' \<Longrightarrow> Q (f x) (f x')" 
and "\<And>x x'. P x x \<Longrightarrow> P x' x' \<Longrightarrow> Q (f x) (f x') \<Longrightarrow> P x x'"
and "\<And>y. Q y y \<Longrightarrow> \<exists>x. P x x \<and> Q y (f x)" 
shows "bij_upto P Q f"
using assms unfolding bij_upto_def by (meson neper_per per_def)

lemma bij_upto_id: "neper P \<Longrightarrow> bij_upto P P id"
apply(rule bij_uptoI) by auto

lemma bij_upto_id': "neper P \<Longrightarrow> P = Q \<Longrightarrow> bij_upto P Q id" using bij_upto_id by auto

lemma bij_upto_rel_fun: "bij_upto P Q f \<Longrightarrow> rel_fun P Q f f"
  unfolding bij_upto_def rel_fun_def by blast

lemma bij_upto_rel_fun': "bij_upto P Q f \<Longrightarrow> Q \<le> Q' \<Longrightarrow> rel_fun P Q' f f"
  unfolding bij_upto_def rel_fun_def by blast

lemma type_copy_bij: "type_definition f g UNIV \<Longrightarrow> bij f"
  by (meson o_bij type_copy_Abs_o_Rep type_copy_Rep_o_Abs)

lemma neper_vimage2p_bij: "bij f \<Longrightarrow> neper R \<Longrightarrow> neper (vimage2p f f R)"
  unfolding neper_def per_def vimage2p_def bij_iff
  by metis

lemma vimage2p_bij_eq: "bij f \<Longrightarrow> R = (=) \<Longrightarrow> vimage2p f f R = (=)"
  unfolding neper_def per_def vimage2p_def bij_iff
  by blast

lemma restr_self: "neper R \<Longrightarrow> restr R (\<lambda>x. \<exists>a. R a a \<and> R a x) = R"
  unfolding restr_def fun_eq_iff neper_def per_def
  by metis

lemma restr_True: "neper R \<Longrightarrow> restr R (\<lambda>x. True) = R"
  unfolding restr_def fun_eq_iff neper_def per_def
  by metis

lemma bij_upto_bij: "bij f \<Longrightarrow> neper R \<Longrightarrow> bij_upto (vimage2p f f R) R f"
  unfolding bij_upto_def vimage2p_def bij_iff neper_def per_def id_apply
  by metis

lemma bij_upto_iff_bij_betw: 
"bij_upto (perOfSet A) (perOfSet B) f \<longleftrightarrow> bij_betw f A B"
unfolding bij_upto_def bij_betw_def inj_on_def perOfSet_def by auto

lemma type_definition_bij_upto:
  assumes "type_definition Rep Abs (Collect A)"
  shows "bij_upto (=) (eq_onp A) Rep"
  by (auto simp: bij_upto_def eq_onp_def
    type_definition.Rep[OF assms, simplified]
    type_definition.Rep_inject[OF assms, simplified]
    elim: type_definition.Rep_cases[OF assms, simplified])

(* General-purpose infrastructure for generating "default" relators for new types *)

lemma bij_upto_restr_inv_imagep:
assumes "neper Q" and "\<And>x. t x \<Longrightarrow> tr (f x) \<and> Q (f x) (f x)" 
and "\<And>y. tr y \<and> Q y y \<Longrightarrow> \<exists>x. t x \<and> Q y (f x)"
shows "bij_upto (restr (inv_imagep (restr Q tr) f) t) (restr Q tr) f"
using assms unfolding bij_upto_def restr_def 
  by simp (metis neper_per per_def) 

lemma bij_upto_inv_imagep:
assumes "{x. R x x} \<subseteq> range Rep" and "bij_upto R Q f" 
shows "bij_upto (inv_imagep R Rep) Q (f o Rep)"
  using assms unfolding bij_upto_def inv_imagep_def image_def apply safe
  subgoal by (metis comp_eq_dest_lhs)
  subgoal by (metis comp_eq_dest_lhs)
  subgoal for y
    apply (drule spec[of _ y])
    apply (drule iffD1, assumption)
    apply (erule exE conjE)+
    apply (drule subsetD)
     apply (erule CollectI)
    apply (erule CollectE bexE)+
    apply hypsubst_thin
    by (metis comp_eq_dest_lhs)
  subgoal by (metis comp_eq_dest_lhs) .

lemma bij_upto_restr_inv_imagep_inj:
assumes c: "Collect t \<subseteq> range Rep"
and "neper Q" "\<And>x. t x \<Longrightarrow> tr (f x) \<and> Q (f x) (f x)" 
and "\<And>y. tr y \<and> Q y y \<Longrightarrow> \<exists>x. t x \<and> Q y (f x)"
shows 
"bij_upto 
   (inv_imagep (restr (inv_imagep (restr Q tr) f) t) Rep)
   (restr Q tr) 
   (f \<circ> Rep)"
apply(rule bij_upto_inv_imagep
  [OF _ bij_upto_restr_inv_imagep[OF assms(2-4), simplified]])
using c unfolding restr_def inv_imagep_def by auto

(* can be used for many wide_typedefs (namely those whose types 
do not have well-behaved relators), to simplify bureaucracy: *)
lemma bij_upto_criterion:
assumes c: "type_definition Rep Abs (Collect t)"
and "neper Q" "\<And>x. t x \<Longrightarrow> tr (f x) \<and> Q (f x) (f x)" 
and "\<And>y. tr y \<and> Q y y \<Longrightarrow> \<exists>x. t x \<and> Q y (f x)"
shows 
"bij_upto 
   (inv_imagep (restr (inv_imagep (restr Q tr) f) t) Rep)
   (restr Q tr) 
   (f \<circ> Rep)"
apply(rule bij_upto_restr_inv_imagep_inj[OF _ assms(2-4)])
using c unfolding type_definition_def image_def by auto metis

lemma neper_criterion:
"type_definition Rep Abs (Collect t) \<Longrightarrow> neper Q \<Longrightarrow> \<exists>x. t x \<Longrightarrow> 
(\<And>x. t x \<Longrightarrow> tr (f x) \<and> Q (f x) (f x)) \<Longrightarrow> 
neper (inv_imagep (restr (inv_imagep (restr Q tr) f) t) Rep)"
apply safe
subgoal for x
apply(rule neper_inv_imagep)
  subgoal apply(rule neper_restr)
    subgoal apply(rule neper_inv_imagep[of _ _ x])
      subgoal apply(rule neper_restr)
        subgoal by simp
        subgoal by auto .
    subgoal unfolding restr_def by auto .
  subgoal apply(rule exI[of _ x])
  unfolding inv_imagep_def restr_def by auto .
  by (simp add: restr_def type_definition_def) .

lemma eq_criterion:  
"type_definition Rep Abs (Collect t) \<Longrightarrow>  (\<And>x. t x \<Longrightarrow> tr x) \<Longrightarrow>
 inv_imagep (restr (inv_imagep (restr (=) tr) id) t) Rep = (=)"
unfolding inv_imagep_def restr_def fun_eq_iff apply auto  
	apply (auto simp add: inj_eq type_definition.Rep_inject)  
	by (meson mem_Collect_eq type_definition.Rep)+

(* The next theorem should be used when we think of the wide-typedef construction on the 
raw type first, and not on the defined type directly
(which is recommended in most cases, to avoid confusion when reasoning about the bijection-up-to)
*)
lemma bij_upto_transportFromRaw:
assumes t: "type_definition Rep Abs (Collect t)" and P': "P' = inv_imagep P Rep"
and b: "bij_upto (restr P t) Q f"
shows "bij_upto P' Q (f o Rep)"
proof-
  have P': "P' = inv_imagep (restr P t) Rep"
  using t unfolding P' restr_def inv_imagep_def fun_eq_iff  
  by (simp add: type_definition_def)
  show ?thesis unfolding P' apply(rule bij_upto_inv_imagep)
  using b t  by auto (metis CollectI restr_def t type_definition.Rep_range)
qed


(* INVERSES UPTO *)

definition "inv_upto R1 R2 f i2 \<equiv> SOME i1. R1 i1 i1 \<and> R2 i2 (f i1)"

lemma inv_upto: "bij_upto R1 R2 f \<Longrightarrow> R2 i2 i2 \<Longrightarrow>
   R1 (inv_upto R1 R2 f i2) (inv_upto R1 R2 f i2) \<and> R2 i2 (f ((inv_upto R1 R2 f i2)))"
unfolding inv_upto_def apply(rule someI_ex[of "\<lambda>i1. R1 i1 i1 \<and> R2 i2 (f i1)"])
unfolding bij_upto_def by blast

lemmas inv_upto_forth = inv_upto[THEN conjunct1]
lemmas inv_upto_back = inv_upto[THEN conjunct2]

lemma inv_upto_bij_upto: 
assumes R1: "neper R1" and R2: "neper R2" and b: "bij_upto R1 R2 f"
defines "g \<equiv> inv_upto R1 R2 f"
shows "bij_upto R2 R1 g"
proof-
  have g: "\<And>i2. R2 i2 i2 \<Longrightarrow> R1 (g i2) (g i2)"  
       "\<And>i2. R2 i2 i2 \<Longrightarrow> R2 i2 (f (g i2))" 
  	by (auto simp add: b g_def inv_upto)
  show ?thesis 
  apply(rule bij_uptoI[OF R1])
    subgoal for x y using b unfolding bij_upto_def
      by (metis (full_types) CollectD CollectI R2 g(1) g(2) neper_classes_eq)
     subgoal using b unfolding bij_upto_def 
     	 by (metis (full_types) R2 g(2) mem_Collect_eq neper_classes_eq)
     subgoal using b unfolding bij_upto_def 
     	 by (meson g(1) g(2)) .
qed

lemma bij_upto_eq_bij: "bij_upto (=) (=) f \<longleftrightarrow> bij f"
unfolding bij_upto_def bij_def inj_def surj_def by auto

lemma inv_upto_eq_inv: "bij f \<longrightarrow> inv_upto (=) (=) f = inv f"
	by (metis (mono_tags) bij_def bij_upto_eq_bij inj_imp_inv_eq inv_upto)

lemma inv_upto_iff_bij_betw: 
"bij_betw f A B \<Longrightarrow> inv_upto (perOfSet A) (perOfSet B) f = inv_into A f"
  unfolding bij_betw_def inj_on_def perOfSet_def inv_upto_def inv_into_def fun_eq_iff
  by auto (metis image_eqI)

lemma inv_upto_eqI: 
assumes R: "R1 = perOfSet A" "R2 = perOfSet A"
and f: "\<forall>a\<in>A. f a = a" "bij_betw f A A"
 and a: "a \<in> A"
shows "inv_upto R1 R2 f a = a"
proof-
  have 0: "R1 a a" using R a unfolding perOfSet_def by auto
  show ?thesis unfolding R
  using inv_upto[OF f(2)[unfolded bij_upto_iff_bij_betw[symmetric] R[symmetric]] 0]
  unfolding R perOfSet_def apply auto
  unfolding perOfSet_def[symmetric] using f(2)  
  unfolding inv_upto_iff_bij_betw[OF f(2)] 
  by (simp add: f(1))
qed


(* RELATIVIZATION OF CHOICE *)

(* The correct version of choice relativisation: *)
definition Eps_rlt :: "'a rel \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a" where 
  "Eps_rlt \<equiv> \<lambda>R. \<lambda>p. if (\<exists>x. R x x \<and> p x) 
  then (SOME x. R x x \<and> p x) 
  else (SOME x. R x x \<and> R \<noteq> (=))"

(* Sanity checks for Eps_rlt: *)

(* 1. Sanity check: proving by hand the relativized version of 
the characteristic theorem: *)
thm someI[no_vars]

lemma someI_rlt: "rel_fun R (=) P P \<Longrightarrow> R x x \<Longrightarrow> P x \<Longrightarrow> P (Eps_rlt R P)"
  unfolding Eps_rlt_def rel_fun_def
  by (subst if_P) (blast | rule someI2_ex)+

(* 2. NEPER-parametricity: *)

lemma neper_param_Eps_rlt: 
  assumes "neper R"
  shows "rel_fun (rel_fun R (=)) R (Eps_rlt R) (Eps_rlt R)"
  unfolding rel_fun_def Eps_rlt_def apply auto
  subgoal for f x g y
    apply (subgoal_tac "(SOME x. R x x \<and> f x) = (SOME x. R x x \<and> g x)")
     apply (metis (no_types, lifting) tfl_some)
    apply (rule Eps_cong; blast)
    done
  by (metis (mono_tags, lifting) assms neper_def someI_ex)

(* 3. Recoverability: *)

lemma Eps_rlt_eq[symmetric, rlt_eq]: "Eps = Eps_rlt (=)"
  unfolding Eps_rlt_def
  apply (rule ext)
  subgoal for p
    apply (cases "\<exists>x. x = x \<and> p x")
    subgoal by auto
    subgoal
      apply auto 
      by presburger . .

lemma Eps_rlt_True: "neper R \<Longrightarrow> Eps_rlt R (\<lambda>_. True) = (SOME a. R a a)"
unfolding Eps_rlt_def by presburger

(* Relativizing indefinitite choice: *)

definition The_rlt :: "'a rel \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a" where 
  "The_rlt \<equiv> \<lambda>R. \<lambda>p. if (\<exists>x. R x x \<and> p x) \<and> 
                        (\<forall>x y. R x x \<and> R y y \<and> p x \<and> p y \<longrightarrow> R x y) 
  then (SOME x. R x x \<and> p x) 
  else if R = (=) then (THE x. p x)
  else (SOME x. R x x)"

(* 1. Sanity check: proving by hand the relativized version of 
the characteristic theorems: *)
thm theI[no_vars]

lemma "neper R \<Longrightarrow> rel_fun R (=) P P \<Longrightarrow> R x x \<Longrightarrow> 
 P x \<Longrightarrow> (\<And>y. P y \<Longrightarrow> R y x) \<Longrightarrow> P (The_rlt R P)"
  unfolding The_rlt_def rel_fun_def
  apply (subst if_P)
   apply (metis neper_sym neper_trans)
  apply (rule someI2_ex)
   apply blast
  apply blast
  done

thm theI_unique[no_vars]

lemma "neper R \<Longrightarrow> rel_fun R (=) P P \<Longrightarrow> R x x \<Longrightarrow>
 (\<And>y. P y \<Longrightarrow> R y x) \<Longrightarrow> P x \<longleftrightarrow> P (The_rlt R P)"
  unfolding The_rlt_def rel_fun_def
  apply (rule iffI)
   apply (subst if_P)
    apply (metis neper_sym neper_trans)
   apply (rule someI2_ex)
    apply blast
   apply blast
  apply blast
  done
	          
(* Parametricity: *)
lemma neper_param_The_rlt: 
  assumes "neper (R::'a rel)"
  shows "rel_fun (rel_fun R (=)) R (The_rlt R) (The_rlt R)"
unfolding rel_fun_def proof safe
  fix p q::"'a\<Rightarrow>bool" assume 0: "\<forall>x y. R x y \<longrightarrow> p x = q y"
  show "R (The_rlt R p) (The_rlt R q)"
  proof(cases "(\<exists>x. R x x \<and> p x) \<and> 
               (\<forall>x y. R x x \<and> R y y \<and> p x \<and> p y \<longrightarrow> R x y)")
    case True
    have *: "(SOME x. R x x \<and> p x) = (SOME x. R x x \<and> q x)"
      by (rule Eps_cong) (auto simp: 0)
    have "R (SOME x. R x x \<and> p x) (SOME x. R x x \<and> q x)"
      unfolding *[symmetric] by (rule someI2_ex) (use True in \<open>blast\<close>)+
    thus ?thesis 
      using True unfolding The_rlt_def if_P[OF True] using 0
      by (subst if_P) blast
  next
    case False note f = False
    show ?thesis 
    proof(cases "R = (=)")
      case True thus ?thesis 
      	using "0" by presburger
    next
      case False 
      have "R (SOME x. R x x) (SOME x. R x x)"
      by (meson assms neper_def some_eq_imp)
    thus ?thesis unfolding The_rlt_def if_not_P[OF f] if_not_P[OF False] 
      using 0 f by (subst if_not_P) blast
    qed
  qed
qed
  
(* 3. Recoverability: *)
lemma The_rlt_eq[symmetric, rlt_eq]: "The = The_rlt (=)"
  unfolding The_rlt_def
  apply (rule ext)
  subgoal for p
  apply (cases "(\<exists>x. x = x \<and> p x) \<and> (\<forall>x y. x = x \<and> y = y \<and> p x \<and> p y \<longrightarrow> x = y)")
    subgoal by (auto simp: someI the_equality)
    subgoal by auto . .
    

(* UNIFORM INFRASTRUCTURE FOR TYPEDEFS *)

definition rep :: "('old \<Rightarrow> bool) \<Rightarrow> 'new \<Rightarrow> 'old" where 
  "rep t \<equiv> SOME Rep. (\<forall>y. t y \<longleftrightarrow> (\<exists>x. y = Rep x)) \<and> 
                         (\<forall>x y. Rep x = Rep y \<longrightarrow> x = y)" 

lemma sanityCheck_abs_rep: 
  fixes Rep :: "'new \<Rightarrow> 'old"
  assumes "type_definition Rep Abs (Collect t)"
  shows "type_definition (rep t ::'new \<Rightarrow> 'old) (INV (rep t)) (Collect t)" (is "type_definition ?r _ _")
proof-
  have 1: "(\<forall>y. t y \<longleftrightarrow> (\<exists>x. y = Rep x)) \<and> (\<forall>x y. Rep x = Rep y \<longrightarrow> x = y)"
    using assms unfolding type_definition_def by simp metis
  have 11: "(\<forall>y. t y \<longleftrightarrow> (\<exists>x. y = ?r x)) \<and> (\<forall>x y. ?r x = ?r y \<longrightarrow> x = y)" 
    unfolding rep_def 
    by (rule someI[of "\<lambda>Rep. (\<forall>y. t y \<longleftrightarrow> (\<exists>x. y = Rep x)) \<and> (\<forall>x y. Rep x = Rep y \<longrightarrow> x = y)"])
      (auto simp: 1)
  moreover
  have 2: "\<forall>a\<in>Collect t. \<exists>b. ?r b = a" using 11 by auto
  then obtain Aabs where 22: "\<forall>a\<in>Collect t. ?r (Aabs a) = a" by metis
  { fix a assume a: "a\<in>Collect t" 
    have "?r (INV ?r a) = a" unfolding INV_def
      by(rule someI[of "\<lambda>b. rep t b = a" "Aabs a"]) (auto simp: bspec[OF 22 a])
  }
  ultimately show ?thesis unfolding type_definition_def by auto
qed

axiomatization where TYPE_singleton: "\<And>x y :: 'a::{} itself. x \<equiv> y"

definition Rep_itself where "Rep_itself (TYPE('a)) = ()"
definition Abs_itself where "Abs_itself (x :: unit) = (TYPE('a))"
lemma type_definition_itself:
  "type_definition Rep_itself Abs_itself {x. True}"
  by standard (auto simp: Abs_itself_def TYPE_singleton)

lemma itself_abs_def:
  assumes "f TYPE('a) \<equiv> (x :: 'b :: {})"
  shows "f \<equiv> (\<lambda>_::'a :: {} itself. x)"
proof -
  from assms have "f i \<equiv> x" for i
    using TYPE_singleton[of "TYPE('a)" i] by simp
  from this[abs_def] show "f \<equiv> (\<lambda>_::'a :: {} itself. x)"
    .
qed


(*NOTE: make sure that there are no typedecls along dependencies*)

ML_file "../Tools/wide_database.ML"
ML_file "../Tools/relativization.ML"
ML_file "../Tools/wide_typedef.ML"
ML_file "../Tools/wide_datatype.ML"

ML \<open>fun RLCST t lthy = Relativization.RLTHM
  (t |> dest_Const |> fst |> Binding.qualified_name |> Binding.prefix_name "refl_" |> Binding.suffix_name "_rlt")
  (infer_instantiate' lthy [SOME (Thm.cterm_of lthy t)] @{thm refl} |> Morphism.thm (Local_Theory.target_morphism lthy))
  lthy
  |> tap (fn (thm, ctxt) => thm |> Thm.pretty_thm ctxt |> @{print}) |> snd\<close>
ML \<open>fun RLTHM b thm lthy = Relativization.RLTHM b thm lthy
  |> tap (fn (thm, ctxt) => thm |> Thm.pretty_thm ctxt |> @{print}) |> snd\<close>


(* SIMPLIFICATION RULES FOR THE RELATIVIZATION OF LOGICAL CONSTANTS *)

local_setup \<open> RLCST @{term "True"} \<close>
local_setup \<open> RLCST @{term "False"} \<close>
local_setup \<open> RLCST @{term "(\<and>)"} \<close>
local_setup \<open> RLCST @{term "(\<or>)"} \<close>
local_setup \<open> RLCST @{term "Not"} \<close>
local_setup \<open> RLCST @{term All} \<close>
local_setup \<open> RLCST @{term Ex} \<close>
local_setup \<open> RLCST @{term Ex1} \<close>

lemmas False_rlt_eq[simp] True_rlt_eq[simp]

(* Relativized connectives and quantifiers behave as expected: *)

lemma All_rlt_simp[simp]:
  "neper R \<Longrightarrow> All_rlt R \<phi> = (\<forall>x. R x x \<longrightarrow> \<phi> x)"
  unfolding All_rlt_def True_rlt_def rel_fun_eq rel_fun_def
    neper_def per_def by metis

lemma Ex_rlt_simp[simp]: 
  "neper R \<Longrightarrow> Ex_rlt R \<phi> = (\<exists>x. R x x \<and> \<phi> x)"
  unfolding Ex_rlt_def True_rlt_def rel_fun_eq rel_fun_def
    neper_def per_def All_rlt_def by metis

lemma and_rlt_simp[simp]: "and_rlt P Q = (P \<and> Q)" 
  unfolding rlt_eq ..

lemma or_rlt_simp[simp]: "or_rlt P Q = (P \<or> Q)"
  unfolding rlt_eq ..

lemma not_rlt_simp[simp]: "not_rlt P = (\<not> P)" 
  by (simp only: not_rlt_def rlt_eq simp_thms)

lemma Ex1_rlt_simp[simp]: 
  assumes "neper R"
  shows "Ex1_rlt R \<phi> = (\<exists>x. R x x \<and> \<phi> x \<and> (\<forall>y. R y y \<and> \<phi> y \<longrightarrow> R y x))"
  unfolding Ex1_rlt_def rel_fun_eq rel_fun_def
    neper_def per_def Ex_rlt_simp[OF assms] and_rlt_simp
    All_rlt_simp[OF assms] by auto

(* REALATIVIZATION OF TYPES *)

(* Products have a wide type definition *)
local_setup \<open> RLCST @{term Pair_Rep} \<close>

(* For simplicity and uniformity, switch from the defining set 
Product_Type.prod to a defining predicate "tprod": *)
definition tprod :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool" where 
  "tprod \<equiv> \<lambda>f. \<exists>a b. f = Pair_Rep a b"

lemma prod_tprod: "Product_Type.prod = Collect tprod"
  unfolding Product_Type.prod_def tprod_def ..

wide_typedef prod rel: "rel_prod" rep: "\<lambda>R1 R2 (a,b). Pair_Rep_rlt R1 R2 a b"
  via type_definition_prod[unfolded prod_tprod]
  subgoal for R1 R2 unfolding neper_def per_def
    apply safe
    subgoal premises prems
      using prems(7)
      by (simp add: prems(3,5)[rule_format])
    subgoal premises prems
      using prems(7,8)
      by (auto intro: prems(4,6)[rule_format, OF conjI])
    subgoal premises prems for a b
      using prems(1,2) by (auto intro: exI[of _ "(a, b)"])
    done
  subgoal unfolding neper_def per_def  
  	by (simp add: prod.rel_eq)
  subgoal for R1 R2
    unfolding bij_upto_def
    apply safe
    subgoal for a b aa bb 
      unfolding rel_fun_def rel_prod.simps Pair_Rep_rlt_def 
        tprod_rlt_def restr_def[abs_def]
      apply auto
           apply (metis neper_def per_def)
          apply (metis neper_def per_def)
         apply (metis neper_def per_def)
        apply (metis neper_def per_def)
       apply (rule exI[of _ a], rule conjI)
        apply (metis neper_def per_def)
       apply (rule exI[of _ b], rule conjI)
        apply (metis neper_def per_def)
       apply (metis neper_def per_def)
      apply (rule exI[of _ a], rule conjI)
       apply (metis neper_def per_def)
      apply (rule exI[of _ b], rule conjI)
       apply (metis neper_def per_def)
      apply (metis neper_def per_def)
      done
    subgoal for a b aa bb 
      unfolding rel_fun_def rel_prod.simps Pair_Rep_rlt_def 
        tprod_rlt_def restr_def[abs_def] by auto
    subgoal for f   
      unfolding rel_fun_def rel_prod.simps Pair_Rep_rlt_def 
        tprod_rlt_def restr_def[abs_def] Ex_rlt_simp 
      apply auto unfolding neper_def per_def apply safe 
      subgoal for x xx a aa
        apply(rule exI[of _ x]) apply safe apply(rule exI[of _ xx])
        by meson .
    subgoal 
      unfolding rel_fun_def rel_prod.simps Pair_Rep_rlt_def 
        tprod_rlt_def restr_def[abs_def] Ex_rlt_simp and_rlt_simp
      unfolding neper_def per_def apply safe
      subgoal by meson
      subgoal by meson
      subgoal by blast
      subgoal by blast . .
  subgoal
    apply (simp add: fun_eq_iff Pair_Rep_rlt_def Rep_prod)
    apply (metis (mono_tags, lifting) Abs_prod_inverse Pair_Rep_def Pair_def Product_Type.prod_def mem_Collect_eq)
    done
  .

(* Sums have a wide type definition *)

(* For simplicity and uniformity, switch from the defining set 
Sum_Type.sum to a defining predicate "t": *)
definition tsum :: "('a \<Rightarrow> 'b \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> bool" where 
  "tsum \<equiv> \<lambda>f. (\<exists>a. f = Inl_Rep a) \<or> (\<exists>b. f = Inr_Rep b)"

lemma sum_tsum: "Sum_Type.sum = Collect tsum"
  unfolding Sum_Type.sum_def tsum_def ..

local_setup \<open> RLCST @{term Inl_Rep} \<close>
local_setup \<open> RLCST @{term Inr_Rep} \<close>

wide_typedef sum rel: "rel_sum" rep: "\<lambda>R1 R2 a_b. case a_b of Inl a \<Rightarrow> Inl_Rep_rlt R1 R2 a 
                                        |Inr b \<Rightarrow> Inr_Rep_rlt R2 R1 b"
  via type_definition_sum[unfolded sum_tsum]
  subgoal for R1 R2 unfolding neper_def per_def
    apply safe
    subgoal premises prems for a b c d
      using prems(7)
      by (cases c; cases d; simp add: prems(3,5)[rule_format])
    subgoal premises prems for a b c d e
      using prems(7,8)
      by (cases c; cases d; cases e; auto intro: prems(4,6)[rule_format, OF conjI])
    subgoal premises prems for a b
      using prems(1) by (auto intro: exI[of _ "Inl a"])
    done
  subgoal unfolding neper_def per_def  
    using sum.rel_eq by blast
  subgoal for R1 R2 unfolding bij_upto_def
    apply safe
    subgoal for a b
      unfolding rel_fun_def rel_prod.simps Inl_Rep_rlt_def Inr_Rep_rlt_def 
        tsum_rlt_def restr_def[abs_def] or_rlt_simp and_rlt_simp
      apply (auto split: sum.splits) 
      by (metis neper_def per_def)+
    subgoal for a b
      unfolding rel_fun_def rel_prod.simps Inl_Rep_rlt_def Inr_Rep_rlt_def 
        tsum_rlt_def restr_def[abs_def] or_rlt_simp and_rlt_simp
      apply (auto split: sum.splits) 
      by (metis neper_def)+
    subgoal for f 
      unfolding rel_fun_def rel_prod.simps Pair_Rep_rlt_def 
        tprod_rlt_def restr_def[abs_def] Ex_rlt_simp 
      apply auto unfolding tsum_rlt_def Inl_Rep_rlt_def 
        Inr_Rep_rlt_def
        and_rlt_simp or_rlt_simp Ex_rlt_simp All_rlt_simp
        rel_fun_def rlt_eq apply safe 
      subgoal for a 
        apply(rule exI[of _ "Inl a"]) apply safe 
      	subgoal by simp
        subgoal by simp
        subgoal by simp
        subgoal by (metis (no_types, lifting) neper_def old.sum.simps(5) per_def) .
      subgoal for b
        apply(rule exI[of _ "Inr b"]) apply safe 
        subgoal by simp 
        subgoal by simp
        subgoal by simp
        subgoal by (metis (no_types, lifting) neper_def old.sum.simps(6) per_def) . .
    subgoal for f 
      unfolding rel_fun_def rel_prod.simps Pair_Rep_rlt_def 
        tprod_rlt_def restr_def[abs_def] Ex_rlt_simp 
      by simp_all (metis (no_types, lifting) neper_def per_def)+ .
  subgoal by (auto simp: fun_eq_iff Inl_Rep_rlt_def Inr_Rep_rlt_def Inl_def Inr_def Abs_sum_inverse Inl_RepI Inr_RepI Inl_Rep_def Inr_Rep_def
        split: sum.splits) .

definition "Rep_set = (\<lambda>X x. x \<in> X)"
lemma type_definition_set: "type_definition Rep_set Collect {P. True}"
  by standard (auto simp: fun_eq_iff Rep_set_def)

(* The PER closure: *)
definition perClassCl where "perClassCl A R a \<equiv> \<exists>a'. A a' \<and> R a' a"

wide_typedef set rel: "rel_set"  rep: "\<lambda>R A. perClassCl (\<lambda>a. a \<in> A) R" via type_definition_set
  subgoal by (meson neper_def neper_rel_set)
  subgoal by simp
  subgoal for R
    subgoal unfolding rel_fun_def rel_set_def perClassCl_def bij_upto_def restr_def 
      apply (simp only: Rep_set_def rlt_eq) apply safe  
      subgoal by (metis neper_def per_def)
      subgoal by (metis neper_def per_def)
      subgoal by (metis neper_def per_def)
      subgoal by metis
      subgoal for f apply(rule exI[of _ "Collect (perClassCl f R)"]) 
        unfolding neper_def per_def perClassCl_def mem_Collect_eq by blast
      subgoal by (metis neper_def per_def)
      subgoal by (metis neper_def per_def) . .
  subgoal
    by (auto simp: perClassCl_def fun_eq_iff Rep_set_def)
  .

local_setup \<open> fn lthy => Relativization.register_quasidef
  \<^const_name>\<open>Set.member\<close>
  ({c=\<^term>\<open>(\<in>)::'a \<Rightarrow> 'a set \<Rightarrow> bool\<close>, rhs=Relativization.Original \<^term>\<open>\<lambda>(x::'a) (X :: 'a set). Rep_set X x\<close>}
  |> Relativization.morph_quasidef (Morphism.term_morphism "polymorphic"
      (singleton (Variable.polymorphic lthy))))
  lthy \<close>

local_setup \<open> fn lthy => Relativization.register_quasidef
  \<^const_name>\<open>Pure.type\<close>
  ({c=\<^term>\<open>undefined :: 'a\<close>, rhs=Relativization.Original \<^term>\<open>SOME x :: 'a. True\<close>}
  |> Relativization.morph_quasidef (Morphism.term_morphism "polymorphic"
      (singleton (Variable.polymorphic lthy))))
  lthy \<close>

local_setup \<open> fn lthy => Relativization.register_quasidef
  \<^const_name>\<open>Pure.type\<close>
  ({c=\<^term>\<open>TYPE('a)\<close>, rhs=Relativization.Original \<^term>\<open>Abs_itself ()\<close>}
  |> Relativization.morph_quasidef (Morphism.term_morphism "polymorphic"
      (singleton (Variable.polymorphic lthy))))
  lthy \<close>

lemma type_definition_unit: "type_definition Rep_unit Abs_unit {x. x}"
  using type_definition_unit
    arg_cong[where f="type_definition Rep_unit Abs_unit" and x = "{x. x}" and y = "{True}"]
  by (auto simp: type_definition_def)

wide_typedef unit rel: "(=) :: unit rel" rep: "\<lambda>_. True" via type_definition_unit
  by (auto simp: neper_def per_def bij_upto_def restr_def fun_eq_iff Rep_unit[simplified])

lemma Nat_nonempty: "\<exists>x. Nat x"
  using Zero_RepI by blast

local_setup \<open> RLCST @{term Nat}\<close>
local_setup \<open> RLCST @{term Ball} \<close>
local_setup \<open> RLCST @{term Bex} \<close>
local_setup \<open> RLCST @{term "(\<subseteq>)"} \<close>
local_setup \<open> RLCST @{term UNIV} \<close>

lemma member_rlt_simp[simp]: 
  "member_rlt R x A \<longleftrightarrow> (\<exists>a'. a' \<in> A \<and> R a' x)" 
  unfolding member_rlt_def Rep_set_rlt_def perClassCl_def by simp

lemma neper_rel_set_iff: 
  "neper R \<Longrightarrow> rel_set R A A \<longleftrightarrow> A \<subseteq> {x. R x x}" 
  unfolding rel_set_def neper_def per_def 
  by (meson Ball_Collect)

lemma less_eq_set_rlt[simp]: 
  "neper R \<Longrightarrow> rel_set R A A \<Longrightarrow> rel_set R B B \<Longrightarrow>
 less_eq_set_rlt R A B \<longleftrightarrow> {x. \<exists>a'\<in>A. R a' x} \<subseteq> {x. \<exists>a'\<in>B. R a' x}"
  unfolding less_eq_set_rlt_def Set.less_eq_set_rlt_def less_eq_fun_rlt_def
    le_fun_rlt_def less_eq_bool_rlt_def le_bool_rlt_def apply (simp add: neper_rel_set_iff)
  by auto (metis neper_def per_def)

lemma Ball_rlt_simp[simp]:
  "neper R \<Longrightarrow> Ball_rlt R A \<phi> = (\<forall>x a. a \<in> A \<and> R a x \<longrightarrow> \<phi> x)"
  unfolding Ball_rlt_def by simp (metis neper_per per_def)

lemma Bex_rlt_simp[simp]:
  "neper R \<Longrightarrow> Bex_rlt R A \<phi> = (\<exists>x a. a \<in> A \<and> R a x \<and> \<phi> x)"
  unfolding Bex_rlt_def by simp (metis neper_per per_def)

axiomatization where Collect_rlt_simp[simp]:
  "Collect_rlt = (\<lambda>R p. {x. R x x \<and> p x})"

lemma top_bool_rlt_simp[simp]:
  "top_bool_rlt = True"
  unfolding top_bool_rlt_def Orderings.top_bool_rlt_def rlt_eq by auto

lemma top_fun_rlt_simp[simp]:
  "top_fun_rlt R S t = (\<lambda>_. t)"
  unfolding top_fun_rlt_def Orderings.top_fun_rlt_def by auto

lemma top_set_rlt_simp[simp]:
  "neper R \<Longrightarrow> top_set_rlt R = {x. R x x}" 
  unfolding top_set_rlt_def Set.top_set_rlt_def 
  by (subst Collect_rlt_simp) simp

wide_typedef nat rel: "(=) :: nat rel" rep: Rep_Nat
  by (auto simp only: restr_eq rlt_eq type_definition_bij_upto[OF type_definition_nat])

lemmas bij_upto_simps[bij_upto] = top_set_rlt_def Set.top_set_rlt_def top_bool_rlt_simp
  Collect_rlt_simp top_fun_rlt_simp member_rlt_simp
  simp_thms mem_Collect_eq rel_fun_True restr_self restr_True

wide_typedef itself rel: "\<lambda>R. (=) :: _ itself rel" rep: "\<lambda>R. Rep_itself" via type_definition_itself
  by (auto simp: type_definition_bij_upto[OF type_definition_itself] restr_eq)

ML \<open>val _ = Theory.setup (BNF_FP_Def_Sugar.fp_sugars_interpretation Wide_Datatype.wide_plugin Wide_Datatype.generate_wide);\<close>

local_setup \<open>RLCST @{term set}\<close>
local_setup \<open>RLCST @{term digit7}\<close>


wide_typedef String.literal rel: "(=) :: String.literal rel" rep: literal.explode
  by (auto simp only: restr_eq rlt_eq rrel_eq type_definition_bij_upto[OF String.type_definition_literal])

local_setup \<open>RLCST @{term intrel}\<close>

wide_typedef int rel: "(=) :: int rel" rep: Rep_int
  by (auto simp only: restr_eq rlt_eq rrel_eq type_definition_bij_upto[OF type_definition_int])

local_setup \<open>RLCST @{term fst}\<close>
local_setup \<open>RLCST @{term inj_on}\<close>
local_setup \<open>RLTHM @{binding the_equality_rlt} @{thm the_equality}\<close>
local_setup \<open>RLTHM @{binding someI2_ex_rlt} @{thm someI2_ex}\<close>

lemma INV_rlt_INV:
  assumes inj_rlt_strong: "\<forall>x y. A x x \<and> B (f_rlt x) (f y) \<longrightarrow> A x y"
    and x_f: "x \<in> range f"
    and "\<forall>a aa. A a a \<and> B (f_rlt a) x_rlt \<and> f aa = x \<longrightarrow> A a aa"
    and surj: "\<exists>x. A x x \<and> B (f_rlt x) x_rlt"
  shows "neper A \<Longrightarrow> neper B \<Longrightarrow>
  rel_fun A B f_rlt f_rlt \<Longrightarrow> B x_rlt x_rlt \<Longrightarrow>
  A (INV_rlt A B f_rlt x_rlt) (INV f x)"
  apply (auto simp: INV_rlt_def INV_def)
  apply (rule someI2_ex_rlt[where Q="\<lambda>x_rlt. A x_rlt (SOME a. f a = x)"])
      apply assumption
     apply (simp add: rel_fun_def)
  using neper_classes_eq apply fastforce
    apply (simp add: rel_fun_def)
    apply (metis (mono_tags, lifting) CollectD CollectI neper_classes_eq)
   apply simp
   apply (metis surj)
  apply (rule someI2_ex[where Q="\<lambda>x. A _ x"])
   apply (metis (mono_tags, lifting) x_f image_iff)
  apply (metis (mono_tags, lifting) assms(3))
  done

lemma Pair_rlt_Pair: "neper R \<Longrightarrow> neper S \<Longrightarrow>
  rel_fun R (rel_fun S (rel_prod R S)) (Pair_rlt R S) Pair"
  unfolding Pair_rlt_def Pair_Rep_rlt_def Abs_prod_rlt_def Rep_prod_rlt_def
    Pair_def Pair_Rep_def Abs_prod_qdef Rep_prod[simplified]
    prod.rep_eq[symmetric]
  apply (intro rel_funI)
  apply simp
  apply (rule INV_rlt_INV[where A="rel_prod R S"])
  subgoal for x y xx yy
    apply (auto simp: rel_fun_def)
    done
  subgoal 
    apply (auto simp: rel_fun_def)
    done
  subgoal 
    apply (auto simp: rel_fun_def)
     apply (metis (mono_tags, lifting) mem_Collect_eq neper_classes_eq)
    apply (metis (mono_tags, lifting) mem_Collect_eq neper_classes_eq)
    done
      apply (simp_all only: neper)
    apply (auto simp: rel_fun_def)
          apply (metis neper_def per_def)
         apply (metis neper_def per_def)
        apply (metis neper_def per_def)
       apply (metis neper_def per_def)
      apply (metis neper_def per_def)
     apply (metis neper_def per_def)
    apply (metis neper_def per_def)
   apply (metis neper_def per_def)
  apply (metis neper_def per_def)
  done

lemma case_prod_rlt_case_prod: "neper R \<Longrightarrow> neper S \<Longrightarrow> neper T \<Longrightarrow>
  rel_fun (rel_fun R (rel_fun S T)) (rel_fun (rel_prod R S) T)
    (case_prod_rlt R S T) case_prod"
  unfolding case_prod_rlt_def fun_eq_iff rel_fun_def
  apply safe
  apply (rule the_equality_rlt[of T])
      apply assumption
     apply (metis neper_def per_def rel_prod_inject)
    apply (auto simp add: rel_fun_def)
  apply (metis neper_def per_def)
    apply (metis neper_def per_def)
  subgoal for x y a b aa ba
    apply (intro exI[of _ a] exI[of _ b] conjI)
       apply (meson neper_per per_def)
      apply (meson neper_per per_def)
     apply (rule prod.rel_flip[THEN iffD1])
     apply (simp add: neper_conversep[symmetric])
     apply (rule Pair_rlt_Pair[THEN rel_funD, THEN rel_funD])
        apply assumption
       apply assumption
      apply (meson neper_per per_def)
     apply (meson neper_per per_def)
    apply (meson neper_per per_def)
    done
  subgoal for x y a b aa bb z aaa bbb
    apply (subgoal_tac "rel_prod R S (a, b) (aaa, bbb)")
    prefer 2
     apply (rule prod.rel_transp[THEN transpD])
    apply (metis neper_def per_def transpI)
       apply (metis neper_def per_def transpI)
    apply assumption
     apply (rule Pair_rlt_Pair[THEN rel_funD, THEN rel_funD])
        apply assumption
       apply assumption
      apply (meson neper_per per_def)
     apply (meson neper_per per_def)
    apply (metis (no_types, lifting) mem_Collect_eq neper_classes_eq rel_prod_inject)
    done
  done

lemma fst_rlt_fst: "neper R \<Longrightarrow> neper S \<Longrightarrow> rel_fun (rel_prod R S) R (fst_rlt R S) fst"
  unfolding fst_rlt_def fst_def
  apply (rule rel_funI)
  apply (rule case_prod_rlt_case_prod[THEN rel_funD, THEN rel_funD, of R S R])
  apply auto
  done

lemma snd_rlt_snd: "neper R \<Longrightarrow> neper S \<Longrightarrow> rel_fun (rel_prod R S) S (snd_rlt R S) snd"
  unfolding snd_rlt_def snd_def
  apply (rule rel_funI)
  apply (rule case_prod_rlt_case_prod[THEN rel_funD, THEN rel_funD, of R S S])
  apply auto
  done

lemma id_rlt_simp[simp]: "id_rlt R = id"
unfolding id_rlt_def by auto 

end 

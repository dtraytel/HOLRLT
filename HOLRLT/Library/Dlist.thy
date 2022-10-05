(* Author: Florian Haftmann, TU Muenchen
   Author: Andreas Lochbihler, ETH Zurich *)

section \<open>Lists with elements distinct as canonical example for datatype invariants\<close>

theory Dlist
imports Confluent_Quotient
begin

subsection \<open>The type of distinct lists\<close>

typedef 'a dlist = "{xs::'a list. distinct xs}"
  morphisms list_of_dlist Abs_dlist
proof
  show "[] \<in> {xs. distinct xs}" by simp
qed

context begin

qualified definition dlist_eq where "dlist_eq = BNF_Def.vimage2p remdups remdups (=)"

qualified lemma equivp_dlist_eq: "equivp dlist_eq"
  unfolding dlist_eq_def by(rule equivp_vimage2p)(rule identity_equivp)

qualified definition abs_dlist :: "'a list \<Rightarrow> 'a dlist" where "abs_dlist = Abs_dlist o remdups"

definition qcr_dlist :: "'a list \<Rightarrow> 'a dlist \<Rightarrow> bool" where "qcr_dlist x y \<longleftrightarrow> y = abs_dlist x"

qualified lemma Quotient_dlist_remdups: "Quotient dlist_eq abs_dlist list_of_dlist qcr_dlist"
  unfolding Quotient_def dlist_eq_def qcr_dlist_def vimage2p_def abs_dlist_def
  by (auto simp add: fun_eq_iff Abs_dlist_inject
    list_of_dlist[simplified] list_of_dlist_inverse distinct_remdups_id)

end

locale Quotient_dlist begin
setup_lifting Dlist.Quotient_dlist_remdups Dlist.equivp_dlist_eq[THEN equivp_reflp2]
end

setup_lifting type_definition_dlist

lemma dlist_eq_iff:
  "dxs = dys \<longleftrightarrow> list_of_dlist dxs = list_of_dlist dys"
  by (simp add: list_of_dlist_inject)

lemma dlist_eqI:
  "list_of_dlist dxs = list_of_dlist dys \<Longrightarrow> dxs = dys"
  by (simp add: dlist_eq_iff)

text \<open>Formal, totalized constructor for \<^typ>\<open>'a dlist\<close>:\<close>

definition Dlist :: "'a list \<Rightarrow> 'a dlist" where
  "Dlist xs = Abs_dlist (remdups xs)"

lemma distinct_list_of_dlist [simp, intro]:
  "distinct (list_of_dlist dxs)"
  using list_of_dlist [of dxs] by simp

lemma list_of_dlist_Dlist [simp]:
  "list_of_dlist (Dlist xs) = remdups xs"
  by (simp add: Dlist_def Abs_dlist_inverse)

lemma remdups_list_of_dlist [simp]:
  "remdups (list_of_dlist dxs) = list_of_dlist dxs"
  by simp

lemma Dlist_list_of_dlist [simp, code abstype]:
  "Dlist (list_of_dlist dxs) = dxs"
  by (simp add: Dlist_def list_of_dlist_inverse distinct_remdups_id)


text \<open>Fundamental operations:\<close>

context
begin

qualified definition empty :: "'a dlist" where
  "empty = Dlist []"

qualified definition insert :: "'a \<Rightarrow> 'a dlist \<Rightarrow> 'a dlist" where
  "insert x dxs = Dlist (List.insert x (list_of_dlist dxs))"

qualified definition remove :: "'a \<Rightarrow> 'a dlist \<Rightarrow> 'a dlist" where
  "remove x dxs = Dlist (remove1 x (list_of_dlist dxs))"

qualified definition map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a dlist \<Rightarrow> 'b dlist" where
  "map f dxs = Dlist (remdups (List.map f (list_of_dlist dxs)))"

qualified definition filter :: "('a \<Rightarrow> bool) \<Rightarrow> 'a dlist \<Rightarrow> 'a dlist" where
  "filter P dxs = Dlist (List.filter P (list_of_dlist dxs))"

qualified definition rotate :: "nat \<Rightarrow> 'a dlist \<Rightarrow> 'a dlist" where
  "rotate n dxs = Dlist (List.rotate n (list_of_dlist dxs))"

end


text \<open>Derived operations:\<close>

context
begin

qualified definition null :: "'a dlist \<Rightarrow> bool" where
  "null dxs = List.null (list_of_dlist dxs)"

qualified definition member :: "'a dlist \<Rightarrow> 'a \<Rightarrow> bool" where
  "member dxs = List.member (list_of_dlist dxs)"

qualified definition length :: "'a dlist \<Rightarrow> nat" where
  "length dxs = List.length (list_of_dlist dxs)"

qualified definition fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a dlist \<Rightarrow> 'b \<Rightarrow> 'b" where
  "fold f dxs = List.fold f (list_of_dlist dxs)"

qualified definition foldr :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a dlist \<Rightarrow> 'b \<Rightarrow> 'b" where
  "foldr f dxs = List.foldr f (list_of_dlist dxs)"

end


subsection \<open>Executable version obeying invariant\<close>

lemma list_of_dlist_empty [simp, code abstract]:
  "list_of_dlist Dlist.empty = []"
  by (simp add: Dlist.empty_def)

lemma list_of_dlist_insert [simp, code abstract]:
  "list_of_dlist (Dlist.insert x dxs) = List.insert x (list_of_dlist dxs)"
  by (simp add: Dlist.insert_def)

lemma list_of_dlist_remove [simp, code abstract]:
  "list_of_dlist (Dlist.remove x dxs) = remove1 x (list_of_dlist dxs)"
  by (simp add: Dlist.remove_def)

lemma list_of_dlist_map [simp, code abstract]:
  "list_of_dlist (Dlist.map f dxs) = remdups (List.map f (list_of_dlist dxs))"
  by (simp add: Dlist.map_def)

lemma list_of_dlist_filter [simp, code abstract]:
  "list_of_dlist (Dlist.filter P dxs) = List.filter P (list_of_dlist dxs)"
  by (simp add: Dlist.filter_def)

lemma list_of_dlist_rotate [simp, code abstract]:
  "list_of_dlist (Dlist.rotate n dxs) = List.rotate n (list_of_dlist dxs)"
  by (simp add: Dlist.rotate_def)


text \<open>Explicit executable conversion\<close>

definition dlist_of_list [simp]:
  "dlist_of_list = Dlist"

lemma [code abstract]:
  "list_of_dlist (dlist_of_list xs) = remdups xs"
  by simp


text \<open>Equality\<close>

instantiation dlist :: (equal) equal
begin

definition "HOL.equal dxs dys \<longleftrightarrow> HOL.equal (list_of_dlist dxs) (list_of_dlist dys)"

instance
  by standard (simp add: equal_dlist_def equal list_of_dlist_inject)

end

declare equal_dlist_def [code]

lemma [code nbe]: "HOL.equal (dxs :: 'a::equal dlist) dxs \<longleftrightarrow> True"
  by (fact equal_refl)


subsection \<open>Induction principle and case distinction\<close>

lemma dlist_induct [case_names empty insert, induct type: dlist]:
  assumes empty: "P Dlist.empty"
  assumes insrt: "\<And>x dxs. \<not> Dlist.member dxs x \<Longrightarrow> P dxs \<Longrightarrow> P (Dlist.insert x dxs)"
  shows "P dxs"
proof (cases dxs)
  case (Abs_dlist xs)
  then have "distinct xs" and dxs: "dxs = Dlist xs"
    by (simp_all add: Dlist_def distinct_remdups_id)
  from \<open>distinct xs\<close> have "P (Dlist xs)"
  proof (induct xs)
    case Nil from empty show ?case by (simp add: Dlist.empty_def)
  next
    case (Cons x xs)
    then have "\<not> Dlist.member (Dlist xs) x" and "P (Dlist xs)"
      by (simp_all add: Dlist.member_def List.member_def)
    with insrt have "P (Dlist.insert x (Dlist xs))" .
    with Cons show ?case by (simp add: Dlist.insert_def distinct_remdups_id)
  qed
  with dxs show "P dxs" by simp
qed

lemma dlist_case [cases type: dlist]:
  obtains (empty) "dxs = Dlist.empty"
    | (insert) x dys where "\<not> Dlist.member dys x" and "dxs = Dlist.insert x dys"
proof (cases dxs)
  case (Abs_dlist xs)
  then have dxs: "dxs = Dlist xs" and distinct: "distinct xs"
    by (simp_all add: Dlist_def distinct_remdups_id)
  show thesis
  proof (cases xs)
    case Nil with dxs
    have "dxs = Dlist.empty" by (simp add: Dlist.empty_def)
    with empty show ?thesis .
  next
    case (Cons x xs)
    with dxs distinct have "\<not> Dlist.member (Dlist xs) x"
      and "dxs = Dlist.insert x (Dlist xs)"
      by (simp_all add: Dlist.member_def List.member_def Dlist.insert_def distinct_remdups_id)
    with insert show ?thesis .
  qed
qed


subsection \<open>Functorial structure\<close>

functor map: map
  by (simp_all add: remdups_map_remdups fun_eq_iff dlist_eq_iff)


subsection \<open>Quickcheck generators\<close>

quickcheck_generator dlist predicate: distinct constructors: Dlist.empty, Dlist.insert

subsection \<open>BNF instance\<close>

context begin

qualified inductive double :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "double (xs @ ys) (xs @ x # ys)" if "x \<in> set ys"

qualified lemma strong_confluentp_double: "strong_confluentp double"
proof
  fix xs ys zs :: "'a list"
  assume ys: "double xs ys" and zs: "double xs zs"
  consider (left) as y bs z cs where "xs = as @ bs @ cs" "ys = as @ y # bs @ cs" "zs = as @ bs @ z # cs" "y \<in> set (bs @ cs)" "z \<in> set cs"
    | (right) as y bs z cs where "xs = as @ bs @ cs" "ys = as @ bs @ y # cs" "zs = as @ z # bs @ cs" "y \<in> set cs" "z \<in> set (bs @ cs)"
  proof -
    show thesis using ys zs
      by(clarsimp simp add: double.simps append_eq_append_conv2)(auto intro: that)
  qed
  then show "\<exists>us. double\<^sup>*\<^sup>* ys us \<and> double\<^sup>=\<^sup>= zs us"
  proof cases
    case left
    let ?us = "as @ y # bs @ z # cs"
    have "double ys ?us" "double zs ?us" using left
      by(auto 4 4 simp add: double.simps)(metis append_Cons append_assoc)+
    then show ?thesis by blast
  next
    case right
    let ?us = "as @ z # bs @ y # cs"
    have "double ys ?us" "double zs ?us" using right
      by(auto 4 4 simp add: double.simps)(metis append_Cons append_assoc)+
    then show ?thesis by blast
  qed
qed

qualified lemma double_Cons1 [simp]: "double xs (x # xs)" if "x \<in> set xs"
  using double.intros[of x xs "[]"] that by simp

qualified lemma double_Cons_same [simp]: "double xs ys \<Longrightarrow> double (x # xs) (x # ys)"
  by(auto simp add: double.simps Cons_eq_append_conv)

qualified lemma doubles_Cons_same: "double\<^sup>*\<^sup>* xs ys \<Longrightarrow> double\<^sup>*\<^sup>* (x # xs) (x # ys)"
  by(induction rule: rtranclp_induct)(auto intro: rtranclp.rtrancl_into_rtrancl)

qualified lemma remdups_into_doubles: "double\<^sup>*\<^sup>* (remdups xs) xs"
  by(induction xs)(auto intro: doubles_Cons_same rtranclp.rtrancl_into_rtrancl)

qualified lemma dlist_eq_into_doubles: "Dlist.dlist_eq \<le> equivclp double"
  by(auto 4 4 simp add: Dlist.dlist_eq_def vimage2p_def
     intro: equivclp_trans converse_rtranclp_into_equivclp rtranclp_into_equivclp remdups_into_doubles)

qualified lemma factor_double_map: "double (map f xs) ys \<Longrightarrow> \<exists>zs. Dlist.dlist_eq xs zs \<and> ys = map f zs \<and> set zs \<subseteq> set xs"
  by(auto simp add: double.simps Dlist.dlist_eq_def vimage2p_def map_eq_append_conv)
    (metis (no_types, opaque_lifting) list.simps(9) map_append remdups.simps(2) remdups_append2 set_append set_eq_subset set_remdups)

qualified lemma dlist_eq_set_eq: "Dlist.dlist_eq xs ys \<Longrightarrow> set xs = set ys"
  by(simp add: Dlist.dlist_eq_def vimage2p_def)(metis set_remdups)

qualified lemma dlist_eq_map_respect: "Dlist.dlist_eq xs ys \<Longrightarrow> Dlist.dlist_eq (map f xs) (map f ys)"
  by(clarsimp simp add: Dlist.dlist_eq_def vimage2p_def)(metis remdups_map_remdups)

qualified lemma confluent_quotient_dlist:
  "confluent_quotient double Dlist.dlist_eq Dlist.dlist_eq Dlist.dlist_eq Dlist.dlist_eq Dlist.dlist_eq
     (map fst) (map snd) (map fst) (map snd) list_all2 list_all2 list_all2 set set"
  by(unfold_locales)(auto intro: strong_confluentp_imp_confluentp strong_confluentp_double
    dest: factor_double_map dlist_eq_into_doubles[THEN predicate2D] dlist_eq_set_eq
    simp add: list.in_rel list.rel_compp dlist_eq_map_respect Dlist.equivp_dlist_eq equivp_imp_transp)

lifting_update dlist.lifting
lifting_forget dlist.lifting

end

context begin
interpretation Quotient_dlist: Quotient_dlist .

lift_bnf (plugins del: code) 'a dlist
  subgoal for A B by(rule confluent_quotient.subdistributivity[OF Dlist.confluent_quotient_dlist])
  subgoal by(force dest: Dlist.dlist_eq_set_eq intro: equivp_reflp[OF Dlist.equivp_dlist_eq])
  done

qualified lemma list_of_dlist_transfer[transfer_rule]:
  "bi_unique R \<Longrightarrow> (rel_fun (Quotient_dlist.pcr_dlist R) (list_all2 R)) remdups list_of_dlist"
  unfolding rel_fun_def Quotient_dlist.pcr_dlist_def qcr_dlist_def Dlist.abs_dlist_def
  by (auto simp: Abs_dlist_inverse intro!: remdups_transfer[THEN rel_funD])

lemma list_of_dlist_map_dlist[simp]:
  "list_of_dlist (map_dlist f xs) = remdups (map f (list_of_dlist xs))"
  by transfer (auto simp: remdups_map_remdups)

end


(*******************)
(* the dlist type-definition is wide *)

abbreviation "dlist_all2 \<equiv> \<lambda>R. Dlist.dlist_eq OO list_all2 R OO Dlist.dlist_eq"

lemmas Dlist_dlist_eq_def = Dlist.dlist_eq_def[unfolded BNF_Def.vimage2p_def fun_eq_iff, rule_format]

lemma dlist_all2: 
"dlist_all2 R xs ys \<longleftrightarrow> 
  (\<exists>xs' ys'. remdups xs' = remdups xs \<and> remdups ys' = remdups ys \<and> list_all2 R xs' ys')"
unfolding OO_def Dlist_dlist_eq_def by metis

lemma rel_dlist_alt: "rel_dlist R = BNF_Def.vimage2p list_of_dlist list_of_dlist (dlist_all2 R)"
  unfolding rel_dlist_def
  apply (auto simp: fun_eq_iff vimage2p_def Dlist.dlist_eq_def relcompp_apply)
  subgoal for dxs dys xs ys
    apply (auto simp: list.rel_map rel_sum.simps elim!: list.rel_mono_strong intro!: exI[of _ "map (\<lambda>x. case x of Inr r \<Rightarrow> r) xs"]
      exI[of _ "map (\<lambda>x. case x of Inr r \<Rightarrow> r) ys"])
    apply (metis case_sum_o_inj(2) map_ident map_map remdups_list_of_dlist remdups_map_remdups)
    apply (metis Inl_Inr_False ex_map_conv set_remdups)
    apply (metis case_sum_o_inj(2) map_ident map_map remdups_list_of_dlist remdups_map_remdups)
    done
  subgoal for dxs dys xs ys
    apply (auto simp: list.rel_map remdups_map_inj_on intro!: exI[of _ "map Inr xs"]
      exI[of _ "map Inr ys"])
    done
  done

lemma rel_dlist_alt2: "rel_dlist R = inv_imagep (dlist_all2 R) list_of_dlist"
unfolding rel_dlist_alt BNF_Def.vimage2p_def inv_imagep_def ..

(* *)

definition gg where "gg R xs \<equiv> remdups (map (getRepr R) xs)"

(* *)

lemma neper_restr_rrel_list_distinct_rlt: 
"neper R \<Longrightarrow> neper (restr (rrel_list R) (distinct_rlt R))"
  apply(rule neper_restr)
    subgoal using list.rrel_neper by fastforce
    subgoal apply(rule exI[of _ "[]"]) unfolding rrel_alt 
    by auto .

lemma gg_forward: 
assumes R: "neper R" and r: "restr (dlist_all2 R) distinct xs ys"
shows "restr (rrel_list R) (distinct_rlt R) (gg R xs) (gg R ys)"
proof-
  from r obtain xs' ys' where xys': "list_all2 R xs' ys'"
  and xs: "xs = remdups xs'" and ys: "ys = remdups ys'"
  unfolding restr_def dlist_all2 by (auto simp: distinct_remdups_id) 
  hence l: "length xs' = length ys'"  
  	using list_all2_iff by blast

  have 0: "set xs' \<subseteq> {x. R x x}" "set ys' \<subseteq> {x. R x x}"
  using xys' 
  by auto (metis assms in_set_conv_nth list_all2_conv_all_nth neper_per per_def)+

  show ?thesis
  unfolding restr_def proof safe
    have 1: "remdups (map (getRepr R) (remdups xs')) = 
             remdups (map (getRepr R) (remdups ys'))"
    using l xys'
    proof(induct xs' ys' rule: list_induct2)
    	case Nil
    	then show ?case by auto
    next
    	case (Cons x xs y ys)
    	then show ?case apply auto 
    		apply (metis assms image_eqI list.set_map neper_getRepr_eq set_remdups)
        apply (metis (mono_tags, lifting) assms imageI image_set neper_getRepr_eq set_remdups)
        by (meson assms neper_getRepr_eq)
    qed
    show "rrel_list R (gg R xs) (gg R ys)" 
    unfolding rrel_alt gg_def unfolding xs ys 
    unfolding 1[symmetric] unfolding list_all2_same 
    using R 0(1)  
    by simp (metis (mono_tags, lifting) CollectD geterRepr_related in_mono neper_def per_def)

    hence 2: "rrel_list R (gg R xs) (gg R xs)" "rrel_list R (gg R ys) (gg R ys)" 
    by (auto simp: "1" gg_def xs ys)
  
    show "distinct_rlt R (gg R xs)" 
    unfolding distinct_rlt_simp[OF R 2(1)] unfolding distinct_map proof safe
      show "distinct (gg R xs)"
      unfolding gg_def by auto
    next
      show "inj_on (getRepr R) (set (gg R xs))"
      unfolding inj_on_def gg_def
      by simp (metis "0"(1) CollectD assms geterRepr_related neper_getRepr_eq 
        set_remdups subset_code(1) xs)
    qed

    show "distinct_rlt R (gg R ys)" 
    unfolding distinct_rlt_simp[OF R 2(2)] unfolding distinct_map proof safe
      show "distinct (gg R ys)"
      unfolding gg_def by auto
    next
      show "inj_on (getRepr R) (set (gg R ys))"
      unfolding inj_on_def gg_def
      by simp (metis "0"(2) CollectD assms geterRepr_related neper_getRepr_eq 
        set_remdups subset_code(1) ys)
    qed
  qed
qed

lemma gg_backward: 
assumes R: "neper R" 
and xs: "restr (dlist_all2 R) distinct xs xs"
and ys: "restr (dlist_all2 R) distinct ys ys"
and 0: "restr (rrel_list R) (distinct_rlt R) (gg R xs) (gg R ys)"
shows "restr (dlist_all2 R) distinct xs ys"
proof-
  from xs ys 0
  have xys: "distinct xs" "distinct ys" "set xs \<subseteq> {x. R x x}" "set ys \<subseteq> {x. R x x}"
  and gxys: "list_all2 R (gg R xs) (gg R ys)" "distinct_rlt R (gg R xs)" "distinct_rlt R (gg R ys)" 
  using R unfolding restr_def dlist_all2 rrel_alt 
  by auto (metis in_set_conv_nth list.rrel_neper 
      list_all2_nthD2 mem_Collect_eq neper_classes_eq rrel_alt set_remdups)+
  have gxys: "gg R xs = gg R ys" using gxys(1) unfolding gg_def
  unfolding list_eq_iff_nth_eq list_all2_conv_all_nth apply auto
  by (smt (verit, ccfv_threshold) CollectD assms getRepr_inject image_iff image_set 
    in_mono nth_mem set_remdups xys(3) xys(4))

  show ?thesis
  unfolding restr_def proof safe
    show "distinct xs" by fact
    show "distinct ys" by fact
    have "\<exists>xs' ys'. remdups xs' = xs \<and> remdups ys' = ys \<and> list_all2 R xs' ys'"
    using xys gxys(1) unfolding gg_def

    proof(induction "(xs,ys)" arbitrary: xs ys 
     rule: measure_induct[of "\<lambda>(xs,ys). length xs + length ys"])
    	case (1 xss ys)
      note ih = 1(1)[simplified, rule_format]
    	show ?case proof(cases xss)
        case Nil show ?thesis 
        using "1.prems"(5) Nil by fastforce  
      next 
        case (Cons x xs) note xss = Cons
        show ?thesis proof(cases "getRepr R x \<in> getRepr R ` set xs")
        case True note x = True
        then obtain x' where x': "x' \<in> set xs" "R x x'" 
        using 1(4) unfolding xss using R neper_getRepr_eq_imp by fastforce
        
        have 0: "remdups (map (getRepr R) xs) = remdups (map (getRepr R) ys)"
        using "1.prems"(5) x unfolding xss by simp

        have "\<exists>xs'. remdups xs' = xs \<and> (\<exists>ys'. remdups ys' = ys \<and> list_all2 R xs' ys')"
        apply(rule ih[of xs ys]) using 1(2-6) 0 unfolding xss by auto
        then obtain xs' ys' where 
        2: "remdups xs' = xs" "remdups ys' = ys" "list_all2 R xs' ys'" by auto
        hence "rel_set R (set xs') (set ys')"  
        using list.set_transfer unfolding rel_fun_def by auto
        note 2 = 2 this

        obtain x' where x': "x' \<in> set xs'" "R x x'"  
        	using "2"(1) x'(1) x'(2) by auto 
        then obtain x'' where x'': "x'' \<in> set ys' \<and> R x' x''" 
        by (meson "2"(4) rel_setD1) 
        have x'': "x'' \<in> set ys'" "R x x''"         
        by (metis assms neper_per per_def x'' x'(2))+

        show ?thesis  
        apply(rule exI[of _ "x # xs'"]) apply(rule exI[of _ "x'' # ys'"]) 
        using 2 "1.prems"(1) x'' unfolding xss by auto
      next
        case False note x = False
        have 0: "getRepr R x # remdups (map (getRepr R) xs) = remdups (map (getRepr R) ys)"
        using "1.prems"(5) x unfolding xss by simp
        obtain zs1 zs2 where ys: "map (getRepr R) ys = zs1 @ getRepr R x # zs2" and 
        zs: "\<forall>i<length zs1. 
           zs1!i \<in> set (drop (Suc i) zs1) \<union> {getRepr R x} \<union> set zs2"
        and "remdups (map (getRepr R) xs) = remdups zs2"
        using remdups_Cons[OF 0[symmetric]] by metis

        from ys obtain ys1 y ys2 where ys: "ys = ys1 @ y # ys2" and 
        "zs1 = map (getRepr R) ys1" and 
        y: "getRepr R y = getRepr R x" and 
        "zs2 = map (getRepr R) ys2"  
        	by (smt (verit, ccfv_threshold) map_eq_Cons_D map_eq_append_conv)

        hence ys1: "\<forall>i<length ys1.  
           getRepr R (ys1!i) \<in> getRepr R ` set (drop (Suc i) ys1) \<union> {getRepr R x} \<union> getRepr R ` set ys2"
        and ys2: "remdups (map (getRepr R) xs) = remdups (map (getRepr R) ys2)"
        using zs by (auto simp add: drop_map  
         \<open>remdups (map (getRepr R) xs) = remdups zs2\<close> \<open>zs2 = map (getRepr R) ys2\<close>)

        have Rxy: "R x y" 
        	using "1"(4) "1"(5) assms neper_getRepr_eq_imp xss y ys by fastforce

        have "\<exists>xs'. remdups xs' = xs \<and> (\<exists>ys'. remdups ys' = ys2 \<and> list_all2 R xs' ys')" 
        apply(rule ih[OF _ _ _ _ _ ys2])
          using 1(2-6) 0 unfolding xss using ys by auto
        then obtain xs' ys' where 2: "remdups xs' = xs" "remdups ys' = ys2" "list_all2 R xs' ys'"
        by auto
        hence "rel_set R (set xs') (set ys')" 
        	by (meson list.set_transfer rel_fun_def)
        note 2 = 2 this

        
        have ii: "\<forall>i<length ys1. getRepr R (ys1!i) \<in> getRepr R ` set (drop (Suc i) ys1) \<union> 
                {getRepr R x} \<union> getRepr R ` set xs'"
        using zs 2(4) unfolding rel_set_def
        by (metis "2"(1) image_set set_remdups ys1 ys2)

        have qq: "set xs' \<union> set ys1 \<subseteq> {x . R x x}" apply auto
        apply (metis "2"(4) assms neper_per per_def rel_set_def)
        using "1"(5) ys by force

        {fix i assume i: "i<length ys1"
         have Ri: "R (ys1!i) (ys1!i)"  
         	 using all_set_conv_all_nth i qq by fastforce
         have "getRepr R (ys1!i) \<in> {getRepr R x} \<union> getRepr R ` set xs'" 
         using i apply(induct "length ys1-Suc i" arbitrary: i) 
           subgoal for i using ii by auto
           subgoal for j i  
           by simp (metis "0" "2"(1) UnCI imageI image_set insert_iff list.simps(15) 
             nth_mem set_append set_remdups ys) . 
         then obtain u where u: "u \<in> insert x (set xs')" 
         and "getRepr R (ys1!i) = getRepr R u" by blast
         hence "R u (ys1!i)"  
         	 by (metis (no_types, lifting) "1.prems"(3) "2"(1) CollectD Ri assms list.simps(15) 
              neper_getRepr_eq_imp set_remdups subsetD xss)
         hence "\<exists>u. u \<in> insert x (set xs') \<and> R u (ys1!i)" using u by auto
        }
        then obtain uu where uu: "\<forall>i<length ys1. uu i \<in> insert x (set xs') \<and> R (uu i) (ys1!i)" 
         by metis
        define us where "us = map uu [0..<length ys1]"
        have us: "set us \<subseteq> insert x (set xs')" "list_all2 R us ys1"
        using uu unfolding us_def  
        by (auto simp add: list_all2_conv_all_nth)
        
        show ?thesis 
        apply(rule exI[of _ "us @ x # xs'"]) apply(rule exI[of _ "ys1 @ y # ys'"]) 
        apply safe 
          subgoal using "2"(1) x xss us(1)  
          	by auto (metis list.simps(15) remdups.simps(2) remdups_append rev_image_eqI)
          subgoal unfolding ys 
          by (metis "1.prems"(2) "2"(2) append_Cons remdups_append2 remdups_id_iff_distinct 
             self_append_conv2 ys)
          subgoal using us(2) by (simp add: "2"(3) Rxy list_all2_appendI) . 
        qed 
      qed
    qed
    thus "dlist_all2 R xs ys" unfolding dlist_all2 by (metis remdups_remdups)
  qed
qed

lemma gg_surj_upto: 
assumes R: "neper R"  
and r: "restr (rrel_list R) (distinct_rlt R) ys ys"
shows "\<exists>xs. restr (dlist_all2 R) distinct xs xs \<and> 
             restr (rrel_list R) (distinct_rlt R) ys (gg R xs)" 
proof-
  from r have yys: "rrel_list R ys ys" and ys: "distinct (map (getRepr R) ys) "  
   using R unfolding restr_def by auto
  hence ys2: "list_all2 R ys ys" "set ys \<subseteq> {x. R x x}" unfolding rrel_alt  
  	by (auto simp: list_all2_same subsetI)
  show ?thesis 
  proof(rule exI[of _ ys], unfold restr_def, safe)
    show dys: "distinct ys" "distinct ys" using ys distinct_map by blast+
    
    show "dlist_all2 R ys ys" using ys2(1) unfolding dlist_all2 by auto

    show "rrel_list R ys (gg R ys)" 
    unfolding gg_def rrel_alt 
    unfolding ys[unfolded remdups_id_iff_distinct[symmetric]]
    using ys2(2) unfolding list_all2_conv_all_nth 
    by (simp add: assms getRepr_neper list_all2_nthD ys2(1))

    hence 1: "rrel_list R (gg R ys) (gg R ys)"  
    	by (metis assms list.rrel_neper mem_Collect_eq neper_classes_eq) 

    show "distinct_rlt R (gg R ys)"
    unfolding distinct_rlt_simp[OF R 1] unfolding  distinct_map proof safe
      show "distinct (gg R ys)" unfolding gg_def by simp
      show "inj_on (getRepr R) (set (gg R ys))" unfolding inj_on_def gg_def 
      by simp (metis assms geterRepr_related list_all2_same neper_getRepr_eq ys2(1))
    qed
    
    show "distinct_rlt R ys" using r unfolding restr_def by simp
  qed 
qed

lemma bij_upto_gg: 
assumes R: "neper R"
shows "bij_upto 
    (restr (dlist_all2 R) distinct)
    (restr (rrel_list R) (distinct_rlt R)) 
    (gg R)"
proof(intro bij_uptoI)
  show "neper (restr (rrel_list R) (distinct_rlt R))"
  using neper_restr_rrel_list_distinct_rlt[OF R] .
next
  fix xs ys 
  assume "restr (dlist_all2 R) distinct xs ys"
  thus "restr (rrel_list R) (distinct_rlt R) (gg R xs) (gg R ys)"
  using gg_forward[OF R] by simp  
next
  fix xs ys assume xs: "restr (dlist_all2 R) distinct xs xs"
  and ys: "restr (dlist_all2 R) distinct ys ys"
  and 0: "restr (rrel_list R) (distinct_rlt R) (gg R xs) (gg R ys)"
  thus "restr (dlist_all2 R) distinct xs ys"
  using gg_backward[OF R] by simp  
next  
  fix ys assume r: "restr (rrel_list R) (distinct_rlt R) ys ys" 
  thus "\<exists>xs. restr (dlist_all2 R) distinct xs xs \<and> 
             restr (rrel_list R) (distinct_rlt R) ys (gg R xs)" 
  using gg_surj_upto[OF R] by simp 
qed
     
lemma gg_eq[simp]: "\<And>xs. distinct xs \<Longrightarrow> gg (=) xs = xs"
unfolding gg_def fun_eq_iff by simp

lemma neper_rel_dlist[simp]: "neper R \<Longrightarrow> neper (rel_dlist R)"
apply(rule relator_pres_neper[of rel_dlist], safe)
  subgoal using dlist.rel_compp .
  subgoal using dlist.rel_conversep .
  subgoal apply(rule exI[of _ "Abs_dlist []"])
  unfolding rel_dlist_alt2 dlist_all2  
  by (simp add: Abs_dlist_inverse) .

(* *)

wide_typedef dlist rel: rel_dlist rep: "\<lambda>R. gg R \<circ> list_of_dlist"
  subgoal using neper_rel_dlist .
  subgoal using dlist.rel_eq .
  subgoal using bij_upto_transportFromRaw[OF dlist.type_definition_dlist rel_dlist_alt2 bij_upto_gg] .
  subgoal unfolding fun_eq_iff o_def apply safe apply(subst gg_eq) by auto .


end

(*  Title:      HOL/Library/DAList.thy
    Author:     Lukas Bulwahn, TU Muenchen
*)

section \<open>Abstract type of association lists with unique keys\<close>

theory DAList
imports AList
begin

text \<open>This was based on some existing fragments in the AFP-Collection framework.\<close>

subsection \<open>Preliminaries\<close>

lemma distinct_map_fst_filter:
  "distinct (map fst xs) \<Longrightarrow> distinct (map fst (List.filter P xs))"
  by (induct xs) auto


subsection \<open>Type \<open>('key, 'value) alist\<close>\<close>

typedef ('key, 'value) alist = "{xs :: ('key \<times> 'value) list. (distinct \<circ> map fst) xs}"
  morphisms impl_of Alist
proof
  show "[] \<in> {xs. (distinct \<circ> map fst) xs}"
    by simp
qed

setup_lifting type_definition_alist

lemma alist_ext: "impl_of xs = impl_of ys \<Longrightarrow> xs = ys"
  by (simp add: impl_of_inject)

lemma alist_eq_iff: "xs = ys \<longleftrightarrow> impl_of xs = impl_of ys"
  by (simp add: impl_of_inject)

lemma impl_of_distinct [simp, intro]: "distinct (map fst (impl_of xs))"
  using impl_of[of xs] by simp

lemma Alist_impl_of [code abstype]: "Alist (impl_of xs) = xs"
  by (rule impl_of_inverse)


subsection \<open>Primitive operations\<close>

lift_definition lookup :: "('key, 'value) alist \<Rightarrow> 'key \<Rightarrow> 'value option" is map_of  .

lift_definition empty :: "('key, 'value) alist" is "[]"
  by simp

lift_definition update :: "'key \<Rightarrow> 'value \<Rightarrow> ('key, 'value) alist \<Rightarrow> ('key, 'value) alist"
  is AList.update
  by (simp add: distinct_update)

(* FIXME: we use an unoptimised delete operation. *)
lift_definition delete :: "'key \<Rightarrow> ('key, 'value) alist \<Rightarrow> ('key, 'value) alist"
  is AList.delete
  by (simp add: distinct_delete)

lift_definition map_entry ::
    "'key \<Rightarrow> ('value \<Rightarrow> 'value) \<Rightarrow> ('key, 'value) alist \<Rightarrow> ('key, 'value) alist"
  is AList.map_entry
  by (simp add: distinct_map_entry)

lift_definition filter :: "('key \<times> 'value \<Rightarrow> bool) \<Rightarrow> ('key, 'value) alist \<Rightarrow> ('key, 'value) alist"
  is List.filter
  by (simp add: distinct_map_fst_filter)

lift_definition map_default ::
    "'key \<Rightarrow> 'value \<Rightarrow> ('value \<Rightarrow> 'value) \<Rightarrow> ('key, 'value) alist \<Rightarrow> ('key, 'value) alist"
  is AList.map_default
  by (simp add: distinct_map_default)


subsection \<open>Abstract operation properties\<close>

(* FIXME: to be completed *)

lemma lookup_empty [simp]: "lookup empty k = None"
by (simp add: empty_def lookup_def Alist_inverse)

lemma lookup_update:
  "lookup (update k1 v xs) k2 = (if k1 = k2 then Some v else lookup xs k2)"
by(transfer)(simp add: update_conv')

lemma lookup_update_eq [simp]:
  "k1 = k2 \<Longrightarrow> lookup (update k1 v xs) k2 = Some v"
by(simp add: lookup_update)

lemma lookup_update_neq [simp]:
  "k1 \<noteq> k2 \<Longrightarrow> lookup (update k1 v xs) k2 = lookup xs k2"
by(simp add: lookup_update)

lemma update_update_eq [simp]:
  "k1 = k2 \<Longrightarrow> update k2 v2 (update k1 v1 xs) = update k2 v2 xs"
by(transfer)(simp add: update_conv')

lemma lookup_delete [simp]: "lookup (delete k al) = (lookup al)(k := None)"
  by (simp add: lookup_def delete_def Alist_inverse distinct_delete delete_conv')


subsection \<open>Further operations\<close>

subsubsection \<open>Equality\<close>

instantiation alist :: (equal, equal) equal
begin

definition "HOL.equal (xs :: ('a, 'b) alist) ys == impl_of xs = impl_of ys"

instance
  by standard (simp add: equal_alist_def impl_of_inject)

end


subsubsection \<open>Size\<close>

instantiation alist :: (type, type) size
begin

definition "size (al :: ('a, 'b) alist) = length (impl_of al)"

instance ..

end


subsection \<open>Quickcheck generators\<close>

context
  includes state_combinator_syntax term_syntax
begin

definition
  valterm_empty :: "('key :: typerep, 'value :: typerep) alist \<times> (unit \<Rightarrow> Code_Evaluation.term)"
  where "valterm_empty = Code_Evaluation.valtermify empty"

definition
  valterm_update :: "'key :: typerep \<times> (unit \<Rightarrow> Code_Evaluation.term) \<Rightarrow>
  'value :: typerep \<times> (unit \<Rightarrow> Code_Evaluation.term) \<Rightarrow>
  ('key, 'value) alist \<times> (unit \<Rightarrow> Code_Evaluation.term) \<Rightarrow>
  ('key, 'value) alist \<times> (unit \<Rightarrow> Code_Evaluation.term)" where
  [code_unfold]: "valterm_update k v a = Code_Evaluation.valtermify update {\<cdot>} k {\<cdot>} v {\<cdot>}a"

fun random_aux_alist
where
  "random_aux_alist i j =
    (if i = 0 then Pair valterm_empty
     else Quickcheck_Random.collapse
       (Random.select_weight
         [(i, Quickcheck_Random.random j \<circ>\<rightarrow> (\<lambda>k. Quickcheck_Random.random j \<circ>\<rightarrow>
           (\<lambda>v. random_aux_alist (i - 1) j \<circ>\<rightarrow> (\<lambda>a. Pair (valterm_update k v a))))),
          (1, Pair valterm_empty)]))"

end

instantiation alist :: (random, random) random
begin

definition random_alist
where
  "random_alist i = random_aux_alist i i"

instance ..

end

instantiation alist :: (exhaustive, exhaustive) exhaustive
begin

fun exhaustive_alist ::
  "(('a, 'b) alist \<Rightarrow> (bool \<times> term list) option) \<Rightarrow> natural \<Rightarrow> (bool \<times> term list) option"
where
  "exhaustive_alist f i =
    (if i = 0 then None
     else
      case f empty of
        Some ts \<Rightarrow> Some ts
      | None \<Rightarrow>
          exhaustive_alist
            (\<lambda>a. Quickcheck_Exhaustive.exhaustive
              (\<lambda>k. Quickcheck_Exhaustive.exhaustive (\<lambda>v. f (update k v a)) (i - 1)) (i - 1))
            (i - 1))"

instance ..

end

instantiation alist :: (full_exhaustive, full_exhaustive) full_exhaustive
begin

fun full_exhaustive_alist ::
  "(('a, 'b) alist \<times> (unit \<Rightarrow> term) \<Rightarrow> (bool \<times> term list) option) \<Rightarrow> natural \<Rightarrow>
    (bool \<times> term list) option"
where
  "full_exhaustive_alist f i =
    (if i = 0 then None
     else
      case f valterm_empty of
        Some ts \<Rightarrow> Some ts
      | None \<Rightarrow>
          full_exhaustive_alist
            (\<lambda>a.
              Quickcheck_Exhaustive.full_exhaustive
                (\<lambda>k. Quickcheck_Exhaustive.full_exhaustive (\<lambda>v. f (valterm_update k v a)) (i - 1))
              (i - 1))
            (i - 1))"

instance ..

end


section \<open>alist is a BNF\<close>

lift_bnf (dead 'k, set: 'v) alist [wits: "[] :: ('k \<times> 'v) list"] for map: map rel: rel
  by auto

hide_const valterm_empty valterm_update random_aux_alist

hide_fact (open) lookup_def empty_def update_def delete_def map_entry_def filter_def map_default_def
hide_const (open) impl_of lookup empty update delete map_entry filter map_default map set rel


(*******************)
(* the alist type-definition is wide *)

(* *)

definition "kvdistinct \<equiv> distinct \<circ> map fst"
 
lemma kvdistinct_aux: "kvdistinct = kvdistinct" ..
local_setup \<open>RLTHM @{binding kvdistinct_aux_rlt'} @{thm kvdistinct_aux}\<close>
term kvdistinct_rlt

lemma kvdistinct_rlt_simp[simp]: 
"neper R1 \<Longrightarrow> neper R2 \<Longrightarrow> rrel_list (rel_prod R1 R2) kvs kvs \<Longrightarrow>
kvdistinct_rlt R1 R2 kvs \<longleftrightarrow> 
distinct (map (getRepr R1) (map fst kvs))"
unfolding kvdistinct_rlt_def comp_rlt_def apply simp apply(subst distinct_rlt_simp)
  subgoal by auto
  subgoal unfolding rrel_alt  
    by (simp add: list_all2_conv_all_nth rel_prod_sel rlt_param neper)
  subgoal by (auto simp: rlt_param neper) .

(* *)

lemma restr_kvdistinct_rlt_distinct: 
assumes R: "neper R1" "neper R2"
shows "restr (list_all2 (rel_prod R1 R2)) (kvdistinct_rlt R1 R2) \<le> 
       restr (list_all2 (rel_prod R1 R2)) (distinct \<circ> map fst)"
proof-
  have "\<And> kvs. rrel_list (rel_prod R1 R2) kvs kvs
     \<Longrightarrow> kvdistinct_rlt R1 R2 kvs \<Longrightarrow> (distinct \<circ> map fst) kvs"
  using R using distinct_map by fastforce
  thus ?thesis using R unfolding restr_def rrel_alt 
  by auto (smt (verit, best) list_all2_conv_all_nth neper_def per_def rel_prod_sel)+
qed 

(* *)

definition rrel_alist :: "('k\<Rightarrow>'k\<Rightarrow>bool) \<Rightarrow> ('v\<Rightarrow>'v\<Rightarrow>bool) \<Rightarrow> ('k,'v)alist \<Rightarrow> ('k,'v)alist \<Rightarrow> bool"
where "rrel_alist R1 R2 = (inv_imagep (restr (list_all2 (rel_prod R1 R2)) (kvdistinct_rlt R1 R2)) alist.impl_of)"

(* *)

lemma neper_rrel_alist[simp]:
"neper R1 \<Longrightarrow> neper R2 \<Longrightarrow> neper (rrel_alist R1 R2)"
unfolding rrel_alist_def apply(rule neper_inv_imagep[of _ _ "Alist []"])
  apply(rule neper_restr)
    subgoal by (metis list.rrel_neper prod.rrel_neper rrel_alt)
    subgoal apply(rule exI[of _ "[]"]) by (simp add: rrel_alt)
    subgoal  by (metis empty.abs_eq empty.rep_eq impl_of_distinct kvdistinct_rlt_simp 
       list.ctr_transfer(1) list.simps(8) restr_def rrel_alt) .


lemma kvdistinct_rlt_eq[simp]: "kvdistinct_rlt (=) (=) = distinct \<circ> map fst"
by (simp add: kvdistinct_def kvdistinct_rlt_eq)

lemma rrel_alist_eq[simp]: 
"rrel_alist (=) (=) = (=)"
unfolding rrel_alist_def inv_imagep_def fun_eq_iff 
by (simp add: alist_eq_iff list_all2_eq prod.rel_eq restr_def)

(* *)

lemma bij_upto_alist: 
assumes R: "neper R1" "neper R2"
shows "bij_upto 
    (restr (restr (list_all2 (rel_prod R1 R2)) (kvdistinct_rlt R1 R2)) (distinct \<circ> map fst))
    (restr (list_all2 (rel_prod R1 R2)) (kvdistinct_rlt R1 R2)) 
    id"
unfolding restr_leq[OF restr_kvdistinct_rlt_distinct[OF R]]
apply(rule bij_upto_id) using assms 
	by (metis distinct_rlt_Nil distinct_rlt_eq kvdistinct_rlt_simp list.rrel_neper list.simps(8) 
   list_all2_Nil  neper_eq neper_restr prod.rrel_neper rrel_alt)

thm bij_upto_transportFromRaw[OF alist.type_definition_alist rrel_alist_def bij_upto_alist, simped]
  
wide_typedef alist rel: rrel_alist rep: "\<lambda>R1 R2. alist.impl_of"
  subgoal using neper_rrel_alist .
  subgoal using rrel_alist_eq .
  subgoal for R1 R2 using 
   bij_upto_transportFromRaw[OF alist.type_definition_alist rrel_alist_def bij_upto_alist, simped] 
  unfolding  rrel_alt kvdistinct_rlt_def .
  subgoal .. .

(* Compatibility with the BNF relator for alist: *)
lemma rrel_alist_eq_alist_rel: "neper R \<Longrightarrow> rrel_alist (=) R = alist.rel R"
unfolding alist.rel_def rrel_alist_def BNF_Def.vimage2p_def inv_imagep_def fun_eq_iff
restr_def apply safe
  subgoal apply(subst kvdistinct_rlt_simp) unfolding rrel_alt 
  apply (auto simp: list_all2_conv_all_nth )  
  by (metis (mono_tags, lifting) neper_per per_def rel_prod_sel)
  subgoal apply(subst kvdistinct_rlt_simp) unfolding rrel_alt 
  apply (auto simp: list_all2_conv_all_nth )  
  by (metis (mono_tags, lifting) neper_per per_def rel_prod_sel) .



end

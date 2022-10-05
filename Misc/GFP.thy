(*  Title:       GFP
    Authors:     Jasmin Blanchette, Andrei Popescu, Dmitriy Traytel
    Maintainer:  Dmitriy Traytel <traytel at inf.ethz.ch>
*)

section \<open>Greatest Fixpoint (a.k.a. Codatatype)\<close>

(*<*)
theory GFP
  imports "HOLRLT-Library.BNF_Axiomatization"
begin
  (*>*)

unbundle cardinal_syntax

ML \<open>open Ctr_Sugar_Util\<close>
notation BNF_Def.convol ("<_ , _>")

text \<open>
\begin{tabular}{rcl}
  'b &=& ('a, 'b) F
\end{tabular}

To build a witness scenario, let us assume

\begin{tabular}{rcl}
  ('a, 'b) F &=& unit + 'a * 'b
\end{tabular}
\<close>

declare [[bnf_internals]]
bnf_axiomatization (Fset1: 'a, Fset2: 'b)  F
  [wits: "('a, 'b) F"]
  for map: Fmap rel: Frel

declare F.rel_eq[rrel_eq]

axiomatization where Frel_neper[simp]:
  "\<And>R1 R2. neper R1 \<Longrightarrow> neper R2 \<Longrightarrow> neper (Frel R1 R2)"

local_setup \<open>Wide_Database.register_wide @{type_name F}
  {T = @{typ "('a, 'b) F"}, axioms = {bij_upto = refl,
    rel_eq = @{thm F.rel_eq}, rel_per = @{thm Frel_neper}, rep_eq = refl, cond_eq = NONE},
    facts = (), rel = @{term "Frel :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow>
  ('a, 'b) F \<Rightarrow> ('a, 'b) F \<Rightarrow> bool"}, cond = NONE, deps = []}\<close>

abbreviation Fin :: "'a1 set \<Rightarrow> 'a2 set \<Rightarrow> (('a1, 'a2) F) set" where
  "Fin A1 A2 \<equiv> {x. Fset1 x \<subseteq> A1 \<and> Fset2 x \<subseteq> A2}"

lemma Fmap_comp_id: "Fmap g1 g2 (Fmap id f2 x) = Fmap g1 (g2 o f2) x"
  apply (rule trans)
   apply (rule F.map_comp)
  unfolding o_id
  apply (rule refl)
  done

lemmas Fin_mono2 = F.in_mono[OF subset_refl]
lemmas Fin_mono2' = subsetD[OF Fin_mono2]

lemma Fmap_congL: "\<lbrakk>\<forall>a \<in> Fset2 x. f a = a\<rbrakk> \<Longrightarrow>
  Fmap id f x = x"
  apply (rule trans)
   apply (rule F.map_cong0)
    apply (rule refl)
   apply (rule trans)
    apply (erule bspec)
    apply assumption
   apply (rule sym)
   apply (rule id_apply)
  apply (rule F.map_id)
  done


subsection \<open>Coalgebra\<close>

definition coalg where
  "coalg B s = ((\<forall>a \<in> B. s a \<in> Fin (UNIV :: 'a set) B))"

lemmas coalg_Fin = bspec[OF iffD1[OF coalg_def]]

lemma coalg_Fset2:
  "\<lbrakk>coalg B s; a \<in> B\<rbrakk> \<Longrightarrow> Fset2 (s a) \<subseteq> B"
  apply (tactic \<open>dtac @{context} @{thm iffD1[OF coalg_def]} 1\<close>)
  apply (drule bspec[rotated])
   apply assumption
  apply (erule CollectE conjE)+
  apply assumption
  done


subsection\<open>Type-coalgebra\<close>

abbreviation "tcoalg s \<equiv> coalg UNIV s"

lemma tcoalg: "tcoalg s"
  apply (tactic \<open>rtac @{context} (@{thm coalg_def} RS iffD2) 1\<close>)
  apply (rule ballI)
  apply (rule CollectI)
  apply (rule conjI)
   apply (rule subset_UNIV)
  apply (rule subset_UNIV)
  done


subsection \<open>Morphism\<close>

definition mor where
  "mor B s B' s' f =
   ((\<forall>a \<in> B. f a \<in> B') \<and>
    (\<forall>z \<in> B. Fmap (id :: 'a \<Rightarrow> 'a) f (s z) = s' (f z)))"

lemma mor_image: "mor B s B' s' f \<Longrightarrow> f ` B \<subseteq> B'"
  apply (tactic \<open>dtac @{context} @{thm iffD1[OF mor_def]} 1\<close>)
  apply (erule conjE)+
  apply (rule image_subsetI)
  apply (erule bspec)
  apply assumption
  done

lemmas mor_image' = subsetD[OF mor_image imageI]

lemma morE: "\<lbrakk>mor B s B' s' f; z \<in> B\<rbrakk>
   \<Longrightarrow> Fmap id f (s z) = s' (f z)"
  apply (tactic \<open>dtac @{context} @{thm iffD1[OF mor_def]} 1\<close>)
  apply (erule conjE)+
  apply (erule bspec)
  apply assumption
  done

lemma mor_incl: "\<lbrakk>B \<subseteq> B'\<rbrakk> \<Longrightarrow> mor B s B' s id"
  apply (tactic \<open>rtac @{context} (@{thm mor_def} RS iffD2) 1\<close>)
  apply (rule conjI)
   apply (rule ballI)
   apply (rule ssubst_mem[OF id_apply])
   apply (erule subsetD)
   apply assumption
  apply (rule ballI)
  apply (rule trans[OF F.map_id])
  apply (rule sym)
  apply (rule arg_cong[OF id_apply])
  done

lemmas mor_id = mor_incl[OF subset_refl]

lemma mor_comp:
  "\<lbrakk>mor B s B' s' f;
    mor B' s' B'' s'' f'\<rbrakk> \<Longrightarrow>
   mor B s B'' s'' (f' o f)"
  apply (tactic \<open>rtac @{context} (@{thm mor_def} RS iffD2) 1\<close>)
  apply (rule conjI)

   apply (rule ballI)
   apply (rule ssubst_mem[OF o_apply])
   apply (erule mor_image')
   apply (erule mor_image')
   apply assumption

  apply (rule ballI)
  apply (tactic \<open>stac @{context} @{thm o_apply} 1\<close>)
  apply (rule trans)
   apply (rule sym[OF Fmap_comp_id])
  apply (rule trans)
   apply (erule arg_cong[OF morE])
   apply assumption
  apply (erule morE)
  apply (erule mor_image')
  apply assumption
  done

lemma mor_cong: "\<lbrakk> f' = f; mor B s B' s' f\<rbrakk> \<Longrightarrow>
  mor B s B' s' f'"
  apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
  apply assumption
  done

lemma mor_UNIV: "mor UNIV s UNIV s' f \<longleftrightarrow>
  Fmap id f o s = s' o f"
  apply (rule iffI)
   apply (rule ext)
   apply (rule trans)
    apply (rule trans)
     apply (rule o_apply)
    apply (erule morE)
    apply (rule UNIV_I)
   apply (rule sym[OF o_apply])

  apply (tactic \<open>rtac @{context} (@{thm mor_def} RS iffD2) 1\<close>)
  apply (rule conjI)
   apply (rule ballI)
   apply (rule UNIV_I)
  apply (rule ballI)
  apply (erule o_eq_dest)
  done

lemma mor_str:
  "mor UNIV s UNIV (Fmap id s) s"
  apply (rule iffD2)
   apply (rule mor_UNIV)
  apply (rule refl)
  done

lemma mor_case_sum:
  "mor UNIV s UNIV (case_sum (Fmap id Inl o s) s') Inl"
  apply (tactic \<open>rtac @{context} (@{thm mor_UNIV} RS iffD2) 1\<close>)
  apply (rule sym)
  apply (rule case_sum_o_inj(1))
  done

subsection \<open>Bisimulations\<close>

definition bis where
  "bis B s B' s' R =
   ((R \<subseteq> B \<times> B') \<and>
   ((\<forall>b1 b1'. (b1, b1') \<in> R \<longrightarrow>
     (\<exists>z \<in> Fin UNIV R. Fmap id fst z = s b1 \<and> Fmap id snd z = s' b1'))))"

lemma bis_cong: "\<lbrakk>bis B s B' s' R; R' = R\<rbrakk> \<Longrightarrow> bis B s B' s' R'"
  apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
  apply assumption
  done

lemma bis_Frel:
  "bis B s B' s' R \<longleftrightarrow>
  (R \<subseteq> B \<times> B') \<and> ((\<forall> b1 b1'. (b1, b1') \<in> R \<longrightarrow> Frel (=) (in_rel R) (s b1) (s' b1')))"
  apply (rule trans[OF bis_def])
  apply (rule iffI)
   apply (erule conjE)
   apply (erule conjI)

   apply (rule allI)
   apply (rule allI)
   apply (rule impI)
   apply (erule allE)+
   apply (erule impE)
    apply assumption
   apply (erule bexE)
   apply (erule conjE CollectE)+
   apply (rule iffD2[OF F.in_rel])
   apply (rule exI)
   apply (rule conjI[rotated])
    apply (rule conjI)
     apply (rule trans)
      apply (rule trans)
       apply (rule F.map_comp)
      apply (rule F.map_cong0)
       apply (rule fst_diag_id)
      apply (rule fun_cong[OF o_id])
     apply assumption

    apply (rule trans)
     apply (rule trans)
      apply (rule F.map_comp)
     apply (rule F.map_cong0)
      apply (rule snd_diag_id)
     apply (rule fun_cong[OF o_id])
    apply assumption

   apply (rule CollectI)
   apply (rule conjI)
    apply (rule ord_eq_le_trans)
     apply (rule F.set_map(1))
    apply (rule subset_trans)
     apply (erule image_mono)
    apply (rule image_subsetI)
    apply (rule CollectI)
    apply (rule case_prodI)
    apply (rule refl)
   apply (rule ord_eq_le_trans)
    apply (rule trans)
     apply (rule F.set_map(2))
    apply (rule trans[OF fun_cong[OF image_id] id_apply])
   apply (erule Collect_case_prod_in_rel_leI)

  apply (erule conjE)
  apply (erule conjI)

  apply (rule allI)
  apply (rule allI)
  apply (rule impI)
  apply (erule allE)
  apply (erule allE)
  apply (erule impE)
   apply assumption
  apply (drule iffD1[OF F.in_rel])
  apply (erule exE conjE CollectE Collect_case_prod_in_rel_leE)+

(*Frel_bis_su*)
  apply (rule bexI)
   apply (rule conjI)
    apply (rule trans)
     apply (rule F.map_comp)
    apply (tactic \<open>stac @{context} @{thm id_o} 1\<close>)
    apply (tactic \<open>stac @{context} @{thm o_id} 1\<close>)
    apply assumption

   apply (rule trans)
    apply (rule F.map_comp)
   apply (tactic \<open>stac @{context} @{thm id_o} 1\<close>)
   apply (tactic \<open>stac @{context} @{thm o_id} 1\<close>)
   apply (rule trans)
    apply (rule F.map_cong0)
     apply (rule Collect_case_prodD)
     apply (erule subsetD)
     apply assumption
    apply (rule refl)
   apply assumption

  apply (rule CollectI)
  apply (rule conjI)
   apply (rule subset_UNIV)

  apply (rule ord_eq_le_trans)
   apply (rule trans)
    apply (rule F.set_map(2))
   apply (rule trans[OF fun_cong[OF image_id] id_apply])
  apply assumption
  done

lemma bis_converse:
  "bis B s B' s' R \<Longrightarrow> bis B' s' B s (R^-1)"
  apply (tactic \<open>rtac @{context} (@{thm bis_Frel} RS iffD2) 1\<close>)
  apply (tactic \<open>dtac @{context} (@{thm bis_Frel} RS iffD1) 1\<close>)
  apply (erule conjE)+
  apply (rule conjI)

   apply (rule iffD1[OF converse_subset_swap])
   apply (erule subset_trans)
   apply (rule equalityD2)
   apply (rule converse_Times)

  apply (rule allI)
  apply (rule allI)
  apply (rule impI)
  apply (rule predicate2D[OF eq_refl[OF arg_cong2[of _ _ _ _ "Frel"]]])
    apply (rule conversep_eq)
   apply (rule conversep_in_rel)
  apply (rule predicate2D[OF eq_refl[OF sym[OF F.rel_conversep]]])
  apply (erule allE)+
  apply (rule conversepI)
  apply (erule mp)
  apply (erule converseD)
  done

lemma bis_Comp:
  "\<lbrakk>bis B s B' s' P;
    bis B' s' B'' s'' Q\<rbrakk> \<Longrightarrow>
    bis B s B'' s'' (P O Q)"
  apply (tactic \<open>rtac @{context} (@{thm bis_Frel[THEN iffD2]}) 1\<close>)
  apply (tactic \<open>dtac @{context} (@{thm bis_Frel[THEN iffD1]}) 1\<close>)+
  apply (erule conjE)+
  apply (rule conjI)
   apply (erule relcomp_subset_Sigma)
   apply assumption

  apply (rule allI)+
  apply (rule impI)
  apply (rule predicate2D[OF eq_refl[OF arg_cong2[of _ _ _ _ "Frel"]]])
    apply (rule eq_OO)
   apply (rule relcompp_in_rel)
  apply (rule predicate2D[OF eq_refl[OF sym[OF F.rel_compp]]])
  apply (erule relcompE)
  apply (tactic \<open>dtac @{context} (@{thm prod.inject[THEN iffD1]}) 1\<close>)
  apply (erule conjE)
  apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
  apply (erule allE)+
  apply (rule relcomppI)
   apply (erule mp)
   apply assumption
  apply (erule mp)
  apply assumption
  done

lemma bis_Gr: "\<lbrakk>coalg B s; mor B s B' s' f\<rbrakk> \<Longrightarrow> bis B s B' s' (BNF_Def.Gr B f)"
  unfolding bis_Frel eq_alt in_rel_Gr F.rel_Grp
  apply (rule conjI)
   apply (rule iffD2[OF Gr_incl])
   apply (erule mor_image)

  apply (rule allI)
  apply (rule allI)
  apply (rule impI)
  apply (rule GrpI)
   apply (erule trans[OF morE])
    apply (erule GrD1)
   apply (erule arg_cong[OF GrD2])
  apply (erule coalg_Fin)
  apply (erule GrD1)
  done

lemmas bis_image2 = bis_cong[OF bis_Comp[OF bis_converse[OF bis_Gr] bis_Gr] image2_Gr]
lemmas bis_diag = bis_cong[OF bis_Gr[OF _ mor_id] Id_on_Gr]

lemma bis_Union: "\<forall>i \<in> I. bis B s B s (R1i i) \<Longrightarrow> bis B s B s (\<Union>i\<in> I. R1i i)"
  unfolding bis_def
  apply (rule conjI)
   apply (rule UN_least)
   apply (drule bspec)
    apply assumption
   apply (drule conjunct1)
   apply assumption

  apply (rule allI)+
  apply (rule impI)
  apply (erule UN_E)
  apply (drule bspec)
   apply assumption
  apply (drule conjunct2)
  apply (erule allE)+
  apply (drule mp)
   apply assumption
  apply (erule bexE)
  apply (rule bexI)
   apply assumption
  apply (rule Fin_mono2')
   apply (erule SUP_upper2[OF _ subset_refl])
  apply assumption
  done

(* self-bisimulation: *)
abbreviation "sbis B s R \<equiv> bis B s B s R"

(* The greatest self-bisimulation *)
definition lsbis where "lsbis B s =
  (\<Union>R \<in> {R | R . sbis B s R}. R)"

lemma sbis_lsbis:
  "sbis B s (lsbis B s)"
  apply (tactic \<open>rtac @{context} (Thm.permute_prems 0 1 @{thm bis_cong}) 1\<close>)
   apply (rule lsbis_def)
  apply (rule bis_Union)
  apply (rule ballI)
  apply (erule CollectE exE conjE)+
  apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
  apply (erule bis_cong)
  apply (rule refl)
  done

lemmas lsbis_incl = conjunct1[OF iffD1[OF bis_def], OF sbis_lsbis]
lemmas lsbisE =
  mp[OF spec[OF spec[OF conjunct2[OF iffD1[OF bis_def]], OF sbis_lsbis]]]

lemma incl_lsbis: "sbis B s R \<Longrightarrow> R \<subseteq> lsbis B s"
  apply (rule xt1(3))
   apply (rule lsbis_def)
  apply (rule SUP_upper2)
   apply (rule CollectI)
   apply (rule exI)+
   apply (rule conjI)
    apply (rule refl)
   apply assumption
  apply (rule equalityD2)
  apply (rule refl)
  done

lemma equiv_lsbis: "coalg B s \<Longrightarrow> equiv B (lsbis B s)"
  apply (rule iffD2[OF equiv_def])

  apply (rule conjI)
   apply (rule iffD2[OF refl_on_def])
   apply (rule conjI)
    apply (rule lsbis_incl)
   apply (rule ballI)
   apply (rule subsetD)
    apply (rule incl_lsbis)
    apply (rule bis_diag)
    apply assumption
   apply (erule Id_onI)

  apply (rule conjI)
   apply (rule iffD2[OF sym_def])
   apply (rule allI)+
   apply (rule impI)
   apply (rule subsetD)
    apply (rule incl_lsbis)
    apply (rule bis_converse)
    apply (rule sbis_lsbis)
   apply (erule converseI)

  apply (rule iffD2[OF trans_def])
  apply (rule allI)+
  apply (rule impI)+
  apply (rule subsetD)
   apply (rule incl_lsbis)
   apply (rule bis_Comp)
    apply (rule sbis_lsbis)
   apply (rule sbis_lsbis)
  apply (erule relcompI)
  apply assumption
  done


subsection \<open>The Tree Coalgebra\<close>

typedef bd_type_JF = "UNIV :: (bd_type_F) set"
  by auto

type_synonym 'a JT = "((bd_type_JF) list set \<times>
  (bd_type_JF list \<Rightarrow> ('a, bd_type_JF) F))"

abbreviation "bd_JF \<equiv> dir_image bd_F Abs_bd_type_JF"
lemmas bd_F = dir_image[OF Abs_bd_type_JF_inject[OF UNIV_I UNIV_I] F.bd_Card_order] 
lemmas bd_F_Cinfinite = Cinfinite_cong[OF bd_F F.bd_Cinfinite]
lemmas bd_F_Card_order = Card_order_ordIso[OF F.bd_Card_order ordIso_symmetric[OF bd_F]]
lemma bd_F_card_order: "card_order bd_JF" 
	by (metis Abs_bd_type_JF_inject F.bd_card_order Rep_bd_type_JF_inverse UNIV_I bijI' card_order_dir_image)


lemmas Fset1_bd' = ordLeq_transitive[OF F.set_bd(1) ordLeq_ordIso_trans[OF ordLeq_refl[OF F.bd_Card_order] bd_F]]
lemmas Fset2_bd' = ordLeq_transitive[OF F.set_bd(2) ordLeq_ordIso_trans[OF ordLeq_refl[OF F.bd_Card_order] bd_F]]

(* 
abbreviation Succ :: "bd_type_JF list set \<Rightarrow> bd_type_JF list \<Rightarrow> bd_type_JF set" where
"Succ Kl kl \<equiv> {k. k \<in> BNF_Greatest_Fixpoint.Succ Kl kl}"

definition Succ :: "bd_type_JF list set \<Rightarrow> bd_type_JF list \<Rightarrow> bd_type_JF set" where
"Succ Kl kl \<equiv> {k. k \<in> BNF_Greatest_Fixpoint.Succ Kl kl}"

definition strT :: "'a JT \<Rightarrow> ('a, 'a JT) F" where
  "strT = (case_prod (%Kl lab. Fmap id
   (\<lambda>k1. (BNF_Greatest_Fixpoint.Shift Kl k1, BNF_Greatest_Fixpoint.shift lab k1)) (lab [])))"
*)

definition Succ :: "bd_type_JF list set \<Rightarrow> bd_type_JF list \<Rightarrow> bd_type_JF set" where 
"Succ Kl kl = {k . kl @ [k] \<in> Kl}"
definition Shift :: "bd_type_JF list set \<Rightarrow> bd_type_JF \<Rightarrow> bd_type_JF list set" where 
"Shift Kl k = {kl. k # kl \<in> Kl}"
definition shift :: "(bd_type_JF list \<Rightarrow> ('a, bd_type_JF) F)
   \<Rightarrow> bd_type_JF \<Rightarrow> bd_type_JF list \<Rightarrow> ('a, bd_type_JF) F" where 
"shift lab k = (\<lambda>kl. lab (k # kl))"

lemma empty_Shift: "\<lbrakk>[] \<in> Kl; k \<in> Succ Kl []\<rbrakk> \<Longrightarrow> [] \<in> Shift Kl k"
  unfolding Shift_def Succ_def by simp

lemma SuccD: "k \<in> Succ Kl kl \<Longrightarrow> kl @ [k] \<in> Kl"
  unfolding Succ_def by simp

lemmas SuccE = SuccD[elim_format]

lemma SuccI: "kl @ [k] \<in> Kl \<Longrightarrow> k \<in> Succ Kl kl"
  unfolding Succ_def by simp

lemma ShiftD: "kl \<in> Shift Kl k \<Longrightarrow> k # kl \<in> Kl"
  unfolding Shift_def by simp

lemma Succ_Shift: "Succ (Shift Kl k) kl = Succ Kl (k # kl)"
  unfolding Succ_def Shift_def by auto

definition isNode :: 
"bd_type_JF list set \<Rightarrow> (bd_type_JF list \<Rightarrow> ('a, bd_type_JF) F) \<Rightarrow> bd_type_JF list \<Rightarrow> bool"
where
"isNode Kl lab kl = (\<exists>x1. lab kl = x1 \<and> Fset2 x1 = Succ Kl kl)"

abbreviation isTree where
  "isTree Kl lab \<equiv> ([] \<in> Kl \<and>
 (\<forall>kl \<in> Kl. (\<forall>k1 \<in> Succ Kl kl. isNode Kl lab (kl @ [k1]))))"

definition carT :: "'a JT set" where
  "carT = {(Kl :: (bd_type_JF) list set, lab) | Kl lab. isTree Kl lab \<and> isNode Kl lab []}"


definition strT :: "'a JT \<Rightarrow> ('a, 'a JT) F" where
  "strT = (case_prod (%Kl lab. Fmap id
   (\<lambda>k1. (Shift Kl k1, shift lab k1)) (lab [])))"

lemma coalg_T: "coalg carT strT"
  unfolding coalg_def carT_def isNode_def
  apply (rule ballI)
  apply (erule CollectE exE conjE)+
  apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
  apply (rule ssubst_mem[OF trans[OF fun_cong[OF strT_def] prod.case]])
  apply (rule CollectI)
  apply (rule conjI)
   apply (rule subset_UNIV)
  apply (rule ord_eq_le_trans[OF F.set_map(2)])
  apply (rule image_subsetI)
  apply (rule CollectI)
  apply (rule exI)+
  apply (rule conjI)
   apply (rule refl)
  apply (rule conjI)
   apply (rule conjI)
    apply (erule empty_Shift)
    apply (drule rev_subsetD)
     apply (erule equalityD1)
    apply assumption
   apply (rule ballI)
   apply (rule ballI)
   apply (drule ShiftD)
   apply (drule bspec)
    apply (erule thin_rl)
    apply assumption
   apply (drule bspec)
    apply (erule subsetD[OF equalityD1[OF Succ_Shift]])
   apply (erule exE conjE)+
   apply (rule exI)
   apply (rule conjI)
    apply (rule trans[OF fun_cong[OF shift_def]])
    apply (rule trans[OF arg_cong[OF sym[OF append_Cons]]])
    apply assumption
   apply (erule trans)
   apply (rule sym)
   apply (rule trans)
    apply (rule Succ_Shift)
   apply (rule arg_cong[OF sym[OF append_Cons]])

  apply (drule bspec)
   apply assumption
  apply (drule bspec)
   apply (erule subsetD[OF equalityD1])
   apply assumption
  apply (erule exE conjE)+
  apply (rule exI)
  apply (rule conjI)
   apply (rule trans[OF fun_cong[OF shift_def]])
   apply (erule trans[OF arg_cong[OF sym[OF append_Nil]]])
  apply (erule trans)
  apply (rule sym)
  apply (rule trans)
   apply (rule Succ_Shift)
  apply (rule arg_cong[OF sym[OF append_Nil]])
  done

abbreviation tobd_JF where "tobd_JF s x \<equiv> toCard (Fset2 (s x)) bd_JF"
abbreviation frombd_JF where "frombd_JF s x \<equiv> fromCard (Fset2 (s x)) bd_JF"

lemmas tobd_JF_inj = toCard_inj[OF Fset2_bd' bd_F_Card_order]
lemmas frombd_F2_tobd_JF = fromCard_toCard[OF Fset2_bd' bd_F_Card_order]

(* the levels of the behavior of a via s, through the embedding in Field bd_F *)
definition Lev where
  "Lev s = rec_nat (%a. {[]})
    (%n rec.
      (%a.
        {tobd_JF s a b # kl | b kl. b \<in> Fset2 (s a) \<and> kl \<in> rec b}))"

lemmas Lev_0 = fun_cong[OF rec_nat_0_imp[OF Lev_def]]
lemmas Lev_Suc = fun_cong[OF rec_nat_Suc_imp[OF Lev_def]]

(* recovery of the element corresponding to a path: *)
definition rv where
  "rv s = rec_list (%b1. b1)
    (%k kl rec.
      (%b1. (%k1. rec (frombd_JF s b1 k1)) k))"

lemmas rv_Nil = fun_cong[OF rec_list_Nil_imp[OF rv_def]]
lemmas rv_Cons = fun_cong[OF rec_list_Cons_imp[OF rv_def]]

(* the labels: *)
abbreviation "Lab s b1 kl \<equiv>
  (\<lambda>k. Fmap id (tobd_JF s k) (s k)) (rv s kl b1)"

(* the behavior of a under s: *)
definition "beh s a = (\<Union>n. Lev s n a, Lab s a)"

lemma length_Lev[rule_format]:
  "\<forall>kl b1 b2. (kl \<in> Lev s n b1 \<longrightarrow> length kl = n)"
  apply (rule nat_induct)
   apply (rule allI)+
   apply (rule impI)
   apply (drule subsetD[OF equalityD1[OF Lev_0]])
   apply (erule singletonE)
   apply (erule ssubst)
   apply (rule list.size(3))

  apply (rule allI)+
  apply (rule impI)
  apply (drule subsetD[OF equalityD1[OF Lev_Suc]])
  apply (erule CollectE exE conjE)+
  apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
  apply (rule trans)
   apply (rule length_Cons)
  apply (rule arg_cong[of _ _ Suc])
  apply (erule allE)+
  apply (erule mp)
  apply assumption
  done

lemma length_Lev': "kl \<in> Lev s n a \<Longrightarrow> kl \<in> Lev s (length kl) a"
  apply (frule length_Lev)
  apply (erule ssubst)
  apply assumption
  done

lemma rv_last:
  "\<forall>k b1 b2.
   ((\<exists>b1'. rv s (kl @ [k]) b1 = b1'))"
  apply (rule list.induct[of _ kl])
   apply (rule allI)+
   apply (rule exI)
   apply (rule trans[OF arg_cong[OF append_Nil]])
   apply (rule rv_Cons)

  apply (rule allI)+
  apply (erule allE)+
  apply (erule exE)
  apply (rule exI)
  apply (rule trans[OF arg_cong[OF append_Cons]])
  apply (rule trans[OF rv_Cons])
  apply assumption
  done

lemmas rv_last' = spec[OF spec[OF spec[OF rv_last]]]

lemma Fset_Lev:
  "\<forall>kl b1 b2 b1' b2' b1'' b2''.
   (kl \<in> Lev s n b1 \<longrightarrow>
    ((rv s kl b1 = b1' \<longrightarrow>
      (b1'' \<in> Fset2 (s b1') \<longrightarrow>
        kl @ [tobd_JF s b1' b1''] \<in> Lev s (Suc n) b1))))"
  apply (rule nat_induct[of _ n])
    (*IB*)
   apply (rule allI)+
   apply (rule impI)
   apply (drule subsetD[OF equalityD1[OF Lev_0]])
   apply (erule singletonE)
   apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
   apply (rule impI)
   apply (drule trans[OF sym])
    apply (rule rv_Nil)
   apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
   apply (rule impI)
   apply (rule ssubst_mem[OF append_Nil])
   apply (rule subsetD[OF equalityD2])
    apply (rule Lev_Suc)
   apply (rule CollectI)
   apply (rule exI)+
   apply (rule conjI)
    apply (rule refl)
   apply (erule conjI)
   apply (rule subsetD[OF equalityD2])
    apply (rule Lev_0)
   apply (rule singletonI)

(*IS*)
  apply (rule allI)+
  apply (rule impI)
  apply (drule subsetD[OF equalityD1[OF Lev_Suc]])
  apply (erule CollectE exE conjE)+
  apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
  apply (rule impI)
  apply (rule impI)
  apply (rule subsetD[OF equalityD2])
   apply (rule Lev_Suc)
  apply (rule ssubst_mem[OF append_Cons])
  apply (rule CollectI)
  apply (rule exI)+
  apply (rule conjI)
   apply (rule refl)
  apply (rule conjI)
   apply assumption
  apply (drule sym[OF trans[OF sym]])
   apply (rule trans[OF rv_Cons])
   apply (erule arg_cong[OF frombd_F2_tobd_JF])
  apply (erule allE)+
  apply (drule mp)
   apply assumption
  apply (drule mp)
   apply assumption
  apply (erule mp)
  apply assumption
  done

lemmas Fset_Lev' = Fset_Lev[rule_format]

lemma Fset_image_Lev:
  "\<forall>kl k b1 b2 b1' b2'.
   (kl \<in> Lev s n b1 \<longrightarrow>
    (kl @ [k] \<in> Lev s (Suc n) b1 \<longrightarrow>
      (rv s kl b1 = b1' \<longrightarrow> k \<in> tobd_JF s b1' ` Fset2 (s b1'))))"
  apply (rule nat_induct[of _ n])
    (*IB*)
   apply (rule allI)+
   apply (rule impI)
   apply (drule subsetD[OF equalityD1[OF Lev_0]])
   apply (erule singletonE)
   apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
   apply (rule impI)
   apply (rule impI)
   apply (drule trans[OF sym])
    apply (rule rv_Nil)
   apply (drule ssubst_mem[OF sym[OF append_Nil]])
   apply (drule subsetD[OF equalityD1[OF Lev_Suc]])
   apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
   apply (erule CollectE exE conjE)+
   apply (drule list.inject[THEN iffD1])
   apply (erule conjE)
   apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
   apply (erule imageI)
    (*IS*)

  apply (rule allI)+
  apply (rule impI)
  apply (drule subsetD[OF equalityD1[OF Lev_Suc]])
  apply (erule CollectE exE conjE)+
  apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
  apply (rule impI)
  apply (drule ssubst_mem[OF sym[OF append_Cons]])
  apply (drule subsetD[OF equalityD1[OF Lev_Suc]])
  apply (erule CollectE exE conjE)+
  apply (drule list.inject[THEN iffD1])
  apply (erule conjE)
  apply (tactic \<open>dtac @{context}
  (Thm.permute_prems 0 2 (@{thm tobd_JF_inj} RS iffD1)) 1\<close>)
    apply assumption
   apply assumption
  apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
  apply (rule impI)
  apply (drule trans[OF sym])
   apply (rule trans[OF rv_Cons])
   apply (rule trans[OF arg_cong[OF sum.case(1)]])
   apply (erule arg_cong[OF frombd_F2_tobd_JF])
  apply (erule allE)+
  apply (drule mp)
   apply assumption
  apply (drule mp)
   apply assumption
  apply (erule mp)
  apply (erule sym)
  done

lemmas Fset_image_Lev' = Fset_image_Lev[rule_format]

lemma mor_beh:
  "mor UNIV s carT strT (beh s)"
  apply (rule mor_cong)
   apply (rule ext[OF beh_def])
  apply (tactic \<open>rtac @{context} (@{thm mor_def} RS iffD2) 1\<close>)
  apply (rule conjI)
   apply (rule ballI)
   apply (rule subsetD[OF equalityD2[OF carT_def]])
   apply (rule CollectI)
   apply (rule exI)+
   apply (rule conjI)
    apply (rule refl)
   apply (rule conjI)
    apply (rule conjI)
     apply (rule UN_I)
      apply (rule UNIV_I)
     apply (rule subsetD)
      apply (rule equalityD2)
      apply (rule Lev_0)
     apply (rule singletonI)

    apply (rule ballI)
    apply (erule UN_E)
    apply (rule ballI)
    apply (erule CollectE SuccD[elim_format] UN_E)+
    apply (rule rev_mp[OF rv_last impI])
    apply (rule iffD2[OF isNode_def])
    apply (rule exI)
    apply (rule conjI)
     apply (rule refl)

    apply (rule trans[OF F.set_map(2)])
    apply (rule equalityI)
     apply (rule image_subsetI)
     apply (rule SuccI)
     apply (rule UN_I[OF UNIV_I])
     apply (erule Fset_Lev')
      apply (rule refl)
     apply assumption
    apply (rule subsetI)
    apply (erule CollectE SuccD[elim_format] UN_E)+
    apply (erule thin_rl)
    apply (erule thin_rl)
    apply (erule thin_rl)
    apply (erule thin_rl)
    apply (rule Fset_image_Lev')
      apply assumption
     apply (drule length_Lev)
     apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
     apply (drule length_Lev')
     apply (erule subsetD[OF equalityD1[OF arg_cong[OF length_append_singleton]]])
    apply (rule refl)

   apply (rule iffD2[OF isNode_def])
   apply (rule exI)
   apply (rule conjI)
    apply (rule arg_cong[OF rv_Nil])

   apply (rule trans[OF F.set_map(2)])
   apply (rule equalityI)
    apply (rule image_subsetI)
    apply (rule SuccI)
    apply (rule UN_I[OF UNIV_I])
    apply (rule Fset_Lev')
      apply (rule subsetD[OF equalityD2])
       apply (rule Lev_0)
      apply (rule singletonI)
     apply (rule rv_Nil)
    apply assumption
   apply (rule subsetI)
   apply (erule CollectE SuccD[elim_format] UN_E)+
   apply (rule Fset_image_Lev')
     apply (rule subsetD[OF equalityD2[OF Lev_0]])
     apply (rule singletonI)
    apply (drule length_Lev')
    apply (erule subsetD[OF equalityD1[OF arg_cong[OF
            trans[OF length_append_singleton arg_cong[of _ _ Suc, OF list.size(3)]]]]])
   apply (rule rv_Nil)

(*mor_tac*)

  apply (rule ballI)
  apply (rule sym)
  apply (rule trans)
   apply (rule trans[OF fun_cong[OF strT_def] prod.case])
  apply (tactic \<open>CONVERSION (Conv.top_conv
              (K (Conv.try_conv (Conv.rewr_conv (@{thm rv_Nil} RS eq_reflection)))) @{context}) 1\<close>)
  apply (rule trans[OF Fmap_comp_id])
  apply (rule F.map_cong0[OF refl])
  apply (rule trans)
   apply (rule o_apply)
  apply (rule iffD2)
   apply (rule prod.inject)
  apply (rule conjI)
   apply (rule trans)
    apply (rule Shift_def)

(*UN_Lev*)
   apply (rule equalityI)
    apply (rule subsetI)
    apply (erule thin_rl)
    apply (erule CollectE UN_E)+
    apply (drule length_Lev')
    apply (drule asm_rl)
    apply (erule thin_rl)
    apply (drule rev_subsetD[OF _ equalityD1])
     apply (rule trans[OF arg_cong[OF length_Cons]])
     apply (rule Lev_Suc)
    apply (erule CollectE exE conjE)+
    apply (tactic \<open>dtac @{context} @{thm list.inject[THEN iffD1]} 1\<close>)
    apply (erule conjE)
    apply (tactic \<open>dtac @{context}
  (Thm.permute_prems 0 2 @{thm tobd_JF_inj[THEN iffD1]}) 1\<close>)
      apply assumption
     apply assumption
    apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
    apply (erule UN_I[OF UNIV_I])

   apply (rule UN_least)
   apply (rule subsetI)
   apply (rule CollectI)
   apply (rule UN_I[OF UNIV_I])
   apply (rule subsetD[OF equalityD2])
    apply (rule Lev_Suc)
   apply (rule CollectI)
   apply (rule exI)+
   apply (rule conjI)
    apply (rule refl)
   apply (erule conjI)
   apply assumption
    (**)

  apply (rule trans)
   apply (rule shift_def)
  apply (rule iffD2)
   apply (rule fun_eq_iff)
  apply (rule allI)
  apply (tactic \<open>CONVERSION (Conv.top_conv
              (K (Conv.try_conv (Conv.rewr_conv (@{thm rv_Cons} RS eq_reflection)))) @{context}) 1\<close>)
  apply (drule frombd_F2_tobd_JF)
  apply (erule arg_cong)
  done

subsection \<open>Quotient Coalgebra\<close>

(* final coalgebra *)
definition car_final where
  "car_final \<equiv> carT // (lsbis carT strT)"
definition str_final where
  "str_final \<equiv> univ (Fmap id
    (Equiv_Relations.proj (lsbis carT strT)) o strT)"

lemma congruent_strQ: "congruent (lsbis carT strT :: 'a JT rel)
  (Fmap id (Equiv_Relations.proj (lsbis carT strT :: 'a JT rel)) o strT)"
  apply (rule congruentI)
  apply (drule lsbisE)
  apply (erule bexE conjE CollectE)+
  apply (rule trans[OF o_apply])
  apply (erule trans[OF arg_cong[OF sym]])
  apply (rule trans[OF Fmap_comp_id])
  apply (rule trans[OF F.map_cong0])
    apply (rule refl)
   apply (rule equiv_proj)
    apply (rule equiv_lsbis)
    apply (rule coalg_T)
   apply (erule subsetD)
   apply assumption
  apply (rule sym)
  apply (rule trans[OF o_apply])
  apply (erule trans[OF arg_cong[OF sym]])
  apply (rule Fmap_comp_id)
  done

lemma coalg_final:
  "coalg car_final str_final"
  unfolding car_final_def str_final_def
  apply (tactic \<open>rtac @{context} (@{thm coalg_def} RS iffD2) 1\<close>)
  apply (rule univ_preserves)
    apply (rule equiv_lsbis)
    apply (rule coalg_T)
   apply (rule congruent_strQ)
  apply (rule ballI)
  apply (rule ssubst_mem)
   apply (rule o_apply)
  apply (rule CollectI)
  apply (rule conjI)
   apply (rule subset_UNIV)
  apply (rule ord_eq_le_trans[OF F.set_map(2)])
  apply (rule image_subsetI)
  apply (rule iffD2)
   apply (rule proj_in_iff)
   apply (rule equiv_lsbis[OF coalg_T])
  apply (erule rev_subsetD)
  apply (erule coalg_Fset2[OF coalg_T])
  done

lemma mor_T_final:
  "mor carT strT car_final str_final
  (Equiv_Relations.proj (lsbis carT strT))"
  unfolding car_final_def str_final_def
   apply (tactic \<open>rtac @{context} (@{thm mor_def} RS iffD2) 1\<close>)
  apply (rule conjI)
   apply (rule ballI)
   apply (rule iffD2)
    apply (rule proj_in_iff)
    apply (rule equiv_lsbis[OF coalg_T])
   apply assumption

  apply (rule ballI)
  apply (rule sym)
  apply (rule trans)
   apply (rule univ_commute)
     apply (rule equiv_lsbis[OF coalg_T])
    apply (rule congruent_strQ)
   apply assumption
  apply (rule o_apply)
  done

lemmas mor_final = mor_comp[OF mor_beh mor_T_final]
lemmas in_car_final = mor_image'[OF mor_final UNIV_I]


(* The final coalgebra as a type *)

typedef (overloaded) 'a JF = "car_final :: 'a JT set set"
  by (rule exI) (rule in_car_final)

(* unfold & unfold *)
definition dtor where
  "dtor x = Fmap id Abs_JF (str_final (Rep_JF x))"

lemma mor_Rep_JF: "mor UNIV dtor car_final str_final Rep_JF"
  unfolding mor_def dtor_def
  apply (rule conjI)
   apply (rule ballI)
   apply (rule Rep_JF)

  apply (rule ballI)
  apply (rule trans[OF Fmap_comp_id])
  apply (rule Fmap_congL)
  apply (rule ballI)
  apply (rule trans[OF o_apply])
  apply (rule Abs_JF_inverse)
  apply (erule rev_subsetD)
  apply (rule coalg_Fset2)
   apply (rule coalg_final)
  apply (rule Rep_JF)
  done

lemma mor_Abs_JF: "mor car_final str_final UNIV dtor Abs_JF"
  unfolding mor_def dtor_def
  apply (rule conjI)
   apply (rule ballI)
   apply (rule UNIV_I)

  apply (rule ballI)
  apply (erule sym[OF arg_cong[OF Abs_JF_inverse]])
  done

definition unfold where
  "unfold s x =
     Abs_JF ((Equiv_Relations.proj (lsbis carT strT) o beh s) x)"

lemma mor_unfold:
  "mor UNIV s UNIV dtor (unfold s)"
  apply (rule iffD2)
   apply (rule mor_UNIV)
  apply (rule ext)
  apply (rule sym[OF trans[OF o_apply]])
  apply (rule trans[OF dtor_def])
  apply (rule trans[OF arg_cong[OF unfold_def]])
  apply (rule trans[OF arg_cong[OF Abs_JF_inverse[OF in_car_final]]])
  apply (rule trans[OF arg_cong[OF sym[OF morE[OF mor_final UNIV_I]]]])
  apply (rule trans[OF Fmap_comp_id])
  apply (rule sym[OF trans[OF o_apply]])
  apply (rule F.map_cong0)
   apply (rule refl)
  apply (rule trans[OF unfold_def])
  apply (rule sym[OF o_apply])
  done

lemmas unfold = sym[OF morE[OF mor_unfold UNIV_I]]

lemma JF_cind: "sbis UNIV dtor R \<Longrightarrow> R \<subseteq> Id"
  apply (rule rev_mp)
   apply (tactic \<open>forward_tac @{context} @{thms bis_def[THEN iffD1]} 1\<close>)
   apply (erule conjE)+
   apply (rule bis_cong)
    apply (rule bis_Comp)
     apply (rule bis_converse)
     apply (rule bis_Gr)
      apply (rule tcoalg)
     apply (rule mor_Rep_JF)
    apply (rule bis_Comp)
     apply assumption
    apply (rule bis_Gr)
     apply (rule tcoalg)
    apply (rule mor_Rep_JF)
   apply (erule relImage_Gr)

  apply (rule impI)
  apply (rule rev_mp)
   apply (rule bis_cong)
    apply (rule bis_Comp)
     apply (rule bis_Gr)
      apply (rule coalg_T)
     apply (rule mor_T_final)
    apply (rule bis_Comp)
     apply (rule sbis_lsbis)
    apply (rule bis_converse)
    apply (rule bis_Gr)
     apply (rule coalg_T)
    apply (rule mor_T_final)
   apply (rule relInvImage_Gr[OF lsbis_incl])

  apply (rule impI)
  unfolding car_final_def str_final_def
  apply (rule subset_trans)
   apply (rule relInvImage_UNIV_relImage)
  apply (rule subset_trans)
   apply (rule relInvImage_mono)
   apply (rule subset_trans)
    apply (erule incl_lsbis)
   apply (rule ord_eq_le_trans)
    apply (rule sym[OF relImage_relInvImage])
    apply (rule xt1(3))
     apply (rule Sigma_cong)
      apply (rule proj_image)
     apply (rule proj_image)
    apply (rule lsbis_incl)
   apply (rule subset_trans)
    apply (rule relImage_mono)
    apply (rule incl_lsbis)
    apply assumption
   apply (rule relImage_proj)
   apply (rule equiv_lsbis[OF coalg_T])
  apply (rule relInvImage_Id_on)
  apply (rule Rep_JF_inject)
  done

lemma unfold_unique_mor:
  "mor UNIV s UNIV dtor f \<Longrightarrow> f = unfold s"
  apply (rule ext)
  apply (erule IdD[OF subsetD[OF JF_cind[OF bis_image2[OF tcoalg _ tcoalg]]]])
   apply (rule mor_comp[OF mor_final mor_Abs_JF])
  apply (rule image2_eqI)
    apply (rule refl)
   apply (rule trans[OF arg_cong[OF unfold_def]])
   apply (rule sym[OF o_apply])
  apply (rule UNIV_I)
  done

lemmas unfold_unique = unfold_unique_mor[OF iffD2[OF mor_UNIV]]
lemmas unfold_dtor = sym[OF unfold_unique_mor[OF mor_id]]

lemmas unfold_o_dtor =
  trans[OF unfold_unique_mor[OF mor_comp[OF mor_str mor_unfold]] unfold_dtor]

(* the fold operator *)
definition ctor where "ctor = unfold (Fmap id dtor)"

lemma ctor_o_dtor:
  "ctor o dtor = id"
  unfolding ctor_def
  apply (rule unfold_o_dtor)
  done

lemma dtor_o_ctor:
  "dtor o ctor = id"
  unfolding ctor_def
  apply (rule ext)
  apply (rule trans[OF o_apply])
  apply (rule trans[OF unfold])
  apply (rule trans[OF Fmap_comp_id])
  apply (rule trans[OF Fmap_congL])
   apply (rule ballI)
   apply (rule trans[OF fun_cong[OF unfold_o_dtor] id_apply])
  apply (rule sym[OF id_apply])
  done


lemmas dtor_ctor = pointfree_idE[OF dtor_o_ctor]
lemmas ctor_dtor = pointfree_idE[OF ctor_o_dtor]

lemmas bij_dtor = o_bij[OF ctor_o_dtor dtor_o_ctor]
lemmas inj_dtor = bij_is_inj[OF bij_dtor]
lemmas surj_dtor = bij_is_surj[OF bij_dtor]
lemmas dtor_nchotomy = surjD[OF surj_dtor]
lemmas dtor_diff = inj_eq[OF inj_dtor]
lemmas dtor_cases = exE[OF dtor_nchotomy]

lemmas bij_ctor = o_bij[OF dtor_o_ctor ctor_o_dtor]
lemmas inj_ctor = bij_is_inj[OF bij_ctor]
lemmas surj_ctor = bij_is_surj[OF bij_ctor]
lemmas ctor_nchotomy = surjD[OF surj_ctor]
lemmas ctor_diff = inj_eq[OF inj_ctor]
lemmas ctor_cases = exE[OF ctor_nchotomy]

lemmas ctor_unfold = iffD1[OF dtor_diff trans[OF unfold sym[OF dtor_ctor]]]

(* corecursor: *)

definition corec where "corec s =
  unfold (case_sum (Fmap id Inl o dtor) s) o Inr"

lemma dtor_o_unfold: "dtor o unfold s = Fmap id (unfold s) o s"
  by (tactic \<open>rtac @{context} (BNF_Tactics.mk_pointfree2 @{context} @{thm unfold}) 1\<close>)

lemma corec_Inl_sum:
  "unfold (case_sum (Fmap id Inl \<circ> dtor) s) \<circ> Inl = id"
  apply (rule trans[OF unfold_unique unfold_dtor])
  apply (rule trans[OF arg_cong2[of _ _ _ _ "(o)", OF F.map_comp0[of id, unfolded id_o] refl]])
  apply (rule sym[OF trans[OF o_assoc]])
  apply (rule trans[OF arg_cong2[of _ _ _ _ "(o)", OF dtor_o_unfold refl]])
  apply (rule box_equals[OF _ o_assoc o_assoc])
  apply (rule arg_cong2[of _ _ _ _ "(o)", OF refl case_sum_o_inj(1)])
  done

lemma case_sum_expand_Inr: "f o Inl = g \<Longrightarrow> case_sum g (f o Inr) = f"
  by (auto split: sum.splits)

theorem corec:
  "dtor (corec s a) = Fmap id (case_sum id (corec s)) (s a)"
  unfolding corec_def o_apply unfold sum.case
    case_sum_expand_Inr[OF corec_Inl_sum] ..

lemma corec_unique:
  "Fmap id (case_sum id f) \<circ> s = dtor \<circ> f \<Longrightarrow> f = corec s"
  unfolding corec_def case_sum_expand_Inr'[OF corec_Inl_sum]
  apply (rule unfold_unique)
  apply (unfold o_case_sum id_o o_id F.map_comp0[symmetric]
      F.map_id0 o_assoc case_sum_o_inj(1))
  apply (erule arg_cong2[of _ _ _ _ case_sum, OF refl])
  done

subsection \<open>Coinduction\<close>

lemma Frel_coind:
  "\<lbrakk>\<forall>a b. phi a b \<longrightarrow> Frel (=) phi (dtor a) (dtor b)\<rbrakk> \<Longrightarrow> (phi a1 b1 \<longrightarrow> a1 = b1)"
  apply (rule rev_mp)
   apply (rule JF_cind)
   apply (rule iffD2)
    apply (rule bis_Frel)
   apply (rule conjI)

    apply (rule ord_le_eq_trans[OF subset_UNIV UNIV_Times_UNIV[THEN sym]])

   apply (rule allI)+
   apply (rule impI)
   apply (erule allE)+
   apply (rule predicate2D[OF eq_refl[OF arg_cong2[of _ _ _ _ "Frel"]]])
     apply (rule refl)
    apply (rule in_rel_Collect_case_prod_eq[symmetric])
   apply (erule mp)
   apply (erule CollectE)
   apply (erule case_prodD)

  apply (rule impI)

  apply (rule impI)
  apply (rule IdD)
  apply (erule subsetD)
  apply (rule CollectI)
  apply (erule case_prodI)
  done

subsection \<open>The Result as an BNF\<close>

abbreviation JFmap where
  "JFmap u \<equiv> unfold (Fmap u id o dtor)"

lemma JFmap: "dtor o JFmap u = Fmap u (JFmap u) o dtor"
  apply (rule ext)
  apply (rule sym[OF trans[OF o_apply]])
  apply (rule sym[OF trans[OF o_apply]])
  apply (rule trans[OF unfold])
  apply (rule box_equals[OF F.map_comp _ F.map_cong0, rotated])
    apply (rule fun_cong[OF id_o])
   apply (rule fun_cong[OF o_id])
  apply (rule sym[OF arg_cong[OF o_apply]])
  done

lemmas JFmap_simps = o_eq_dest[OF JFmap]

theorem JFmap_id: "JFmap id = id"
  apply (rule trans)
   apply (rule unfold_unique)
   apply (rule sym[OF JFmap])
  apply (rule unfold_dtor)
  done

lemma JFmap_unique:
  "\<lbrakk>dtor o u = Fmap f u o dtor\<rbrakk> \<Longrightarrow> u = JFmap f"
  apply (rule unfold_unique)
  unfolding o_assoc F.map_comp0[symmetric] id_o o_id
  apply (erule sym)
  done

theorem JFmap_comp: "JFmap (g o f) = JFmap g o JFmap f"
  apply (rule sym)
  apply (rule JFmap_unique)
  apply (rule trans[OF o_assoc])
  apply (rule trans[OF arg_cong2[of _ _ _ _ "(o)", OF JFmap refl]])
  apply (rule trans[OF sym[OF o_assoc]])
  apply (rule trans[OF arg_cong[OF JFmap]])
  apply (rule trans[OF o_assoc])
  apply (rule arg_cong2[of _ _ _ _ "(o)", OF sym[OF F.map_comp0] refl])
  done

(* The hereditary F-sets1: *)
definition JFcol where
  "JFcol = rec_nat (%a. {})
     (%n rec.
     (%a. Fset1 (dtor a) \<union>
       ((\<Union>a' \<in> Fset2 (dtor a). rec a'))))"

lemmas JFcol_0 = fun_cong[OF rec_nat_0_imp[OF JFcol_def]]
lemmas JFcol_Suc = fun_cong[OF rec_nat_Suc_imp[OF JFcol_def]]

lemma JFcol_minimal:
  "\<lbrakk>\<And>a. Fset1 (dtor a) \<subseteq> K1 a;
    \<And>a a'. a' \<in> Fset2 (dtor a) \<Longrightarrow> K1 a' \<subseteq> K1 a\<rbrakk> \<Longrightarrow>
  \<forall>a. JFcol n a \<subseteq> K1 a"
  apply (rule nat_induct)
   apply (rule allI)+
   apply (rule ord_eq_le_trans)
    apply (rule JFcol_0)
   apply (rule empty_subsetI)

  apply (rule allI)+
  apply (rule ord_eq_le_trans)
   apply (rule JFcol_Suc)
  apply (rule Un_least)
   apply assumption
  apply (rule UN_least)
  apply (erule allE conjE)+
  apply (rule subset_trans)
   apply assumption
  apply assumption
  done

lemma JFset_minimal:
  "\<lbrakk>\<And>a. Fset1 (dtor a) \<subseteq> K1 a;
    \<And>a a'. a' \<in> Fset2 (dtor a) \<Longrightarrow> K1 a' \<subseteq> K1 a\<rbrakk> \<Longrightarrow>
  (\<Union>n. JFcol n a) \<subseteq> K1 a"
  apply (rule UN_least)
  apply (rule rev_mp)
   apply (rule JFcol_minimal)
    apply assumption
   apply assumption
  apply (rule impI)
  apply (erule allE conjE)+
  apply assumption
  done

abbreviation JFset where "JFset a \<equiv> (\<Union>n. JFcol n a)"

lemma Fset1_incl_JFset:
  "Fset1 (dtor a) \<subseteq> JFset a"
  apply (rule SUP_upper2)
   apply (rule UNIV_I)
  apply (rule ord_le_eq_trans)
   apply (rule Un_upper1)
  apply (rule sym)
  apply (rule JFcol_Suc)
  done


lemma Fset2_JFset_incl_JFset:
  "a' \<in> Fset2 (dtor a) \<Longrightarrow> JFset a' \<subseteq> JFset a"
  apply (rule UN_least)
  apply (rule subsetI)
  apply (rule UN_I)
   apply (rule UNIV_I)
  apply (rule subsetD)
   apply (rule equalityD2)
   apply (rule JFcol_Suc)
  apply (rule UnI2)
  apply (erule UN_I)
  apply assumption
  done


lemmas Fset1_JFset = subsetD[OF Fset1_incl_JFset]
lemmas Fset2_JFset_JFset = subsetD[OF Fset2_JFset_incl_JFset]

lemma JFset_le:
  fixes a :: "'a JF"
  shows
    "JFset a \<subseteq> Fset1 (dtor a) \<union> (\<Union> (JFset ` Fset2 (dtor a)))"
  apply (rule JFset_minimal)
   apply (rule Un_upper1)
  apply (rule subsetI)
  apply (rule UnI2)
  apply (erule UN_I)
  apply (erule UnE)
   apply (erule Fset1_JFset)
  apply (erule UN_E)
  apply (erule Fset2_JFset_JFset)
  apply assumption
  done

theorem JFset_simps:
  "JFset a = Fset1 (dtor a) \<union>
    ((\<Union> b \<in> Fset2 (dtor a). JFset b))"
  apply (rule equalityI)
   apply (rule JFset_le)
  apply (rule Un_least)
   apply (rule Fset1_incl_JFset)
  apply (rule UN_least)
  apply (erule Fset2_JFset_incl_JFset)
  done

lemma JFcol_natural:
  "\<forall>b1. u ` (JFcol n b1) = JFcol n (JFmap u b1)"
  apply (rule nat_induct)
   apply (rule allI)+
  unfolding JFcol_0
   apply (rule image_empty)

  apply (rule allI)+
  apply (unfold JFcol_Suc JFmap_simps image_Un image_UN UN_simps(10)
      F.set_map(1) F.set_map(2)) [1]
  apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])
   apply (rule refl)
  apply (rule SUP_cong[OF refl])
  apply (erule allE)+
  apply assumption
  done

theorem JFset_natural: "JFset o (JFmap u) = image u o JFset"
  apply (rule ext)
  apply (rule trans[OF o_apply])
  apply (rule sym)
  apply (rule trans[OF o_apply])
  apply (rule trans[OF image_UN])
  apply (rule SUP_cong[OF refl])
  apply (rule spec[OF JFcol_natural])
  done

theorem JFmap_cong0:
  "((\<forall>p \<in> JFset a. u p = v p) \<longrightarrow> JFmap u a = JFmap v a)"
  apply (rule rev_mp)
   apply (rule Frel_coind[of
        "%b c. \<exists>a. a \<in> {a. \<forall>p \<in> JFset a. u p = v p} \<and> b = JFmap u a \<and> c = JFmap v a"])
   apply (intro allI impI iffD2[OF F.in_rel])

   apply (erule exE conjE)+
   apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
   apply (rule exI)

   apply (rule conjI[rotated])
    apply (rule conjI)
     apply (rule trans[OF F.map_comp])
     apply (rule sym)
     apply (rule trans[OF JFmap_simps])
     apply (rule F.map_cong0)
      apply (rule sym[OF trans[OF o_apply]])
      apply (rule fst_conv)
     apply (rule sym[OF fun_cong[OF fst_convol[unfolded convol_def]]])

    apply (rule trans[OF F.map_comp])
    apply (rule sym)
    apply (rule trans[OF JFmap_simps])
    apply (rule F.map_cong0)
     apply (rule sym[OF trans[OF o_apply]])
     apply (rule trans[OF snd_conv])
     apply (erule CollectE)
     apply (erule bspec)
     apply (erule Fset1_JFset)
    apply (rule sym[OF fun_cong[OF snd_convol[unfolded convol_def]]])

   apply (rule CollectI)
   apply (rule conjI)
    apply (rule ord_eq_le_trans)
     apply (rule F.set_map(1))
    apply (rule image_subsetI)
    apply (rule CollectI)
    apply (rule case_prodI)
    apply (rule refl)

   apply (rule ord_eq_le_trans)
    apply (rule F.set_map(2))
   apply (rule image_subsetI)
   apply (rule CollectI)
   apply (rule case_prodI)
   apply (rule exI)
   apply (rule conjI)
    apply (rule CollectI)
    apply (rule ballI)
    apply (erule CollectE)
    apply (erule bspec)
    apply (erule Fset2_JFset_JFset)
    apply assumption
   apply (rule conjI[OF refl refl])

(**)

  apply (rule impI)

  apply (rule impI)
  apply (erule mp)
  apply (rule exI)
  apply (rule conjI)
   apply (erule CollectI)
  apply (rule conjI)
   apply (rule refl)
  apply (rule refl)
  done

lemmas JFmap_cong = mp[OF JFmap_cong0]

lemma JFcol_bd: "\<forall>(j1 :: 'a JF). |JFcol n j1| \<le>o bd_JF"
  apply (rule nat_induct)
   apply (rule allI)+
   apply (rule ordIso_ordLeq_trans)
    apply (rule card_of_ordIso_subst)
    apply (rule JFcol_0)
   apply (rule Card_order_empty)
   apply (rule bd_F_Card_order)

  apply (rule allI)+
  apply (rule ordIso_ordLeq_trans)
   apply (rule card_of_ordIso_subst)
   apply (rule JFcol_Suc)
  apply (rule Un_Cinfinite_bound)
    apply (rule Fset1_bd')
   apply (rule UNION_Cinfinite_bound)
     apply (rule Fset2_bd')
    apply (rule ballI)
    apply (erule allE)+
    apply assumption
   apply (rule bd_F_Cinfinite)
  apply (rule bd_F_Cinfinite)
  done

theorem JFset_bd: "|JFset j| \<le>o bd_JF"
  apply (rule UNION_Cinfinite_bound)
    apply (rule ordIso_ordLeq_trans)
     apply (rule card_of_nat)
    apply (rule natLeq_ordLeq_cinfinite)
    apply (rule bd_F_Cinfinite)
   apply (rule ballI)
   apply (rule spec[OF JFcol_bd])
  apply (rule bd_F_Cinfinite)
  done

abbreviation "JFwit \<equiv> ctor wit_F"

theorem JFwit: "\<And>x. x \<in> JFset JFwit \<Longrightarrow> False"
  apply (drule rev_subsetD)
   apply (rule equalityD1)
   apply (rule JFset_simps)
  unfolding dtor_ctor
  apply (erule UnE)
   apply (erule F.wit)
  apply (erule UN_E)
  apply (erule F.wit)
  done

(* Additions: *)

context
  fixes phi :: "'a \<Rightarrow> 'a JF \<Rightarrow> bool"
begin

lemmas JFset_induct =
  JFset_minimal[of "%b1. {a \<in> JFset b1 . phi a b1}",
    unfolded subset_Collect_iff[OF Fset1_incl_JFset]
    subset_Collect_iff[OF subset_refl],
    OF ballI
    subset_CollectI[OF Fset2_JFset_incl_JFset]]

end

(*export that one!*)
ML \<open>rule_by_tactic @{context} (ALLGOALS (TRY o etac @{context} asm_rl)) @{thm JFset_induct}\<close>

(* Compositionality of relators *)

abbreviation JFin where "JFin B \<equiv> {a. JFset a \<subseteq> B}"

(* Notions and facts that make sense for any BNF: *)
definition JFrel where
  "JFrel R = (BNF_Def.Grp (JFin (Collect (case_prod R))) (JFmap fst))^--1 OO
              (BNF_Def.Grp (JFin (Collect (case_prod R))) (JFmap snd))"

lemma in_JFrel:
  "JFrel R x y \<longleftrightarrow> (\<exists> z. z \<in> JFin (Collect (case_prod R)) \<and> JFmap fst z = x \<and> JFmap snd z = y)"
  by (rule predicate2_eqD[OF trans[OF JFrel_def OO_Grp_alt]])

lemma J_rel_coind_ind:
  "\<lbrakk>\<forall>x y. R2 x y \<longrightarrow> (f x y \<in> Fin (Collect (case_prod R1)) (Collect (case_prod R2)) \<and>
                               Fmap fst fst (f x y) = dtor x \<and>
                               Fmap snd snd (f x y) = dtor y)\<rbrakk> \<Longrightarrow>
  (\<forall>a\<in>JFset z1. \<forall>x y. R2 x y \<and> z1 = unfold (case_prod f) (x, y) \<longrightarrow> R1 (fst a) (snd a))"
  apply (tactic \<open>rtac @{context} (rule_by_tactic @{context} (ALLGOALS (TRY o etac @{context} asm_rl))
  @{thm JFset_induct[of
  "\<lambda>a z1. \<forall>x y. R2 x y \<and> z1 = unfold (case_prod f) (x, y) \<longrightarrow> R1 (fst a) (snd a)"
  z1]}) 1\<close>)
   apply (rule allI impI)+
   apply (erule conjE)
   apply (drule spec2)
   apply (drule mp)
    apply assumption
   apply (erule CollectE conjE Collect_case_prodD[OF subsetD] rev_subsetD)+
   apply hypsubst
  unfolding unfold F.set_map(1) prod.case image_id id_apply
   apply (rule subset_refl)

(**)

  apply (rule impI allI)+
  apply (erule conjE)
  apply (drule spec2)
  apply (drule mp)
   apply assumption
  apply (erule CollectE conjE)+
  apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
  unfolding unfold F.set_map(2) prod.case image_id id_apply
  apply (erule imageE)
  apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
  apply (erule allE mp)+
  apply (rule conjI)
   apply (erule Collect_case_prodD[OF subsetD])
   apply assumption
  apply (rule arg_cong[OF surjective_pairing])
  done

lemma J_rel_coind_coind1:
  "\<lbrakk>\<forall>x y. R2 x y \<longrightarrow> (f x y \<in> Fin (Collect (case_prod R1)) (Collect (case_prod R2)) \<and>
                               Fmap fst fst (f x y) = dtor x \<and>
                               Fmap snd snd (f x y) = dtor y)\<rbrakk> \<Longrightarrow>
  ((\<exists>y. R2 x1 y \<and> x1' = JFmap fst (unfold (case_prod f) (x1, y))) \<longrightarrow> x1' = x1)"
  apply (rule Frel_coind[of
        "\<lambda>x1' x1. \<exists>y. R2 x1 y \<and> x1' = JFmap fst (unfold (case_prod f) (x1, y))"
        x1' x1
        ])
  apply (intro allI impI iffD2[OF F.in_rel])

  apply (erule exE conjE)+
  apply (drule spec2)
  apply (drule mp)
   apply assumption
  apply (erule CollectE conjE)+
  apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
  apply (rule exI)
  apply (rule conjI[rotated])
   apply (rule conjI)
    apply (rule trans[OF F.map_comp])
    apply (rule sym[OF trans[OF JFmap_simps]])
    apply (rule trans[OF arg_cong[OF unfold]])
    apply (rule trans[OF F.map_comp F.map_cong0])
     apply (rule trans[OF fun_cong[OF o_id]])
     apply (rule sym[OF fun_cong[OF fst_diag_fst]])
    apply (rule sym[OF trans[OF o_apply]])
    apply (rule fst_conv)
   apply (rule trans[OF F.map_comp])
   apply (rule trans[OF F.map_cong0])
     apply (rule fun_cong[OF snd_diag_fst])
    apply (rule trans[OF o_apply])
    apply (rule snd_conv)
   apply (erule trans[OF arg_cong[OF prod.case]])

  apply (unfold prod.case o_def fst_conv snd_conv) []
  apply (rule CollectI)
  apply (rule conjI)
   apply (rule ord_eq_le_trans[OF F.set_map(1)])
   apply (rule image_subsetI CollectI case_prodI)+
   apply (rule refl)

  apply (rule ord_eq_le_trans[OF F.set_map(2)])
  apply (rule image_subsetI CollectI case_prodI exI)+
  apply (rule conjI)
   apply (erule Collect_case_prodD[OF subsetD])
   apply assumption
  apply (rule arg_cong[OF surjective_pairing])
  done

lemma J_rel_coind_coind2:
  "\<lbrakk>\<forall>x y. R2 x y \<longrightarrow> (f x y \<in> Fin (Collect (case_prod R1)) (Collect (case_prod R2)) \<and>
                               Fmap fst fst (f x y) = dtor x \<and>
                               Fmap snd snd (f x y) = dtor y)\<rbrakk> \<Longrightarrow>
  ((\<exists>x. R2 x y1 \<and> y1' = JFmap snd (unfold (case_prod f) (x, y1))) \<longrightarrow> y1' = y1)"
  apply (rule Frel_coind[of
        "\<lambda>y1' y1. \<exists>x. R2 x y1 \<and> y1' = JFmap snd (unfold (case_prod f) (x, y1))"
        y1' y1
        ])
  apply (intro allI impI iffD2[OF F.in_rel])

  apply (erule exE conjE)+
  apply (drule spec2)
  apply (drule mp)
   apply assumption
  apply (erule CollectE conjE)+
  apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
  apply (rule exI)
  apply (rule conjI[rotated])
   apply (rule conjI)
    apply (rule trans[OF F.map_comp])
    apply (rule sym[OF trans[OF JFmap_simps]])
    apply (rule trans[OF arg_cong[OF unfold]])
    apply (rule trans[OF F.map_comp F.map_cong0])
     apply (rule trans[OF fun_cong[OF o_id]])
     apply (rule sym[OF fun_cong[OF fst_diag_snd]])
    apply (rule sym[OF trans[OF o_apply]])
    apply (rule fst_conv)
   apply (rule trans[OF F.map_comp])
   apply (rule trans[OF F.map_cong0])
     apply (rule fun_cong[OF snd_diag_snd])
    apply (rule trans[OF o_apply])
    apply (rule snd_conv)
   apply (erule trans[OF arg_cong[OF prod.case]])

  apply (unfold prod.case o_def fst_conv snd_conv) []
  apply (rule CollectI)
  apply (rule conjI)
   apply (rule ord_eq_le_trans[OF F.set_map(1)])
   apply (rule image_subsetI CollectI case_prodI)+
   apply (rule refl)

  apply (rule ord_eq_le_trans[OF F.set_map(2)])
  apply (rule image_subsetI CollectI case_prodI exI)+
  apply (rule conjI)
   apply (erule Collect_case_prodD[OF subsetD])
   apply assumption
  apply (rule arg_cong[OF surjective_pairing])
  done

lemma J_rel_coind:
  assumes CIH1: "\<forall>x2 y2. R2 x2 y2 \<longrightarrow> Frel R1 R2 (dtor x2) (dtor y2)"
  shows   "R2 \<le> JFrel R1"
  apply (insert CIH1)
  unfolding F.in_rel ex_simps(6)[symmetric] choice_iff
  apply (erule exE)+

  apply (rule predicate2I)
  apply (rule iffD2[OF in_JFrel])
  apply (rule exI conjI)+
   apply (rule CollectI)
   apply (rule rev_mp[OF J_rel_coind_ind])
    apply assumption
   apply (erule thin_rl)
   apply (rule impI)
   apply (rule subsetI CollectI iffD2[OF case_prod_beta])+
   apply (drule bspec)
    apply assumption
   apply (erule allE mp conjE)+
   apply (erule conjI[OF _ refl])

  apply (rule conjI)
   apply (rule rev_mp[OF J_rel_coind_coind1])
    apply assumption
   apply (erule thin_rl)
   apply (rule impI)
   apply (erule mp)
   apply (rule exI)
   apply (erule conjI[OF _ refl])

  apply (rule rev_mp[OF J_rel_coind_coind2])
   apply assumption
  apply (erule thin_rl)
  apply (rule impI)
  apply (erule mp)
  apply (rule exI)
  apply (erule conjI[OF _ refl])
  done

lemma JFrel_Frel: "JFrel R a b \<longleftrightarrow> Frel R (JFrel R) (dtor a) (dtor b)"
  apply (rule iffI)
   apply (drule iffD1[OF in_JFrel])
   apply (erule exE conjE CollectE)+
   apply (rule iffD2[OF F.in_rel])
   apply (rule exI)
   apply (rule conjI)
    apply (rule CollectI)
    apply (rule conjI)
     apply (rule ord_eq_le_trans)
      apply (rule F.set_map(1))
     apply (rule ord_eq_le_trans)
      apply (rule trans[OF fun_cong[OF image_id] id_apply])
     apply (erule subset_trans[OF Fset1_incl_JFset])

    apply (rule ord_eq_le_trans)
     apply (rule F.set_map(2))
    apply (rule image_subsetI)
    apply (rule CollectI)
    apply (rule case_prodI)
    apply (rule iffD2[OF in_JFrel])
    apply (rule exI)
    apply (rule conjI)
     apply (rule CollectI)
     apply (erule subset_trans[OF Fset2_JFset_incl_JFset])
     apply assumption
    apply (rule conjI)
     apply (rule refl)
    apply (rule refl)

   apply (rule conjI)

    apply (rule trans)
     apply (rule F.map_comp)
    apply (rule trans)
     apply (rule F.map_cong0)
      apply (rule fun_cong[OF o_id])
     apply (rule trans)
      apply (rule o_apply)
     apply (rule fst_conv)
    apply (rule trans)
     apply (rule sym)
     apply (rule JFmap_simps)
    apply (rule iffD2[OF dtor_diff])
    apply assumption

   apply (rule trans)
    apply (rule F.map_comp)
   apply (rule trans)
    apply (rule F.map_cong0)
     apply (rule fun_cong[OF o_id])
    apply (rule trans)
     apply (rule o_apply)
    apply (rule snd_conv)
   apply (rule trans)
    apply (rule sym)
    apply (rule JFmap_simps)
   apply (rule iffD2[OF dtor_diff])
   apply assumption

  apply (drule iffD1[OF F.in_rel])
  apply (erule exE conjE CollectE)+
  apply (rule iffD2[OF in_JFrel])
  apply (rule exI)
  apply (rule conjI)
   apply (rule CollectI)
   apply (rule ord_eq_le_trans)
    apply (rule JFset_simps)
   apply (rule Un_least)
    apply (rule ord_eq_le_trans)
     apply (rule box_equals)
       apply (rule F.set_map(1))
      apply (rule arg_cong[OF sym[OF dtor_ctor]])
     apply (rule trans[OF fun_cong[OF image_id] id_apply])
    apply assumption
   apply (rule ord_eq_le_trans)
    apply (rule SUP_cong[OF _ refl])
    apply (rule box_equals[OF _ _ refl])
     apply (rule F.set_map(2))
    apply (rule arg_cong[OF sym[OF dtor_ctor]])
   apply (rule UN_least)
   apply (drule rev_subsetD)
    apply (erule image_mono)
   apply (erule imageE)
   apply (drule ssubst_mem[OF surjective_pairing[symmetric]])
   apply (erule CollectE case_prodE iffD1[OF prod.inject, elim_format] conjE)+
   apply hypsubst
   apply (drule iffD1[OF in_JFrel])
   apply (drule someI_ex)
   apply (erule conjE)+
   apply (erule CollectE conjE)+
   apply assumption

  apply (rule conjI)

   apply (rule iffD1[OF dtor_diff])
   apply (rule trans)
    apply (rule JFmap_simps)
   apply (rule box_equals)
     apply (rule F.map_comp)
    apply (rule arg_cong[OF sym[OF dtor_ctor]])
   apply (rule trans)
    apply (rule F.map_cong0)
     apply (rule fun_cong[OF o_id])
    apply (rule trans[OF o_apply])
    apply (drule rev_subsetD)
     apply assumption
    apply (drule ssubst_mem[OF surjective_pairing[symmetric]])
    apply (erule CollectE case_prodE iffD1[OF prod.inject, elim_format] conjE)+
    apply hypsubst
    apply (drule iffD1[OF in_JFrel])
    apply (drule someI_ex)
    apply (erule conjE)+
    apply assumption
   apply assumption

  apply (rule iffD1[OF dtor_diff])
  apply (rule trans)
   apply (rule JFmap_simps)
  apply (rule trans)
   apply (rule arg_cong[OF dtor_ctor])
  apply (rule trans)
   apply (rule F.map_comp)
  apply (rule trans)
   apply (rule F.map_cong0)
    apply (rule fun_cong[OF o_id])
   apply (rule trans[OF o_apply])
   apply (drule rev_subsetD)
    apply assumption
   apply (drule ssubst_mem[OF surjective_pairing[symmetric]])
   apply (erule CollectE case_prodE iffD1[OF prod.inject, elim_format] conjE)+
   apply hypsubst
   apply (drule iffD1[OF in_JFrel])
   apply (drule someI_ex)
   apply (erule conjE)+
   apply assumption
  apply assumption
  done

lemma JFrel_Comp_le:
  "JFrel R1 OO JFrel R2 \<le> JFrel (R1 OO R2)"
  apply (rule J_rel_coind[OF allI[OF allI[OF impI]]])
  apply (rule predicate2D[OF eq_refl[OF sym[OF F.rel_compp]]])
  apply (erule relcomppE)
  apply (rule relcomppI)
   apply (erule iffD1[OF JFrel_Frel])
  apply (erule iffD1[OF JFrel_Frel])
  done

context includes lifting_syntax
begin

lemma unfold_transfer:
  "((S ===> Frel R S) ===> S ===> JFrel R) unfold unfold"
  unfolding rel_fun_def_butlast all_conj_distrib[symmetric] imp_conjR[symmetric]
  unfolding rel_fun_iff_geq_image2p
  apply (rule allI impI)+
  apply (rule J_rel_coind)
  apply (rule allI impI)+
  apply (erule image2pE)
  apply hypsubst
  apply (unfold unfold) [1]
  apply (rule rel_funD[OF rel_funD[OF rel_funD[OF F.map_transfer]]])
    apply (rule id_transfer)
   apply (rule rel_fun_image2p)
  apply (erule predicate2D)
  apply (erule image2pI)
  done

end

ML \<open>
  BNF_FP_Util.mk_xtor_co_iter_o_map_thms BNF_Util.Greatest_FP false 1 @{thm unfold_unique}
    @{thms JFmap} (map (BNF_Tactics.mk_pointfree2 @{context}) @{thms unfold})
    @{thms F.map_comp0[symmetric]} @{thms F.map_cong0}
\<close>

ML \<open>
  BNF_FP_Util.mk_xtor_co_iter_o_map_thms BNF_Util.Greatest_FP true 1 @{thm corec_unique}
    @{thms JFmap} (map (BNF_Tactics.mk_pointfree2 @{context}) @{thms corec})
    @{thms F.map_comp0[symmetric]} @{thms F.map_cong0}
\<close>

bnf "'a JF"
  map: JFmap
  sets: JFset
  bd: bd_JF
  wits: JFwit
  rel: JFrel
           apply -
           apply (rule JFmap_id)
          apply (rule JFmap_comp)
         apply (erule JFmap_cong[OF ballI])
        apply (rule JFset_natural)
       apply (rule bd_F_card_order)
      apply (rule conjunct1[OF bd_F_Cinfinite])
     apply (rule JFset_bd)
    apply (rule JFrel_Comp_le)
   apply (rule JFrel_def[unfolded OO_Grp_alt mem_Collect_eq])
  apply (erule JFwit)
  done


(**********)
(* Codatatypes are wide with their standard relators! *)

(* Preliminaries: *)  

declare Product_Type.split_paired_Ex[simp del]


lemmas is_car_final = coalg_final 

lemma car_final_ne: "\<exists>ii. ii \<in> car_final" 
	using Rep_JF by blast  

lemma carT_ne: "\<exists>i. i \<in> carT" using car_final_ne unfolding car_final_def
	using coalg_T equiv_Eps_preserves equiv_lsbis by blast  

(* *)
inductive_set Purged :: 
"(bd_type_JF list \<Rightarrow> ('a, bd_type_JF) F) \<Rightarrow> bd_type_JF list set "
for lab where 
"[] \<in> Purged lab"
|
"kl \<in> Purged lab \<Longrightarrow> k \<in> Fset2 (lab kl) \<Longrightarrow> kl@[k] \<in> Purged lab"

lemma Purged_Shift_shift: 
"k \<in> Fset2 (lab [])  \<Longrightarrow>
 Purged (shift lab k) = Shift (Purged lab) k"
apply safe
  subgoal for kl
  apply rotate_tac apply(induct rule: Purged.induct)
    apply auto  
    apply (meson SuccI empty_Shift Purged.simps)
    by (metis ShiftD SuccD SuccI Succ_Shift shift_def Purged.intros(2))
  subgoal for kl
  apply(induct kl rule: rev_induct)
   apply auto  
    using Purged.intros(1) apply blast
    by (metis (no_types, lifting) Shift_def shift_def Purged.simps butlast.simps(2) 
     butlast_snoc last.simps last_snoc list.distinct(1) mem_Collect_eq) .

lemma Purged_back: "kl @ [k] \<in> Purged lab \<Longrightarrow> kl \<in> Purged lab"
apply(induct kl arbitrary: k rule: rev_induct) apply (auto intro!: Purged.intros) 
  apply (metis Purged.simps append_is_Nil_conv butlast.simps(2) butlast_append butlast_snoc) 
  by (metis Purged.simps append_is_Nil_conv butlast.simps(2) butlast_append butlast_snoc last_snoc list.distinct(1))

lemma Purged_incl: 
assumes c: "(Kl,lab) \<in> carT"
shows "Purged lab \<subseteq> Kl"
apply safe subgoal for kl proof(induction kl rule: length_induct)
		case (1 klll) note 0 = 1 note IH = 0(1)
		from 0(2) show ?case proof(cases rule: Purged.cases)
			case 1
			then show ?thesis using c unfolding carT_def by auto
		next
			case (2 kll k)
      have c2: "\<forall>kl\<in>Kl. \<forall>k1. kl @ [k1] \<in> Kl \<longrightarrow> Fset2 (lab (kl @ [k1])) = {k. kl @ [k1, k] \<in> Kl}"
         and c1: "Fset2 (lab []) = {k. [k] \<in> Kl}" 
      using c unfolding isNode_def carT_def Succ_def by auto
			show ?thesis proof(cases kll rule: rev_cases)
				case Nil
				show ?thesis using c1 2(3) unfolding 2(1) Nil by auto
			next
				case (snoc kl k1)
        note kll = `kll \<in> Purged lab`
        have kl: "kl \<in> Purged lab" using kll unfolding snoc  
        	using Purged_back by blast
        have kll: "kll \<in> Kl" using IH[rule_format, OF _ kll] unfolding 2(1) by auto
        have kl: "kl \<in> Kl" using IH[rule_format, OF _ kl] unfolding snoc 2(1) by auto
				show ?thesis using c2 kl kll 2(3) unfolding 2(1) snoc by auto
			qed
		qed
	qed .

lemma Purged_carT[simp,intro]: 
"(Purged lab,lab) \<in> carT"
unfolding carT_def apply (auto intro!: Purged.intros simp: isNode_def Succ_def)
   using Purged.simps apply fastforce
   apply (metis Purged.simps append_is_Nil_conv butlast.simps(2) 
  butlast_append butlast_snoc last.simps last_appendR list.distinct(1))
  apply (metis Purged.intros(1) Purged.intros(2) append.left_neutral)
  using Purged.cases by force

(* *)

inductive isPurged :: 
"(bd_type_JF list \<Rightarrow> ('a, bd_type_JF) F) \<Rightarrow> bd_type_JF list \<Rightarrow> bool"
where
"isPurged lab []"
|
"k \<in> Fset2 (lab []) \<Longrightarrow> isPurged (\<lambda>kl. lab (k # kl)) kl \<Longrightarrow> isPurged lab (k # kl)"

lemma isPurged_append_Fset2: "isPurged lab kl \<Longrightarrow> k \<in> Fset2 (lab kl) \<Longrightarrow> isPurged lab (kl @ [k])"
apply(induct rule: isPurged.induct)
  apply auto 
  apply (meson isPurged.simps)  
  using isPurged.intros(2) by blast

lemma Purged_implies_isPurged: 
"kl \<in> Purged lab \<Longrightarrow> isPurged lab kl"
apply(induct kl rule: Purged.induct)
  subgoal by (simp add: isPurged.intros(1))
  subgoal by (simp add: isPurged_append_Fset2) .

lemma isPurged_implies_Purged: 
"isPurged lab kl \<Longrightarrow> kl \<in> Purged (\<lambda>kl. lab (kl))"
apply(induct kl rule: isPurged.induct)
  subgoal by (simp add: Purged.intros(1))
  subgoal using Purged_Shift_shift unfolding shift_def Shift_def by auto .

lemma Purged_eq_isPurged: "Purged lab = Collect (isPurged lab)"
by (metis Collect_cong Collect_mem_eq Purged_implies_isPurged isPurged_implies_Purged)

(* *) 

definition "purgeLab R Kl lab \<equiv> \<lambda>kl. if kl \<in> Kl then lab kl else (SOME x. Frel R (=) x x)"

lemma purgeLab_carT: "(Kl,lab) \<in> carT \<Longrightarrow> (Kl,purgeLab R Kl lab) \<in> carT"
unfolding carT_def isNode_def Succ_def purgeLab_def by auto

lemma purgeLab_purgeLab[simp]: "purgeLab R Kl (purgeLab R Kl lab) = purgeLab R Kl lab"
unfolding purgeLab_def by auto

lemma in_purgeLab[simp]: "kl \<in> Kl \<Longrightarrow> purgeLab R Kl lab kl = lab kl"
unfolding purgeLab_def by auto

lemma notin_purgeLab[simp]: "kl \<notin> Kl \<Longrightarrow> purgeLab R Kl lab kl = (SOME x. Frel R (=) x x)"
unfolding purgeLab_def by auto

(* *)

definition 
"cleancarT R = {(Purged lab, purgeLab R (Purged lab) lab) | Kl lab. (Kl,lab) \<in> carT}"

lemma cleancarT_carT: "cleancarT R \<subseteq> carT"
by (smt (verit, best) Purged_carT cleancarT_def mem_Collect_eq purgeLab_carT subsetI)

lemma Purged_purgeLab[simp]: "Purged (purgeLab R (Purged lab) lab) = Purged lab"
apply safe
subgoal for kl apply(induct rule: Purged.induct) by (auto intro: Purged.intros)
subgoal for kl apply(induct rule: Purged.induct) by (auto intro: Purged.intros) .

lemma cleancarT_implies_Purged: "(Kl,lab) \<in> cleancarT R \<Longrightarrow> Kl = Purged lab"
unfolding cleancarT_def by auto

lemma cleancarT_implies_lab: 
assumes c: "(Kl,lab) \<in> cleancarT R" and kl: "kl \<notin> Kl" 
shows "lab kl = (SOME x. Frel R (=) x x)" 
using c kl unfolding cleancarT_def apply safe apply(rule notin_purgeLab) by auto

proposition cleancarT_iff: 
"(Kl,lab) \<in> cleancarT R \<longleftrightarrow> (Kl = Purged lab \<and> (\<forall>kl. kl \<notin> Kl \<longrightarrow> lab kl = (SOME x. Frel R (=) x x)))"
apply standard
  subgoal using cleancarT_implies_Purged cleancarT_implies_lab by blast
  subgoal unfolding cleancarT_def apply auto apply(intro exI[of _ Kl] exI[of _ lab]) 
  unfolding purgeLab_def by auto . 

(* *)

thm J_rel_coind
lemmas JFrel_coinduct2 = J_rel_coind[unfolded le_fun_def le_bool_def, rule_format, rotated]

lemma JFrel_coinduct[consumes 1]: 
assumes "R ii ii'"
"(\<And>x x'.  R x x' \<Longrightarrow> Frel (=) R (dtor x) (dtor x'))"
shows "ii = ii'" 
using JFrel_coinduct2[OF assms]  
by (simp add: JF.rel_eq)

declare JF.Rep_JF[simp,intro!]
declare Abs_JF_inverse[simp]
declare Rep_JF_inverse[simp]
declare Abs_JF_inject[simp]
 
lemma car_final_coinduct[consumes 1]: 
assumes 0: "ii \<in> car_final" "ii' \<in> car_final" "Q ii ii'" and 
1: "(\<And>i i'. i \<in> car_final \<Longrightarrow> i' \<in> car_final \<Longrightarrow> Q i i' \<Longrightarrow> Frel (=) Q (str_final i) (str_final i'))"
shows "ii = ii'" 
proof-
  have "Abs_JF ii = Abs_JF ii'"
  apply(rule JFrel_coinduct[of "\<lambda>i i'. Q (Rep_JF i) (Rep_JF i')"])
    subgoal using 0 by simp
    subgoal for i i' using 1[of "Rep_JF i" "Rep_JF i'"] apply (auto simp: dtor_def)
    unfolding F.rel_map apply simp
    apply(drule F.rel_mono_strong)  
    by auto (metis (mono_tags, opaque_lifting) Abs_JF_inverse Rep_JF coalg_Fset2 is_car_final subsetD) .
  thus ?thesis using 0 by auto
qed 

lemma str_final_inj: 
"i \<in> car_final \<Longrightarrow> j \<in> car_final \<Longrightarrow> 
 str_final i = str_final j \<Longrightarrow> i = j" 
by (metis Abs_JF_inject dtor_diff morE mor_Abs_JF)

lemma str_final_inj': "i \<in> car_final \<Longrightarrow>
  i' \<in> car_final \<Longrightarrow> str_final i = str_final i' \<longleftrightarrow> i = i'"
using str_final_inj by auto 

lemma str_final_surj: 
"Fset2 y \<subseteq> car_final \<Longrightarrow> \<exists>ii. ii \<in> car_final \<and> y = str_final ii"
using surj_dtor unfolding surj_def ctor_def apply - apply(erule allE[of _ "Fmap id Abs_JF y"])
apply safe subgoal for i  apply(rule exI[of _ "Rep_JF i"])
	by (smt (verit, ccfv_threshold) Abs_JF_inject F.inj_map_strong 
  Rep_JF coalg_def dtor_def id_apply is_car_final mem_Collect_eq subsetD) .

declare prod.rrel_neper[simp]

(* *)

term "lsbis carT strT"

thm car_final_def
thm lsbis_def
thm bis_def[no_vars]

coinductive mybis :: "('a JT \<Rightarrow> 'a JT \<Rightarrow> bool)"  
where 
"ii\<in>carT \<Longrightarrow> ii'\<in>carT \<Longrightarrow> Frel (=) mybis (strT ii) (strT ii') \<Longrightarrow> mybis ii ii'"

term "lsbis carT strT" 
term mybis

lemma mybis_carT: "mybis ii ii' \<Longrightarrow> ii \<in> carT \<and> ii' \<in> carT"
using mybis.simps by blast

thm F.in_rel[of "(=)", simped, of R a b]

lemma F_in_rel_id1: "Frel (=) R a b =
(\<exists>z. Fset2 z \<subseteq> {(x, y). R x y} \<and> Fmap id fst z = a \<and> Fmap id snd z = b)"
unfolding F.in_rel apply safe  
  subgoal for z apply(rule exI[of _"Fmap fst id z"])
  by (auto simp: F.set_map F.map_comp intro!: F.map_cong0)
  subgoal for z apply(rule exI[of _"Fmap (\<lambda>a. (a,a)) id z"])
  by (auto simp: F.set_map F.map_comp intro!: F.map_cong0) .

lemma sbis_mybis: "sbis carT strT {(ii, ii'). mybis ii ii'}"
unfolding bis_def apply auto  
	using mybis.simps apply blast
  using mybis.simps apply blast
  apply(subst (asm) mybis.simps)  
  unfolding F_in_rel_id1 by auto

lemma mybis_implies_lsbis: 
"{(ii, ii'). mybis ii ii'} \<subseteq> lsbis carT strT"
using incl_lsbis[OF sbis_mybis] .

lemma lsbis_implis_mybis: 
assumes "(ii,ii') \<in> lsbis carT strT" shows "mybis ii ii'"
using assms apply(coinduct rule: mybis.coinduct) apply auto
  subgoal using lsbis_incl by blast
  subgoal using lsbis_incl by blast
  subgoal unfolding lsbis_def bis_Frel unfolding lsbis_def[symmetric]  
  	by simp (smt (z3) CollectI Collect_case_prod_in_rel_leE F_in_rel_id1 case_prodI2 in_mono subrelI) .

lemma lsbis_eq_mybis: "lsbis carT strT = {(ii,ii') . mybis ii ii'}"
using lsbis_implis_mybis mybis_implies_lsbis by auto

lemma mybis_eq_lbis: "mybis = (\<lambda>ii ii'. (ii,ii') \<in> lsbis carT strT)"
unfolding fun_eq_iff by (auto simp: lsbis_eq_mybis)

lemma equiv_lsbis_carT_strT: "equiv carT (lsbis carT strT)"  
	using coalg_T equiv_lsbis by blast

lemma mybis_refl: "ii \<in> carT \<Longrightarrow> mybis ii ii"
using equiv_lsbis_carT_strT unfolding mybis_eq_lbis equiv_def equivp_def refl_on_def by blast

lemma mybis_sym: "mybis ii ii' \<Longrightarrow> mybis ii' ii"
using equiv_lsbis_carT_strT unfolding mybis_eq_lbis equiv_def equivp_def sym_def by blast

lemma mybis_trans: "mybis ii ii' \<Longrightarrow> mybis ii' ii'' \<Longrightarrow> mybis ii ii''"
using equiv_lsbis_carT_strT unfolding mybis_eq_lbis equiv_def equivp_def trans_def by blast

(* *)

lemma mybis_Purged: 
assumes 1: "(Kl,lab) \<in> carT"
shows "mybis (Kl,lab) (Purged lab,lab)"
proof-
  define i j where "i = (Kl,lab)" and "j = (Purged lab,lab)"
  have 0: "i \<in> carT \<and> (\<exists>Kl lab. i = (Kl,lab) \<and> j = (Purged lab,lab))"
  using 1 unfolding i_def j_def by auto
  show ?thesis unfolding i_def[symmetric] j_def[symmetric] using 0 proof coinduct
  	case (mybis i j)
  	then show ?case apply auto 
      subgoal for Kl lab unfolding strT_def apply simp unfolding F.rel_map apply simp
      apply(rule F.rel_refl_strong)
        subgoal by auto
        subgoal unfolding carT_def isNode_def  
        	apply (auto simp add: empty_Shift isNode_def)
          apply (metis ShiftD Succ_Shift shift_def append_Cons)
          apply (metis ShiftD Succ_Shift shift_def append_Cons)
          apply (metis Succ_Shift shift_def append.left_neutral)
          apply (metis Succ_Shift shift_def append.left_neutral)  
          using Purged_Shift_shift mybis apply blast+ . . .
  qed
qed

lemma purgeLab_Nil[simp]: "(Kl,lab) \<in> carT \<Longrightarrow> purgeLab R Kl lab [] = lab []"
unfolding purgeLab_def carT_def by auto

lemma mybis_purgeLab: 
assumes 1: "(Kl,lab) \<in> carT"
shows "mybis (Kl,lab) (Kl,purgeLab R Kl lab)"
proof-
  define i j where "i = (Kl,lab)" and "j = (Kl,purgeLab R Kl lab)"
  have 0: "i \<in> carT \<and> (\<exists>Kl lab. i = (Kl,lab) \<and> j = (Kl,purgeLab R Kl lab))"
  using 1 unfolding i_def j_def by auto
  show ?thesis unfolding i_def[symmetric] j_def[symmetric] using 0 proof coinduct
  	case (mybis i j)
  	then show ?case apply auto
      subgoal for Kl lab using purgeLab_carT by blast
      subgoal for Kl lab unfolding strT_def apply simp unfolding F.rel_map apply simp
      apply(rule F.rel_refl_strong)
        subgoal by auto
        subgoal unfolding carT_def isNode_def  
        	apply (auto simp add: empty_Shift isNode_def)
          apply (metis ShiftD Succ_Shift shift_def append_Cons)
          apply (metis ShiftD Succ_Shift shift_def append_Cons)
          apply (metis Succ_Shift shift_def append.left_neutral)
          apply (metis Succ_Shift shift_def append.left_neutral) 
          unfolding shift_def Shift_def fun_eq_iff purgeLab_def by auto . .
  qed
qed

proposition carT_ex_cleancarT_mybis: 
assumes 1: "i \<in> carT"
shows "\<exists>i'. i' \<in> cleancarT R \<and> mybis i i'"
apply(cases i)
  subgoal for Kl lab apply(rule exI[of _ "(Purged lab, purgeLab R (Purged lab) lab)"])
  by (metis (mono_tags, lifting) CollectI Purged_carT assms cleancarT_def mybis_Purged 
    mybis_purgeLab mybis_trans) .

(* *)

local_setup \<open>Wide_Database.register_wide @{type_name bd_type_F}
  {T = @{typ "bd_type_F"}, axioms = {bij_upto = refl,
    rel_eq = @{thm refl[of "(=)"]}, rel_per = @{thm neper_eq}, rep_eq = refl, cond_eq = NONE},
    facts = (), rel = @{term "(=) :: bd_type_F \<Rightarrow> bd_type_F \<Rightarrow> bool"}, cond = NONE, deps = []}\<close>

local_setup \<open>fn lthy => Wide_Typedef.wide_copy (Typedef.get_info lthy @{type_name bd_type_JF} |> hd) lthy\<close>

definition rel_JT :: "('a\<Rightarrow>'a\<Rightarrow>bool) \<Rightarrow> 'a JT \<Rightarrow> 'a JT => bool" 
where 
"rel_JT (R::'a\<Rightarrow>'a\<Rightarrow>bool) \<equiv> rel_prod (=) (rel_fun (=) (Frel R (=)))"

lemma neper_rel_JT[simp]: "neper R \<Longrightarrow> neper (rel_JT R)"
unfolding rel_JT_def by (simp add: prod.rrel_neper sum.rrel_neper)

lemma rel_JT_eq[simp]: "rel_JT (=) = (=)" 
unfolding rel_JT_def rrel_eq ..

(* *)
lemma strT_param': "rel_JT R ii ii' \<Longrightarrow> Frel R (rel_JT R) (strT ii) (strT ii')"
unfolding strT_def Shift_def shift_def rel_JT_def apply(cases "ii") apply(cases "ii'") 
by (auto simp: F.rel_map rel_fun_def intro: F.rel_mono_strong) 

lemma strT_param: "rel_fun (rel_JT R) (Frel R (rel_JT R)) strT strT"
using strT_param' unfolding rel_fun_def by auto

(* *)


 
(* *)
(* Relativization of strT and carT: *)

term strT
thm strT_def
thm BNF_Greatest_Fixpoint.Shift_def


lemma strT_aux: "strT = strT" ..
local_setup \<open>RLTHM @{binding strT_rlt_neper_param} @{thm strT_aux}\<close>
thm strT_rlt_neper_param[of R Fmap]

lemma shift_rlt[simp]: "neper R \<Longrightarrow> shift_rlt R = shift"
  unfolding shift_rlt_def shift_def by (simp only: rlt_param neper)

definition "sstrT_rlt R \<equiv> strT_rlt R Fmap" 

lemma sstrT_simp[simp]: "neper R \<Longrightarrow> sstrT_rlt R = strT"
unfolding sstrT_rlt_def strT_rlt_def strT_def 
by (simp add: rlt_param rrel_eq rlt_eq fun_eq_iff)

(* *)

lemma carT_aux: "carT = carT" ..
local_setup \<open>RLTHM @{binding carT_rlt_neper_param} @{thm carT_aux}\<close>
thm carT_rlt_neper_param[of R Fset2] 

definition "ccarT_rlt R \<equiv> carT_rlt R Fset2" 

lemma isNode_alt: "isNode Kl lab kl \<longleftrightarrow> (Fset2 (lab kl) = Succ Kl kl)"
unfolding isNode_def by auto
local_setup \<open>RLTHM @{binding isNode_alt_rlt} @{thm isNode_alt}\<close>
thm isNode_alt_rlt[of R Fset2, simped, unfolded rlt_param rrel_eq rlt_eq] 

lemma isNode_rlt_rlt[simp]: "neper R \<Longrightarrow> rel_fun (=) (Frel R (=)) lab lab \<Longrightarrow> 
isNode_rlt R Fset2 Kl lab = isNode Kl lab"
unfolding isNode_alt fun_eq_iff apply clarify
apply(subst isNode_alt_rlt[of R Fset2, simped, unfolded rlt_param rrel_eq rlt_eq]) 
by auto (metis F.set_transfer(2) rel_set_eq)

lemma ccarT_rlt_simp': "neper R \<Longrightarrow> 
ccarT_rlt R = {(Kl, lab) |Kl lab. rel_fun (=) (Frel R (=)) lab lab \<and> (Kl, lab) \<in> carT}"
unfolding ccarT_rlt_def carT_rlt_def carT_def 
apply (simp add: rlt_param rrel_eq rlt_eq fun_eq_iff) apply safe
  apply (auto simp: F.set_transfer)
  apply (smt (verit) F.set_transfer(2) isNode_alt rel_funD rel_set_eq)
  by (metis (full_types) F.set_transfer(2) isNode_alt rel_funD rel_set_eq) 

lemma ccarT_rlt_simp: "neper R \<Longrightarrow> ccarT_rlt R = carT \<inter> {i. rel_JT R i i}"
unfolding ccarT_rlt_simp' carT_def rel_JT_def by auto

(* *)

local_setup \<open>RLTHM @{binding carT_ne_rlt} @{thm carT_ne}\<close>
thm carT_ne_rlt[of R Fset2, unfolded rrel_eq ccarT_rlt_def[symmetric] rel_JT_def[symmetric], simped]

lemma ex_carT_rel_JT: "neper R \<Longrightarrow> \<exists>i. i \<in> carT \<and> rel_JT R i i"
using carT_ne_rlt[of R Fset2, unfolded rrel_eq ccarT_rlt_def[symmetric] rel_JT_def[symmetric], simped]
apply(auto simp: ccarT_rlt_simp[of R]) 
by (metis F.set_transfer(2) rel_set_eq)

(* *)

lemma coalg_aux: "coalg = coalg" ..
local_setup \<open>RLTHM @{binding coalg_rlt_neper_param} @{thm coalg_aux}\<close>
thm coalg_rlt_neper_param

lemma coalg_alt: "coalg B s = (\<forall>i. i \<in> B \<longrightarrow> (\<forall>b. b \<in> Fset2 (s i) \<longrightarrow> b \<in> B))"
unfolding coalg_def by auto
local_setup \<open>RLTHM @{binding coalg_rlt_alt} @{thm coalg_alt}\<close>
thm coalg_rlt_alt[no_vars, simped]

lemma coalg_rlt_simp: "neper R1 \<Longrightarrow>
neper R2 \<Longrightarrow>
rel_fun (Frel R1 R2) (rel_set R1) z1 z1 \<Longrightarrow>
rel_fun (Frel R1 R2) (rel_set R2) z2 z2 \<Longrightarrow>
rel_fun R2 (Frel R1 R2) s s \<Longrightarrow>
rel_set R2 B B \<Longrightarrow>
coalg_rlt R2 R1 z2 z1 B s = 
(\<forall>i. i \<in> closure R2 B \<longrightarrow> 
     closure R2 (z2 (s i)) \<subseteq> closure R2 B)"
unfolding closure_def 
apply(subst coalg_rlt_alt, auto) 
by (metis (no_types, opaque_lifting) mem_Collect_eq neper_classes_eq) 

(* NB: I switch the order of the relation arguments too: *)
definition ccoalg_rlt where 
"ccoalg_rlt R1 R2 \<equiv> coalg_rlt R2 R1 Fset2 Fset1"

lemma ccoalg_rlt_simp: "neper R1 \<Longrightarrow>
neper R2 \<Longrightarrow> rel_fun R2 (Frel R1 R2) s s \<Longrightarrow> rel_set R2 B B \<Longrightarrow>
ccoalg_rlt R1 R2 B s = 
(\<forall>i. i \<in> closure R2 B \<longrightarrow> 
     closure R2 (Fset2 (s i)) \<subseteq> closure R2 B)"
unfolding ccoalg_rlt_def apply(rule coalg_rlt_simp) 
by (auto simp add: F.set_transfer)

(* *)
definition tr :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a JT \<Rightarrow> bool" 
where "tr R \<equiv> \<lambda>i. i \<in> closure (rel_JT R) (ccarT_rlt R)"

lemma Collect_tr: "Collect (tr R) = closure (rel_JT R) (ccarT_rlt R)"
unfolding tr_def by auto

lemma tr_iff:  "tr R i \<longleftrightarrow> (\<exists>i'. i' \<in> ccarT_rlt R \<and> rel_JT R i' i)"
unfolding tr_def closure_def by auto

(* *) 
thm coalg_T
local_setup \<open>RLTHM @{binding coalg_T_rlt} @{thm coalg_T}\<close>
thm coalg_T_rlt[of R Fmap Fset2 Fset2 Fset1]

lemma ccoalg_rlt_ccar_T_rlt: 
"neper R \<Longrightarrow> 
 ccoalg_rlt R (rel_JT R) (ccarT_rlt R) strT"
using coalg_T_rlt[of R Fmap Fset2 Fset2 Fset1, unfolded rrel_eq]
unfolding ccoalg_rlt_def[symmetric] rel_JT_def[symmetric] rel_JT_def[symmetric]
unfolding ccarT_rlt_def[symmetric] ccarT_rlt_def[symmetric] 
unfolding sstrT_rlt_def[symmetric] sstrT_rlt_def[symmetric] 
apply -
unfolding ccarT_rlt_simp[of R] 
apply (auto simp: F.map_transfer F.set_transfer)
by (metis F.set_transfer(2) rel_set_eq)

lemma ccarT_rlt_param: "neper R \<Longrightarrow> rel_set (rel_JT R) (ccarT_rlt R) (ccarT_rlt R)"
unfolding ccarT_rlt_def 
by (metis F.set_transfer(2) bd_type_JF.rrel_eq carT_rlt_neper_param list.rrel_eq rel_JT_def rel_set_eq)

lemma su_closureI: 
"neper R \<Longrightarrow> rel_set R A A \<Longrightarrow> closure R A \<subseteq> closure R B \<Longrightarrow> A \<subseteq> closure R B"
using closure_ext by blast

proposition tr_stable: 
assumes R: "neper R"
shows "rel_JT R i i \<Longrightarrow> tr R i \<Longrightarrow> Fset2 (strT i) \<subseteq> Collect (tr R)"
unfolding Collect_tr unfolding tr_def using ccoalg_rlt_ccar_T_rlt[OF R] using R apply - 
apply(subst (asm) ccoalg_rlt_simp[ of R]) 
  subgoal by auto
  subgoal by auto
  subgoal using strT_param .
  subgoal using ccarT_rlt_param .
  subgoal apply(rule su_closureI)
    subgoal by auto
    subgoal apply(subgoal_tac "Fset2 (strT i) \<subseteq> closure (rel_JT R) (ccarT_rlt R)")
      subgoal unfolding rel_set_def closure_def  
      by simp (smt (verit, best) Ball_Collect mem_Collect_eq neper_classes_eq neper_rel_JT)
      subgoal apply(erule allE[of _ i]) apply simp 
      	by (metis F.set_transfer(2) closure_ext rel_fun_def strT_param subset_trans) .
    subgoal using R by blast . .

proposition tr_closed: "neper R \<Longrightarrow> closed (rel_JT R) (Collect (tr R))"
unfolding closed_def tr_def 
by simp (metis ccarT_rlt_param closed_closure closed_def neper_rel_JT)

proposition tr_rel_JT: "neper R \<Longrightarrow> tr R i \<Longrightarrow> rel_JT R i i"
by (metis Collect_tr mem_Collect_eq neper_classes_eq 
 neper_rel_JT rel_setD2 rel_set_closure')
 

(* *)
thm mybis.simps[simped,of ii ii']
thm mybis.coinduct[of Q ii ii']

lemma mybis_aux: "mybis = mybis" ..
local_setup \<open>RLTHM @{binding mybis_rlt_param} @{thm mybis_aux}\<close>


definition "mmybis_rlt R = mybis_rlt R Fmap Fset1 Fset2 Fmap Fset2"

lemma mmybis_rlt_param: 
"neper R \<Longrightarrow> rel_fun (rel_JT R) (rel_fun (rel_JT R) (=)) (mmybis_rlt R) (mmybis_rlt R)" 
apply(rule mybis_rlt_param[of R Fmap Fset1 Fset2 Fmap Fset2, unfolded mmybis_rlt_def[of R, symmetric] 
rel_JT_def[of R, symmetric] rrel_eq, simped]) 
apply (auto simp: F.set_transfer F.map_transfer)
by (metis F.set_transfer(2) rel_set_eq)

lemma mmybis_rlt_param': 
"neper R \<Longrightarrow> rel_JT R i i' \<Longrightarrow> rel_JT R j j' \<Longrightarrow> mmybis_rlt R i j \<longleftrightarrow> mmybis_rlt R i' j'" 
using mmybis_rlt_param[of R] unfolding rel_fun_def by blast

proposition rel_JT_mmybis_rlt_compp: "neper R \<Longrightarrow> rel_JT R OO mmybis_rlt R OO rel_JT R \<le> mmybis_rlt R"
using mmybis_rlt_param'[of R] 
by auto (metis (no_types, lifting) CollectD CollectI neper_classes_eq neper_rel_JT)

lemma Frel_mmybis_rlt_rel_JT_aux: 
assumes R: "neper R" 
and r: "rel_JT R i ii" "rel_JT R i' ii'" and tr: "tr R ii" "tr R ii'"
and f: "Frel R (mmybis_rlt R) (strT ii) (strT ii')" 
shows "Frel R (mmybis_rlt R) (strT i) (strT i')"
proof-
  have "Frel R (rel_JT R) (strT i) (strT ii)"
  by (simp add: r(1) strT_param')
  moreover 
  have "Frel R (rel_JT R) (strT ii') (strT i')"
  by (metis F.rel_flip R neper_conversep neper_rel_JT r(2) strT_param')
  ultimately 
  have 0: "Frel R (rel_JT R OO mmybis_rlt R OO rel_JT R) (strT i) (strT i')"
  by (smt (verit, ccfv_threshold) F.rel_compp R f neper_relcompp_leq relcomppI)
  show ?thesis apply(rule F.rel_mono_strong[OF 0])
  by auto (metis (no_types, lifting) CollectD CollectI R mmybis_rlt_param' neper_classes_eq neper_rel_JT)
qed

(* *)
local_setup \<open>RLTHM @{binding mybis_refl_rlt} @{thm mybis_refl}\<close>
thm mybis_refl_rlt[of R Fmap Fset1 Fset2 Fmap Fset2, simped, 
unfolded mmybis_rlt_def[symmetric] ccarT_rlt_def[symmetric] sstrT_rlt_def[symmetric]
rlt_param rrel_eq, simped, unfolded rlt_param,simped, unfolded rel_JT_def[symmetric]]

lemma mmybis_rlt_refl: 
"neper R \<Longrightarrow> tr R i \<Longrightarrow> mmybis_rlt R i i"
apply(rule mybis_refl_rlt[of R Fmap Fset1 Fset2 Fmap Fset2, simped, 
unfolded mmybis_rlt_def[symmetric] ccarT_rlt_def[symmetric] sstrT_rlt_def[symmetric]
rlt_param rrel_eq, simped, unfolded rlt_param,simped, unfolded rel_JT_def[symmetric]])
apply (auto simp: F.map_transfer F.set_transfer tr_def closure_def)
apply (metis F.set_transfer(2) rel_set_eq)
by (metis CollectD CollectI neper_classes_eq neper_rel_JT)

(* *)
local_setup \<open>RLTHM @{binding mybis_sym_rlt} @{thm mybis_sym}\<close>
thm mybis_sym_rlt[of R Fmap Fset1 Fset2 Fmap Fset2, simped, 
unfolded mmybis_rlt_def[symmetric] ccarT_rlt_def[symmetric] sstrT_rlt_def[symmetric]
rlt_param rrel_eq, simped, unfolded rlt_param,simped, unfolded rel_JT_def[symmetric]]

lemma mmybis_rlt_sym: 
"neper R \<Longrightarrow> rel_JT R i i \<Longrightarrow> rel_JT R j j \<Longrightarrow> mmybis_rlt R i j \<Longrightarrow> mmybis_rlt R j i"
apply(rule mybis_sym_rlt[of R Fmap Fset1 Fset2 Fmap Fset2, simped, 
unfolded mmybis_rlt_def[symmetric] ccarT_rlt_def[symmetric] sstrT_rlt_def[symmetric]
rlt_param rrel_eq, simped, unfolded rlt_param,simped, unfolded rel_JT_def[symmetric]])
apply (auto simp: F.map_transfer F.set_transfer tr_def closure_def)
by (metis F.set_transfer(2) rel_set_eq)

(* *)
local_setup \<open>RLTHM @{binding mybis_trans_rlt} @{thm mybis_trans}\<close>
thm mybis_trans_rlt[of R Fmap Fset1 Fset2 Fmap Fset2, simped, 
unfolded mmybis_rlt_def[symmetric] ccarT_rlt_def[symmetric] sstrT_rlt_def[symmetric]
rlt_param rrel_eq, simped, unfolded rlt_param,simped, unfolded rel_JT_def[symmetric]]

lemma mmybis_rlt_trans: 
"neper R \<Longrightarrow> rel_JT R i i \<Longrightarrow> rel_JT R j j \<Longrightarrow> rel_JT R k k \<Longrightarrow> 
 mmybis_rlt R i j \<Longrightarrow> mmybis_rlt R j k \<Longrightarrow> mmybis_rlt R i k"
apply(rule mybis_trans_rlt[of R Fmap Fset1 Fset2 Fmap Fset2, simped, 
unfolded mmybis_rlt_def[symmetric] ccarT_rlt_def[symmetric] sstrT_rlt_def[symmetric]
rlt_param rrel_eq, simped, unfolded rlt_param,simped, unfolded rel_JT_def[symmetric]])
apply (auto simp: F.map_transfer F.set_transfer tr_def closure_def)
by (metis F.set_transfer(2) rel_set_eq)
   

(* *) 
thm mybis_carT
local_setup \<open>RLTHM @{binding mybis_carT_rlt} @{thm mybis_carT}\<close>
thm mybis_carT_rlt[of R Fset2 Fmap Fset1 Fset2 Fmap, simped, 
unfolded mmybis_rlt_def[symmetric] ccarT_rlt_def[symmetric] sstrT_rlt_def[symmetric]
rlt_param rrel_eq, simped, unfolded rlt_param,simped, unfolded rel_JT_def[symmetric]]

proposition mmybis_rlt_tr: 
"neper R \<Longrightarrow> rel_JT R i i \<Longrightarrow> rel_JT R j j \<Longrightarrow> mmybis_rlt R i j \<Longrightarrow> tr R i \<and> tr R j"
unfolding tr_def closure_def apply simp
apply(rule mybis_carT_rlt[of R Fset2 Fmap Fset1 Fset2 Fmap, simped, 
unfolded mmybis_rlt_def[symmetric] ccarT_rlt_def[symmetric] sstrT_rlt_def[symmetric]
rlt_param rrel_eq, simped, unfolded rlt_param,simped, unfolded rel_JT_def[symmetric]])
apply (auto simp: F.map_transfer F.set_transfer tr_def closure_def)
by (metis F.set_transfer(2) rel_set_eq)
  
(* *)

lemma equivp_mmybis_rlt: "neper R \<Longrightarrow> 
equiv {i. tr R i} {(i,j). rel_JT R i i \<and> rel_JT R j j \<and> mmybis_rlt R i j}"
unfolding equiv_def refl_on_def sym_def trans_def apply safe  
	using mmybis_rlt_tr apply blast
	using mmybis_rlt_tr apply blast 
  apply (simp add: tr_rel_JT)
  apply (simp add: tr_rel_JT)
  using  mmybis_rlt_refl
  apply (simp add: mmybis_rlt_refl) 
  using mmybis_rlt_sym apply blast
  using mmybis_rlt_trans by blast 
  

(* *)
lemma [simp]: "neper R \<Longrightarrow> Frel_rlt R R (rel_prod (=) (rel_fun (=) (Frel R (=)))) (rel_prod (=) (rel_fun (=) (Frel R (=)))) Fmap Fmap
            Fset2 Fset1 = Frel"
apply(subst Frel_rlt_param) by auto

local_setup \<open>RLTHM @{binding mybis_simps_rlt} @{thm mybis.simps}\<close>
thm mybis_simps_rlt[of R Fmap Fmap Fset2 Fset1 Fset2, simped, 
unfolded mmybis_rlt_def[symmetric] ccarT_rlt_def[symmetric] sstrT_rlt_def[symmetric]
rlt_param rrel_eq, simped, unfolded rlt_param,simped, unfolded rel_JT_def[symmetric], of i j, 
unfolded tr_iff[symmetric]]

thm mybis.simps[of ii ii', simped]
 
proposition mmybis_rlt_simps:  
assumes R: "neper R"
shows
"rel_JT R i i \<Longrightarrow> rel_JT R i' i' \<Longrightarrow> 
 mmybis_rlt R i i' \<longleftrightarrow> 
 (tr R i \<and> tr R i' \<and> Frel R (mmybis_rlt R) (strT i) (strT i'))"
apply(subst mybis_simps_rlt[of R Fmap Fmap Fset2 Fset1 Fset2, simped, 
unfolded mmybis_rlt_def[symmetric] ccarT_rlt_def[symmetric] sstrT_rlt_def[symmetric]
rlt_param rrel_eq, simped, unfolded rlt_param,simped, unfolded rel_JT_def[symmetric], 
unfolded tr_iff[symmetric]])
  subgoal using R by auto
  subgoal by (auto simp: F.map_transfer F.set_transfer F.rel_map)
  subgoal by (auto simp: F.map_transfer F.set_transfer F.rel_map)  
	subgoal by (auto simp: F.map_transfer F.set_transfer F.rel_map)
  subgoal by (auto simp: F.map_transfer F.set_transfer F.rel_map) 
  subgoal by (metis F.set_transfer(2) rel_set_eq)
  subgoal .
  subgoal .
  subgoal apply standard 
    subgoal apply(elim exE conjE)
      subgoal for ii ii' apply(intro conjI)
        subgoal by (meson assms mmybis_rlt_param' mmybis_rlt_refl mmybis_rlt_tr) 
        subgoal by (meson assms mmybis_rlt_param' mmybis_rlt_refl mmybis_rlt_tr)
        subgoal using Frel_mmybis_rlt_rel_JT_aux[OF R] . . .
  subgoal apply(rule exI[of _ i], simp) by (rule exI[of _ i'], simp) . .

(*   *)


local_setup \<open>RLTHM @{binding mybis_coinduct_rlt} @{thm mybis.coinduct}\<close>
thm mybis_coinduct_rlt[of R Fmap Fset1 Fset2 Fmap Fset2, simped, 
unfolded mmybis_rlt_def[symmetric] ccarT_rlt_def[symmetric] sstrT_rlt_def[symmetric]
rlt_param rrel_eq, simped, unfolded rlt_param,simped, unfolded rel_JT_def[symmetric], 
unfolded tr_iff[symmetric], of i j \<phi>]

thm mybis.coinduct[of ii ii', simped]
 
proposition mmybis_rlt_coinduct:  
assumes R: "neper R"
and r: "rel_JT R i i" "rel_JT R j j"
and phi: "rel_fun (rel_JT R) (rel_fun (rel_JT R) (=)) \<phi> \<phi>"
"\<phi> i j"
and 0: "\<And>i j. rel_JT R i i \<Longrightarrow> rel_JT R j j \<Longrightarrow> \<phi> i j \<Longrightarrow>
    tr R i \<and> tr R j \<and> Frel R (\<lambda>uu uua. \<phi> uu uua \<or> mmybis_rlt R uu uua) (strT i) (strT j)" 
shows "mmybis_rlt R i j"
apply(rule mybis_coinduct_rlt[of R Fmap Fset1 Fset2 Fmap Fset2, simped, 
unfolded mmybis_rlt_def[symmetric] ccarT_rlt_def[symmetric] sstrT_rlt_def[symmetric]
rlt_param rrel_eq, simped, unfolded rlt_param,simped, unfolded rel_JT_def[symmetric], 
unfolded tr_iff[symmetric], OF R _ _ _ _ _ r(2,1), of \<phi>, OF _ _ _ _ _ phi])
  subgoal by (auto simp: F.map_transfer F.set_transfer F.rel_map)
  subgoal by (auto simp: F.map_transfer F.set_transfer F.rel_map)  
	subgoal by (auto simp: F.map_transfer F.set_transfer F.rel_map)
  subgoal by (auto simp: F.map_transfer F.set_transfer F.rel_map) 
  subgoal by (metis F.set_transfer(2) rel_set_eq)
  subgoal for i j using 0[of i j] apply clarsimp
  apply(rule exI[of _ i], simp) by (rule exI[of _ j], simp) .
 
(* *)

lemma rel_JT_implies_mmybis_rlt: 
"neper R \<Longrightarrow> mmybis_rlt R i i \<or> mmybis_rlt R j j \<Longrightarrow> rel_JT R i j \<Longrightarrow>  mmybis_rlt R i j"
	by (metis CollectD CollectI mmybis_rlt_param' neper_classes_eq neper_rel_JT)

lemma rel_JT_tr_implies_mmybis_rlt: 
"neper R \<Longrightarrow> tr R i \<or> tr R j \<Longrightarrow> rel_JT R i j \<Longrightarrow> mmybis_rlt R i j"
using mmybis_rlt_refl rel_JT_implies_mmybis_rlt by blast

(* *)
coinductive myrel :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a JT \<Rightarrow> 'a JT \<Rightarrow> bool)" 
for R :: "('a \<Rightarrow> 'a \<Rightarrow> bool)" 
where 
"i \<in> carT \<Longrightarrow> i' \<in> carT \<Longrightarrow> Frel R (myrel R) (strT i) (strT i') \<Longrightarrow> myrel R i i'"

lemma rel_JT_implies_myrel: 
assumes "i \<in> carT" "j \<in> carT" "rel_JT R i j" 
shows "myrel R i j"
proof-
  have 0: "i \<in> carT \<and> j \<in> carT \<and> rel_JT R i j"
  using assms by auto
  show ?thesis
  using 0 proof coinduct
    case (myrel i j)
    hence 1: "Frel R (rel_JT R) (strT i) (strT j)"  
    	using strT_param' by blast
    then show ?case using myrel apply (auto intro!: F.rel_mono_strong[OF 1])  
    	by (meson coalg_T coalg_alt)+
  qed
qed

lemma myrel_conversep:  
assumes "i \<in> carT" "j \<in> carT" "myrel R i j"
shows "myrel (conversep R) j i"
proof-
  have 0: "i \<in> carT \<and> j \<in> carT \<and> myrel R i j"
  using assms by auto
  show ?thesis using 0 proof coinduct
    case (myrel i j)
    hence "Frel R (myrel R) (strT j) (strT i)" 
    	using myrel.cases by blast
    hence 1: "Frel (conversep R) (conversep (myrel R)) (strT i) (strT j)"
    using F.rel_flip by blast
    then show ?case using myrel by (auto intro: F.rel_mono_strong[OF 1] elim: myrel.cases) 
  qed
qed

lemma myrel_compp:  
assumes "i \<in> carT" "j \<in> carT" "myrel Q i j" "myrel R j k"
shows "myrel (Q OO R) i k"
proof-
  have 0: "\<exists>j. i \<in> carT \<and> j \<in> carT \<and> myrel Q i j \<and> myrel R j k"
  using assms by auto
  show ?thesis using 0 proof coinduct
    case (myrel i k)
    then obtain j where 0: "i \<in> carT" "j \<in> carT" "myrel Q i j" "myrel R j k" by auto    
    hence "Frel Q (myrel Q) (strT i) (strT j)"  "Frel R (myrel R) (strT j) (strT k)"
    	using myrel.cases by blast+
    hence 1: "Frel (Q OO R) (myrel Q OO myrel R) (strT i) (strT k)"
    by (metis F.rel_compp relcompp_apply)
    then show ?case using myrel by (auto intro: F.rel_mono_strong[OF 1] elim: myrel.cases) 
  qed
qed

lemma myrel_sym: 
assumes "neper R" and "myrel R i i'"
shows "myrel R i' i"
by (metis assms myrel.cases myrel_conversep neper_conversep)

lemma myrel_trans: 
assumes "neper R" 
and "myrel R i i'" "myrel R i' i''"
shows "myrel R i i''"
	by (metis (no_types, lifting) assms myrel.cases myrel_compp neper_relcompp_leq)

lemma neper_myrel: 
assumes R: "neper R"
shows "neper (myrel R)" 
unfolding neper_def proof safe
  show "per (myrel R)" unfolding per_def  
  	using assms myrel_sym myrel_trans by blast
  have "\<exists>i. i \<in> carT \<and> rel_JT R i i"  
  	using ex_carT_rel_JT[OF R] . 
  thus "\<exists>i. myrel R i i"  
  	using rel_JT_implies_myrel by blast
qed

lemma myrel_eq_mybis:
"myrel (=) i j \<longleftrightarrow> mybis i j"
proof safe
  assume "myrel (=) i j"
  thus "mybis i j"
  apply coinduct apply auto 
  	apply (simp add: myrel.simps) apply (simp add: myrel.simps)
    using F.rel_mono_strong0 myrel.simps by fastforce
next
  assume "mybis i j" 
  thus "myrel (=) i j"
  apply coinduct apply auto 
  	apply (simp add: mybis.simps) apply (simp add: mybis.simps)
    using F.rel_mono_strong0 mybis.simps by fastforce
qed

lemma myrel_compat_mybis:
"mybis i i' \<Longrightarrow> mybis j j' \<Longrightarrow> myrel R i j \<longleftrightarrow> myrel R i' j'"
by (smt (verit, ccfv_SIG) eq_comp_r mybis_carT mybis_sym myrel_compp myrel_eq_mybis)

lemma mmybis_rlt_implies_myrel: 
assumes R: "neper R"
and 0: "i \<in> ccarT_rlt R" "j \<in> ccarT_rlt R" "mmybis_rlt R i j"
shows "myrel R i j" 
proof-
  have 0: "i \<in> carT \<and> rel_JT R i i \<and> j \<in> carT \<and> rel_JT R j j \<and> mmybis_rlt R i j"
  using assms ccarT_rlt_simp by auto
  thus ?thesis proof coinduct
  	case (myrel i j)
    hence t: "tr R i" "tr R j" and f: "Frel R (mmybis_rlt R) (strT i) (strT j)"
    using mmybis_rlt_simps[OF R] by blast+
  	show ?case apply (auto simp: myrel intro!: F.rel_mono_strong[OF f])
    apply (meson myrel coalg_T coalg_alt)
    apply (metis (mono_tags, lifting) Ball_Collect R t(1) tr_rel_JT tr_stable)
    apply (meson coalg_T coalg_alt myrel)
    by (metis (mono_tags, lifting) Ball_Collect R t(2) tr_rel_JT tr_stable) 
  qed
qed

(* *)

definition h :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a JT \<Rightarrow> 'a JT" where 
"h R i \<equiv> getReprOn carT (rel_JT R) i"

lemma tr_h_carT: 
assumes "neper R" "tr R i"
shows "h R i \<in> carT"
by (smt (verit, ccfv_threshold) assms Int_iff ccarT_rlt_simp 
getReprOn_in' h_def mem_Collect_eq neper_classes_eq neper_rel_JT tr_iff)

lemma mmybis_rlt_implies_myrel_h: 
assumes R: "neper R"
and tri: "tr R i" and trj: "tr R j" and m: "mmybis_rlt R i j"
shows "myrel R (h R i) (h R j)" 
proof-
  have 1: "rel_JT R i i" "rel_JT R j j"  
  	using R tr_rel_JT tri trj by blast+
  define i' j' where "i' = h R i"
  and "j' = h R j"

  have i'0: "i' \<in> carT \<and> rel_JT R i i'" 
  unfolding i'_def h_def apply(rule getReprOn_in'[of "rel_JT R"])
    apply (simp add: R) 
    by (metis (no_types, lifting) CollectD CollectI Int_iff R ccarT_rlt_simp neper_classes_eq 
          neper_rel_JT tr_iff tri) 
  hence i': "i' \<in> ccarT_rlt R"  
  	by (metis (no_types, lifting) CollectD CollectI Int_iff R ccarT_rlt_simp neper_classes_eq neper_rel_JT)

  have j'0: "j' \<in> carT \<and> rel_JT R j j'" 
  unfolding j'_def h_def apply(rule getReprOn_in'[of "rel_JT R"])
    apply (simp add: R) 
    by (metis (no_types, lifting) CollectD CollectI Int_iff R ccarT_rlt_simp neper_classes_eq 
          neper_rel_JT tr_iff trj) 
  hence j': "j' \<in> ccarT_rlt R"  
  	by (metis (no_types, lifting) CollectD CollectI Int_iff R ccarT_rlt_simp neper_classes_eq neper_rel_JT)

  have m': "mmybis_rlt R i' j'"  
  	using R i'0 j'0 m mmybis_rlt_param' by blast

  show ?thesis unfolding i'_def[symmetric] j'_def[symmetric]
  using mmybis_rlt_implies_myrel[OF R i' j' m'] .
qed

lemma myrel_h_implies_mmybis_rlt: 
assumes R: "neper R"
and m: "myrel R (h R i) (h R j)" 
and i: "tr R i" and j: "tr R j"
shows "mmybis_rlt R i j"
proof-
  define \<phi> where 
  "\<phi> \<equiv> \<lambda>i j. myrel R (h R i) (h R j) \<and> tr R i \<and> tr R j"

  show ?thesis proof(rule mmybis_rlt_coinduct[OF R, of i j \<phi>])
    show "rel_JT R i i"  
    	by (simp add: R i(1) tr_rel_JT)
    show j: "rel_JT R j j"  
    	by (simp add: R j(1) tr_rel_JT)
    show "rel_fun (rel_JT R) (rel_fun (rel_JT R) (=)) \<phi> \<phi>"
      unfolding \<phi>_def rel_fun_def apply(intro allI impI ) 
      by (smt (verit, ccfv_threshold) R geterReprOn_related mem_Collect_eq 
       mmybis_rlt_implies_myrel_h mmybis_rlt_tr myrel_sym myrel_trans neper_classes_eq 
       neper_rel_JT rel_JT_tr_implies_mmybis_rlt) 
    show "\<phi> i j" using assms unfolding \<phi>_def by auto
    (* *) 
    fix i j
    assume ij: "rel_JT R i i" "rel_JT R j j" and "\<phi> i j"
    hence m: "myrel R (h R i) (h R j)" and 
    i: "tr R i" and j: "tr R j" unfolding \<phi>_def by auto

    have f1: "Frel R (rel_JT R) (strT i) (strT (h R i))"
      by (metis R getReprOn h_def ij(1) neper_rel_JT strT_param')  

    have f2: "Frel R (rel_JT R) (strT (h R j)) (strT j)"  
     by (metis R getReprOn h_def ij(2) mem_Collect_eq neper_classes_eq neper_rel_JT strT_param')

    have f3: "Frel R (myrel R) (strT (h R i)) (strT (h R j))"
    	using m myrel.simps by blast

    have f: "Frel R (rel_JT R OO myrel R OO rel_JT R) (strT i) (strT j)"
    using R f1 f2 f3  
    by (smt (verit, ccfv_threshold) F.rel_compp neper_relcompp_leq relcomppI)
    
    show "tr R i \<and> tr R j \<and> Frel R (\<lambda>uu uua. \<phi> uu uua \<or> mmybis_rlt R uu uua) (strT i) (strT j)"
    proof safe
      show "tr R i" "tr R j" by fact+
      show "Frel R (\<lambda>uu uua. \<phi> uu uua \<or> mmybis_rlt R uu uua) (strT i) (strT j)" 
      apply(rule F.rel_mono_strong[OF f]) apply simp_all unfolding \<phi>_def proof(intro disjI1 conjI)
        fix ii jj assume ii: "ii \<in> Fset2 (strT i)" and jj: "jj \<in> Fset2 (strT j)"
        and "rel_conj (rel_JT R) (myrel R) ii jj"
        then obtain ii' jj' where 
        1: "rel_JT R ii ii'" "myrel R ii' jj'" "rel_JT R jj' jj"
        by blast

        have "rel_JT R ii (h R ii)" by (metis R 1(1) getReprOn h_def neper_rel_JT)
        hence ii': "rel_JT R ii' (h R ii)"  
        	by (metis "1"(1) CollectD CollectI R neper_classes_eq neper_rel_JT)

        have "rel_JT R jj (h R jj)"  
        	by (metis "1"(3) R getReprOn h_def mem_Collect_eq neper_classes_eq neper_rel_JT)
        hence jj': "rel_JT R jj' (h R jj)"  
        	by (metis "1"(3) CollectD CollectI R neper_classes_eq neper_rel_JT)
        
        show "tr R ii" "tr R jj"
              "myrel R (h R ii) (h R jj)"  
          apply (metis Collect_tr R i ii ij(1) in_mono tr_def tr_stable)
          apply (metis Collect_tr R ij(2) in_mono j jj tr_def tr_stable)
          
          by (metis (no_types, lifting) "1"(2) Ball_Collect R i ii ii' ij(1) ij(2) j jj jj' 
         myrel.simps myrel_sym myrel_trans rel_JT_implies_myrel tr_h_carT tr_stable)
      qed
    qed
  qed
qed 


lemma beh_carT: "beh (s::'a JT \<Rightarrow> ('a,'a JT)F) i \<in> carT"
by (meson mor_beh mor_image range_subsetD)

lemma strT_beh: "strT (beh (s::'a JT \<Rightarrow> ('a,'a JT)F) i) = Fmap id (beh s) (s i)"
	by (metis UNIV_I mor_beh mor_def) 

(* *)

local_setup \<open>RLTHM @{binding beh_carT_rlt} @{thm beh_carT}\<close>
thm beh_carT_rlt[of R Fset2 Fmap Fset2 bd_F, unfolded mmybis_rlt_def[of R, symmetric] 
ccarT_rlt_def[symmetric] rel_JT_def[of R, symmetric] rrel_eq, simped, no_vars]

definition "bbeh_rlt R \<equiv> beh_rlt (rel_JT R) R Fmap Fset2 bd_F"

lemma bbeh_rlt_tr: 
"neper R \<Longrightarrow> rel_fun (rel_JT R) (Frel R (rel_JT R)) s s \<Longrightarrow> 
 rel_JT R i i \<Longrightarrow>
 tr R (bbeh_rlt R s i)"
unfolding tr_iff bbeh_rlt_def
apply(rule beh_carT_rlt[of R Fset2 Fmap Fset2 bd_F, unfolded mmybis_rlt_def[of R, symmetric] 
ccarT_rlt_def[symmetric] rel_JT_def[of R, symmetric] rrel_eq, simped])
apply(auto simp: F.set_transfer F.map_transfer)
by (metis F.set_transfer(2) rel_set_eq)

(* *)

local_setup \<open>RLTHM @{binding strT_beh_rlt} @{thm strT_beh}\<close>

thm strT_beh_rlt[of R Fmap Fset2 bd_F Fmap Fmap, unfolded mmybis_rlt_def[of R, symmetric] 
ccarT_rlt_def[symmetric] sstrT_rlt_def[symmetric] rel_JT_def[of R, symmetric] rrel_eq 
bbeh_rlt_def[symmetric], simped, no_vars, unfolded F.rel_map, simped]

lemma strTbbeh_rlt: 
"neper R \<Longrightarrow> rel_fun (rel_JT R) (Frel R (rel_JT R)) s s \<Longrightarrow> rel_JT R i i \<Longrightarrow>
 Frel R (\<lambda>i j. rel_JT R i (bbeh_rlt R s j)) (strT (bbeh_rlt R s i)) (s i)"
apply(rule strT_beh_rlt[of R Fmap Fset2 bd_F Fmap Fmap, unfolded mmybis_rlt_def[of R, symmetric] 
ccarT_rlt_def[symmetric] sstrT_rlt_def[symmetric] rel_JT_def[of R, symmetric] rrel_eq 
bbeh_rlt_def[symmetric], simped, unfolded F.rel_map, simped])
by (auto simp: F.set_transfer F.map_transfer)

(* *)

lemma Frel_iff_Fset: 
"neper Q \<Longrightarrow> neper R \<Longrightarrow> Frel Q R x x \<longleftrightarrow> Fset1 x \<subseteq> {a. Q a a} \<and> Fset2 x \<subseteq> {a. R a a}"
apply safe
  using F.set_transfer[of Q R, unfolded rel_fun_def rel_set_def, rule_format, of x x] 
  apply auto  
  apply (metis CollectD CollectI neper_classes_eq)
  apply (metis CollectD CollectI neper_classes_eq)
  by (metis (mono_tags, lifting) Ball_Collect F.rel_refl_strong)

lemma Frel_myrel_iff_Fset: 
"neper R \<Longrightarrow> Frel R (myrel R) x x \<longleftrightarrow> Fset1 x \<subseteq> {a. R a a} \<and> Fset2 x \<subseteq> {i. myrel R i i}"
by (simp add: Frel_iff_Fset neper_myrel)

lemma neper_Frel_some: "neper R \<Longrightarrow> Frel R (=) (SOME x. Frel R (=) x x) (SOME x. Frel R (=) x x)"
	using Frel_neper neper_Some by blast

lemma neper_Fset1_Frel_some: "neper R \<Longrightarrow> a \<in> Fset1 (SOME x. Frel R (=) x x) \<Longrightarrow> R a a"
apply(frule neper_Frel_some) 
by (smt (verit, best) Ball_Collect Eps_cong Frel_iff_Fset neper_Frel_some neper_eq)

proposition cleancarT_myrel_implies_rel_JT: 
assumes R: "neper R" and i: "i \<in> cleancarT R" and m: "myrel R i i"
shows "rel_JT R i i"
proof(cases i)
  case (Pair Kl lab)
  have Kl: "Kl = Purged lab" 
  and lab: "(\<forall>kl. kl \<notin> Kl \<longrightarrow> lab kl = (SOME x. Frel R (=) x x))" 
  using i unfolding Pair cleancarT_iff by auto

  {fix kl assume kl: "kl \<in> Purged lab"
   hence "isPurged lab kl" using Purged_implies_isPurged by auto
   hence "Fset1 (lab kl) \<subseteq> {a. R a a}"  
   using m kl unfolding Pair proof(induct arbitrary: Kl)
     case (1 lab Kl)
     then show ?case apply(subst (asm) myrel.simps)  
     by (auto simp: Frel_myrel_iff_Fset[OF R] strT_def F.set_map)
   next
 	   case (2 k lab kl Kl)
     hence "Frel R (myrel R) (strT (Kl, lab)) (strT (Kl, lab))" 
     	 by (simp add: myrel.simps)

     hence 1: "Fset2 (strT (Kl,lab)) \<subseteq> {i. myrel R i i}"
     unfolding Frel_myrel_iff_Fset[OF R] by auto

     have 11: "({kl. k # kl \<in> Kl}, \<lambda>a. lab (k # a)) \<in> Fset2 (strT (Kl, lab))"
     using 2(1) unfolding strT_def by (auto simp: F.set_map Shift_def shift_def image_def 
       intro!: bexI[of _ k])

     have 0: "myrel R ({kl. k # kl \<in> Kl}, \<lambda>a. lab (k # a)) ({kl. k # kl \<in> Kl}, \<lambda>a. lab (k # a))"
     using 1 11 by auto

    have 3: "kl \<in> Purged (\<lambda>a. lab (k # a))" 
    using 2(5) Purged_Shift_shift[of _ lab, OF 2(1), unfolded shift_def Shift_def] by auto

 	   show ?case using 2(3)[of "{kl. k # kl \<in> Kl}", OF 0, simped, OF 3] .
   qed
  }
  thus ?thesis unfolding Pair rel_JT_def rel_prod.simps rel_fun_def apply clarsimp    
  apply(rule F.rel_refl_strong) 
    subgoal for kl a using lab[rule_format, of kl] Kl apply(cases "kl \<in> Kl") 
  	using neper_Fset1_Frel_some[OF R] by auto 
    subgoal .. .  
qed

proposition ex_h_tr_myrel: 
assumes R: "neper R" and j: "j \<in> carT"  
and m: "myrel R j j"
shows "\<exists>i. tr R i \<and> myrel R j (h R i)"
proof-
  obtain i where i: "i \<in> cleancarT R \<and> mybis j i"
  using carT_ex_cleancarT_mybis j by blast
  have ii: "i \<in> carT \<and> rel_JT R i i"  
  by (meson R cleancarT_myrel_implies_rel_JT i m mybis_carT myrel_compat_mybis)
  hence iii: " i \<in> ccarT_rlt R"  
  	by (simp add: R ccarT_rlt_simp)
  show ?thesis proof(rule exI[of _ i], safe)
    show "tr R i" using ii iii tr_iff by blast 
    have "myrel R j i"  
    	using i j m mybis_refl myrel_compat_mybis by blast
    thus "myrel R j (h R i)"  
    	by (metis (no_types, lifting) R getReprOn_in h_def ii myrel_trans neper_rel_JT rel_JT_implies_myrel)
  qed
qed

proposition 
assumes "neper R"
shows "bij_upto 
   (restr (mmybis_rlt R) (tr R))
   (restr (myrel R) (\<lambda>i. i \<in> carT))
   (h R)"
apply(rule bij_uptoI)
  subgoal by (meson assms ex_carT_rel_JT neper_myrel neper_restr rel_JT_implies_myrel)
  subgoal unfolding restr_def 
  	by (simp add: assms mmybis_rlt_implies_myrel_h tr_h_carT)
  subgoal unfolding restr_def using assms myrel_h_implies_mmybis_rlt by blast
  subgoal by (metis assms ex_h_tr_myrel mmybis_rlt_refl restr_def tr_h_carT) .


(*********)

type_synonym 'a JTT = "'a JT set" 

definition rel_JTT :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a JT) set \<Rightarrow> ('a JT) set \<Rightarrow> bool"
where 
"rel_JTT (R::'a\<Rightarrow>'a\<Rightarrow>bool) \<equiv> rel_set (rel_JT R)"

(* *)
lemma quotient_aux: "quotient = quotient" ..
local_setup \<open>RLTHM @{binding quotient_rlt_param} @{thm quotient_aux}\<close>
thm quotient_rlt_def[simped, 
unfolded mmybis_rlt_def[symmetric] ccarT_rlt_def[symmetric] sstrT_rlt_def[symmetric]
rlt_param rrel_eq, simped, unfolded rlt_param,simped, unfolded rel_JT_def[symmetric]]

lemma closure_aux: "closure = closure" ..
local_setup \<open>RLTHM @{binding closure_rlt_param} @{thm closure_aux}\<close>

lemma closure_rlt_simp:
"neper R \<Longrightarrow> R OO Q OO R \<le> Q \<Longrightarrow> closure_rlt R Q A = closure (R OO Q OO R) A"
unfolding closure_rlt_def closure_def apply simp apply auto  
	using neper_classes_eq apply fastforce 
	by (smt (verit, best) conversep_iff neper_conversep neper_relcompp_leq predicate2D relcomppI)

lemma neper_restr_mmybis[simp]: 
assumes R: "neper R"
shows "neper (restr (mmybis_rlt R) (\<lambda>i. rel_JT R i i))"
  unfolding neper_def restr_def per_def apply safe
  using assms mmybis_rlt_sym apply blast
  using assms mmybis_rlt_trans apply blast
  by (meson assms ex_carT_rel_JT ex_h_tr_myrel mmybis_rlt_refl rel_JT_implies_myrel tr_rel_JT)

lemmas car_final_closure_mybis = car_final_def[unfolded lsbis_eq_mybis quotient_closure]

lemma ccar_final_rlt_aux: 
assumes R: "neper R"
shows 
" {x. rel_set (rel_JT R) x x \<and>
     (\<exists>xa. rel_JT R xa xa \<and>
           rel_set (rel_JT R) x (closure_rlt (rel_JT R) (mmybis_rlt R) {x. rel_JT R x xa}) \<and>
           (\<exists>a'. a' \<in> ccarT_rlt R \<and> rel_JT R a' xa))} 
= 
{ii. \<exists>i. tr R i \<and> rel_set (rel_JT R) ii (closure (rel_JT R OO mmybis_rlt R OO rel_JT R) {i})}"
using R apply(simp add: closure_singl[symmetric])
apply(subst closure_rlt_simp) 
  subgoal using R by auto
  subgoal by (simp add: assms rel_JT_mmybis_rlt_compp) find_theorems mmybis_rlt neper
  subgoal unfolding closure_relcompp2[OF neper_rel_JT[OF R] neper_restr_mmybis[OF R]] 
  unfolding closure_def tr_iff apply simp 
  apply auto  
  apply (metis (no_types, opaque_lifting) \<open>neper R \<Longrightarrow> neper (rel_JT R)\<close> neper_def per_def set.rrel_neper)
  using tr_iff tr_rel_JT by blast .


local_setup \<open>RLTHM @{binding car_final_closure_mybis_rlt} @{thm car_final_closure_mybis}\<close>

definition ccar_final_rlt where 
"ccar_final_rlt R = car_final_rlt R Fmap Fmap Fset2 Fset1 Fset2"

thm car_final_closure_mybis_rlt[of R Fset2 Fmap Fset1 Fset2 Fmap Fmap Fset2 Fset1, simped, 
unfolded mmybis_rlt_def[symmetric] ccarT_rlt_def[symmetric] sstrT_rlt_def[symmetric]
ccar_final_rlt_def[symmetric]
rlt_param rrel_eq, simped, unfolded rlt_param,simped, unfolded rel_JT_def[symmetric], 
unfolded closure_def[symmetric]]

definition "ccar_final_rlt' R = 
{ii. \<exists>i. tr R i \<and> rel_set (rel_JT R) ii (closure (rel_JT R OO mmybis_rlt R OO rel_JT R) {i})}"

proposition ccar_final_rlt: "neper R \<Longrightarrow> 
rel_set (rel_JTT R) 
  (ccar_final_rlt R) 
  (ccar_final_rlt' R)"
unfolding rel_JTT_def
unfolding ccar_final_rlt'_def
unfolding ccar_final_rlt_aux[symmetric]
apply(rule car_final_closure_mybis_rlt[of R Fset2 Fmap Fset1 Fset2 Fmap Fmap Fset2 Fset1, simped, 
unfolded mmybis_rlt_def[symmetric] ccarT_rlt_def[symmetric] sstrT_rlt_def[symmetric]
ccar_final_rlt_def[symmetric]
rlt_param rrel_eq, simped, unfolded rlt_param,simped, unfolded rel_JT_def[symmetric], 
unfolded closure_def[symmetric]])
apply(auto simp: F.set_transfer F.map_transfer)
by (metis F.set_transfer(2) rel_set_eq)

(* *)
lemma neper_rel_JTT[simp]: "neper R \<Longrightarrow> neper (rel_JTT R)"
unfolding rel_JTT_def by simp

lemma rel_JTT_eq[simp]: "rel_JTT (=) = (=)" 
unfolding rel_JTT_def rel_JT_def rrel_eq ..

coinductive mmyrel :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a JTT \<Rightarrow> 'a JTT \<Rightarrow> bool)" 
for R :: "('a \<Rightarrow> 'a \<Rightarrow> bool)" 
where 
"i \<in> car_final \<Longrightarrow> i' \<in> car_final \<Longrightarrow> Frel R (mmyrel R) (str_final i) (str_final i') \<Longrightarrow> mmyrel R i i'"

term myrel
lemma JFrel_inv_imagep_mmyrel: 
assumes R: "neper R" 
shows "JFrel R = inv_imagep (mmyrel R) Rep_JF"
unfolding inv_imagep_def fun_eq_iff restr_def proof safe
  fix ii ii'
  assume "mmyrel R (Rep_JF ii) (Rep_JF ii')"
  hence 0: "inv_imagep (mmyrel R) Rep_JF ii ii'" unfolding inv_imagep_def by auto
  show "JFrel R ii ii'"
  apply(coinduct rule: JFrel_coinduct2[of "inv_imagep (mmyrel R) Rep_JF", OF 0])
  unfolding inv_imagep_def 
  unfolding dtor_def o_def F.map_comp F.rel_map   
  by (smt (verit, best) Abs_JF_inverse F.rel_cong Rep_JF coalg_alt id_def is_car_final mmyrel.cases)
next 
  fix jj jj'
  assume 1: "JFrel R jj jj'"   
  define ii and ii' where defs: "ii = Rep_JF jj" "ii' = Rep_JF jj'"
  hence 3: "jj = Abs_JF ii"  "jj' = Abs_JF ii'" by auto  
  have 2: "JFrel R (Abs_JF ii) (Abs_JF ii') \<and> ii \<in> car_final \<and> ii' \<in> car_final" 
  using 1 unfolding defs by auto
  show "mmyrel R (Rep_JF jj) (Rep_JF jj')"
  unfolding defs[symmetric] 
  using 2 proof(coinduct rule: mmyrel.coinduct)
    case (mmyrel j1 j2)
    hence 0: "Frel R (\<lambda>x y. JFrel R (Abs_JF x) (Abs_JF y)) (str_final j1) (str_final j2)" 
    apply(subst (asm) JFrel_Frel) by (auto simp: dtor_def F.rel_map)
    show ?case using mmyrel apply simp apply(rule F.rel_mono_strong[OF 0]) 
    by (meson coalg_alt is_car_final)+
  qed
qed

lemma mmyrel_sym: 
assumes R: "neper R" and 0: "mmyrel R ii ii'"
shows "mmyrel R ii' ii"
using 0 apply(coinduct rule: mmyrel.coinduct) apply auto
  subgoal for i i' using mmyrel.simps by auto
  subgoal for i i' using mmyrel.simps by auto
  subgoal for i i'
    apply(subgoal_tac "Frel (conversep R) (conversep (mmyrel R)) (str_final i) (str_final i')")
    using F.rel_mono_strong0 R neper_conversep apply fastforce
    by (simp add: F.rel_flip mmyrel.simps) . 

lemma mmyrel_trans: 
assumes R: "neper (R::'a\<Rightarrow>'a\<Rightarrow>bool)" 
and 0: "mmyrel R ii ii'" "mmyrel R ii' ii''"
shows "mmyrel R ii ii''"
proof-
  have "\<exists>ii'. mmyrel R ii ii' \<and> mmyrel R ii' ii''"
  using 0 by auto
  thus ?thesis proof(coinduct)
    case (mmyrel ii ii'')
    then show ?case proof auto
      fix ii' assume "mmyrel R ii ii'" "mmyrel R ii' ii''"
      thus "ii \<in> car_final"  "ii'' \<in> car_final"
      	using mmyrel.simps by blast+
    next
      fix ii'
      assume m: "mmyrel R ii ii'" "mmyrel R ii' ii''"
      hence "Frel R (mmyrel R) (str_final ii) (str_final ii')"  
      "Frel R (mmyrel R) (str_final ii') (str_final ii'')" 
      using mmyrel.simps by blast+
      hence 1: "Frel R (mmyrel R OO mmyrel R) (str_final ii) (str_final ii'')"
      by (smt (verit, best) F.rel_compp R neper_relcompp_leq relcomppI)
      
      show "Frel R (\<lambda>uu uua. (\<exists>ii'. mmyrel R uu ii' \<and> mmyrel R ii' uua) \<or> mmyrel R uu uua) (str_final ii) (str_final ii'')"
      apply(rule F.rel_mono_strong[OF 1])  
      by blast+
    qed
  qed
qed

lemma JFrel_JFwit: "JFrel (R::'a\<Rightarrow>'a\<Rightarrow>bool) JFwit JFwit"
apply(rule JF.rel_refl_strong) 
using JF.wit by fastforce

lemma neper_JFrel[simp]: "neper (R::'a\<Rightarrow>'a\<Rightarrow>bool) \<Longrightarrow> neper (JFrel R)"
apply(rule relator_pres_neper[of JFrel])
  subgoal using JF.rel_compp .
  subgoal using JF.rel_conversep .
  subgoal using JFrel_JFwit by auto
  subgoal by auto .
  
lemma neper_mmyrel: 
"neper R \<Longrightarrow> neper (mmyrel R)" 
using JFrel_inv_imagep_mmyrel[of R, unfolded inv_imagep_def fun_eq_iff]
using neper_JFrel[of R] unfolding neper_def per_def apply safe
apply (metis mmyrel_sym neper_def per_def)
apply (metis mmyrel_trans neper_def per_def) 
by (smt (z3) restr_def) 

(* *)

definition ttr :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a JTT \<Rightarrow> bool" 
where "ttr R \<equiv> \<lambda>ii. ii \<in> closure (rel_JTT R) (ccar_final_rlt R)"

lemma ttr_def': 
"neper R \<Longrightarrow> ttr R = (\<lambda>ii. ii \<in> closure (rel_JTT R) (ccar_final_rlt' R))"  
	by (metis ccar_final_rlt neper_rel_JTT rel_set_closure_eq ttr_def)

lemma Collect_ttr: "Collect (ttr R) = closure (rel_JTT R) (ccar_final_rlt R)"
unfolding ttr_def by auto

lemma ttr_iff:  "ttr R ii \<longleftrightarrow> (\<exists>ii'. ii' \<in> ccar_final_rlt R \<and> rel_JTT R ii' ii)"
unfolding ttr_def closure_def by auto

lemma Collect_ttr': "neper R \<Longrightarrow> Collect (ttr R) = closure (rel_JTT R) (ccar_final_rlt' R)"
unfolding ttr_def' by auto

lemma ttr_iff':  "neper R \<Longrightarrow> ttr R ii \<longleftrightarrow> (\<exists>ii'. ii' \<in> ccar_final_rlt' R \<and> rel_JTT R ii' ii)"
unfolding ttr_def' closure_def by auto

(* *)

definition quot :: "'a JT \<Rightarrow> 'a JTT"
where "quot i = closure mybis {i}"

definition quotRlt :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a JT \<Rightarrow> 'a JTT" 
where "quotRlt R i = closure (rel_JT R OO mmybis_rlt R OO rel_JT R) {i}"

lemma quot: "i \<in> carT \<Longrightarrow> quot i \<in> car_final"
unfolding car_final_closure_mybis quot_def by auto

lemma quot_surj: "ii \<in> car_final \<Longrightarrow> \<exists>i. i \<in> carT \<and> quot i = ii"
by (smt (verit, best) car_final_closure_mybis mem_Collect_eq quot_def)

lemma mybis_strT:
"i \<in> carT \<Longrightarrow> j \<in> carT \<Longrightarrow> mybis i j \<Longrightarrow> Frel (=) mybis  (strT i) (strT j)"
using mybis.cases by blast

lemma quot_def2: "quot = (\<lambda>x. Collect (mybis x))"
unfolding quot_def closure_def fun_eq_iff by auto

lemma str_quot:
assumes "i \<in> carT"
shows "str_final (quot i) = Fmap id quot (strT i)" 
using assms mor_T_final[unfolded mor_def] 
unfolding str_final_def lsbis_eq_mybis univ_def Equiv_Relations.proj_def quot_def2 
by auto

lemma quot_myrel_mmyrel:
assumes R: "neper R" and m: "myrel R i j"
shows "mmyrel R (quot i) (quot j)"
proof-
  define ii jj where defs: "ii = quot i" "jj = quot j"
  have 0: "\<exists>i j. myrel R i j \<and> ii = quot i \<and> jj = quot j" using m defs by auto
  show ?thesis unfolding defs[symmetric] using 0 proof coinduct
  	case (mmyrel ii jj)
  	then show ?case apply auto
  		apply (meson myrel.cases quot)  
  		apply (meson myrel.cases quot)
      apply(subst (asm) myrel.simps) apply auto
      unfolding str_quot F.rel_map apply(drule F.rel_mono_strong) by auto
  qed
qed

lemma quot_car_final_iff_carT: "quot i \<in> car_final \<longleftrightarrow> i \<in> carT"
unfolding car_final_closure_mybis  
by simp (metis mem_Collect_eq mybis_carT mybis_refl quot_def quot_def2)

lemma quot_mmyrel_myrel:
assumes R: "neper R" and m: "mmyrel R (quot i) (quot j)"
shows "myrel R i j"
using m proof coinduct
  case (myrel i j)
  then show ?case apply auto
    subgoal apply(subst (asm) mmyrel.simps) by (simp add: quot_car_final_iff_carT)
    subgoal apply(subst (asm) mmyrel.simps) by (simp add: quot_car_final_iff_carT)
    subgoal apply(subst (asm) mmyrel.simps) apply safe
      subgoal for _ _
      apply(subst (asm) str_quot)
        subgoal by (simp add: quot_car_final_iff_carT)
        apply(subst (asm) str_quot)
          subgoal by (simp add: quot_car_final_iff_carT)
          unfolding F.rel_map apply(drule F.rel_mono_strong) by auto . . 
qed


(* *)
lemma quotRlt: 
assumes R: "neper R" and t: "tr R i" and m: "mmybis_rlt R i i"
shows "ttr R (quotRlt R i)"
unfolding ttr_iff'[OF R] ccar_final_rlt'_def quotRlt_def apply simp
apply(rule exI[of _ "closure (rel_conj (rel_JT R) (mmybis_rlt R)) {i}"], safe)
  subgoal apply(rule exI[of _ i])
  using assms unfolding rel_set_def closure_def apply auto 
    apply (metis (mono_tags, lifting) CollectD CollectI neper_classes_eq neper_rel_JT relcomppI)
    by (smt (verit, ccfv_threshold) neper_rel_JT neper_relcompp_leq relcompp.cases relcomppI) 
  subgoal unfolding rel_JTT_def
  using assms unfolding rel_set_def closure_def apply auto 
    apply (metis (mono_tags, lifting) CollectD CollectI neper_classes_eq neper_rel_JT relcomppI)
    by (smt (verit, ccfv_threshold) neper_rel_JT neper_relcompp_leq relcompp.cases relcomppI) .

lemma quotRlt_mmybis_rlt_rel_JTT: 
assumes R: "neper R" and  t: "tr R i" "tr R j" and m: "mmybis_rlt R i j"
shows "rel_JTT R (quotRlt R i) (quotRlt R j)"
unfolding rel_JTT_def quotRlt_def
using assms unfolding rel_set_def closure_def  
 by auto (smt (verit, del_insts) mem_Collect_eq mmybis_rlt_param' mmybis_rlt_sym 
   mmybis_rlt_trans neper_classes_eq neper_rel_JT relcomppI tr_rel_JT)+

lemma quotRlt_surj: 
assumes R: "neper R" and t: "ttr R ii" and r: "rel_JTT R ii ii"
shows "\<exists>i. tr R i \<and> mmybis_rlt R i i \<and> rel_JTT R (quotRlt R i) ii"
using assms unfolding quotRlt_def ttr_iff'[OF R] ccar_final_rlt'_def apply clarsimp
unfolding rel_JTT_def[symmetric] 
by (metis (no_types, lifting) mem_Collect_eq mmybis_rlt_refl neper_classes_eq neper_rel_JTT)
 
(* *)
definition hh :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a JTT \<Rightarrow> 'a JTT" where 
"hh R ii = closure mybis 
  {h R (SOME i. tr R i \<and> rel_set (rel_JT R) ii (closure (rel_conj (rel_JT R) (mmybis_rlt R)) {i}))}"

lemma hh: 
assumes R: "neper R" and m: "rel_JTT R ii ii" and t: "ttr R ii"
shows "\<exists>i. hh R ii = closure mybis {h R i} \<and> 
    tr R i \<and> rel_set (rel_JT R) ii (closure (rel_conj (rel_JT R) (mmybis_rlt R)) {i})" 
proof-
  have "\<exists>i. tr R i \<and> rel_set (rel_JT R) ii (closure (rel_conj (rel_JT R) (mmybis_rlt R)) {i})"
  using m t unfolding ttr_iff'[OF R] ccar_final_rlt'_def apply safe
    by (metis (no_types, lifting) R mem_Collect_eq neper_classes_eq neper_rel_JTT rel_JTT_def)
  thus ?thesis unfolding hh_def 
  	by (metis (no_types, lifting) verit_sko_ex')
qed
  
lemma hh_car_final: 
assumes R: "neper R" and m: "rel_JTT R ii ii" and t: "ttr R ii"
shows "hh R ii \<in> car_final"
using hh[OF assms] unfolding car_final_closure_mybis  
	using R tr_h_carT by blast 

lemma neper_rel_conj_rel_JT_mmybis_rlt: 
assumes R: "neper R"
shows "neper (rel_conj (rel_JT R) (mmybis_rlt R))"
unfolding neper_def per_def OO_def apply safe  
  apply (smt (verit, ccfv_threshold) assms geterReprOn_related 
 mem_Collect_eq mmybis_rlt_sym neper_classes_eq neper_rel_JT)
 apply (smt (verit, best) assms mem_Collect_eq mmybis_rlt_param' mmybis_rlt_trans 
  neper_classes_eq neper_rel_JT)
 by (meson assms ex_carT_rel_JT ex_h_tr_myrel mmybis_rlt_refl rel_JT_implies_myrel tr_rel_JT)

lemma rel_JT_rel_conj_mmybis_rlt: "neper R \<Longrightarrow> tr R i \<Longrightarrow> tr R j \<Longrightarrow> 
rel_JT R i j \<Longrightarrow> rel_conj (rel_JT R) (mmybis_rlt R) i j"
unfolding OO_def using mmybis_rlt_refl tr_rel_JT by blast

lemma tr_rel_implies_rel_conj_rel_JT_mmybis_rlt: 
"neper R \<Longrightarrow> tr R i \<Longrightarrow> tr R j \<Longrightarrow> rel_conj (rel_JT R) (mmybis_rlt R) i i"
by (simp add: rel_JT_rel_conj_mmybis_rlt tr_rel_JT)

lemma mmybis_rlt_aux: 
assumes R: "neper R"
and i: "rel_set (rel_JT R) ii (closure (rel_conj (rel_JT R) (mmybis_rlt R)) {i})"
and j: "rel_set (rel_JT R) jj (closure (rel_conj (rel_JT R) (mmybis_rlt R)) {j})"
and t: "tr R i" "tr R j"
and iijj: "rel_set (rel_JT R) ii jj"
shows "mmybis_rlt R i j"
proof-
  have 0: "rel_set (rel_JT R) 
      (closure (rel_conj (rel_JT R) (mmybis_rlt R)) {i})
      (closure (rel_conj (rel_JT R) (mmybis_rlt R)) {j})"
  using assms  
  by (metis (no_types, lifting) CollectD CollectI neper_classes_eq neper_rel_JT set.rrel_neper)
  have "rel_conj (rel_JT R) (mmybis_rlt R) i j" 
  apply(rule rel_set_closure_rel_conj[OF _ _ _ _ 0])
   using R t apply (auto simp: tr_rel_implies_rel_conj_rel_JT_mmybis_rlt)  
   using neper_rel_conj_rel_JT_mmybis_rlt by blast  
  thus ?thesis using t 
  	using R rel_JT_mmybis_rlt_compp by blast
qed

lemma hh_mmyrel: 
assumes R: "neper R" and m: "rel_JTT R ii jj" and ti: "ttr R ii" and tj: "ttr R jj"
shows "mmyrel R (hh R ii) (hh R jj)"
proof-
  have mi: "rel_JTT R ii ii" and mj: "rel_JTT R jj jj"
  	by (metis CollectD CollectI R neper_classes_eq neper_rel_JTT ti tj ttr_iff)+
  show ?thesis
  using hh[OF R mi ti] hh[OF R mj tj] unfolding car_final_closure_mybis quot_def[symmetric] apply auto
  apply(rule quot_myrel_mmyrel) using assms  
  apply auto
  apply(rule mmybis_rlt_implies_myrel_h) 
  by (auto simp add: mmybis_rlt_aux rel_JTT_def)
qed

lemma mmybis_rlt_hh_aux: 
assumes R: "neper R"
and t: "tr R i" "tr R j" 
and ci: "rel_set (rel_JT R) ii (closure (rel_conj (rel_JT R) (mmybis_rlt R)) {i})"
and cj: "rel_set (rel_JT R) jj (closure (rel_conj (rel_JT R) (mmybis_rlt R)) {j})"
and mm: "mmybis_rlt R i j" 
shows "rel_set (rel_JT R) ii jj"  
proof-
  have "rel_set (rel_JT R) 
          (closure (rel_conj (rel_JT R) (mmybis_rlt R)) {i})
          (closure (rel_conj (rel_JT R) (mmybis_rlt R)) {i})"
  using t mm  
  by (metis R mmybis_rlt_refl quotRlt_def quotRlt_mmybis_rlt_rel_JTT rel_JTT_def)
  thus ?thesis using R ci cj 
  	by (smt (verit, best) ccar_final_rlt'_def ccar_final_rlt_aux mem_Collect_eq 
       mm neper_classes_eq neper_rel_JT neper_rel_JTT quotRlt_def quotRlt_mmybis_rlt_rel_JTT 
      rel_JTT_def rel_set_closure_eq set.rrel_neper t(1) t(2) ttr_iff')
qed

lemma hh_mmyrel_back: 
assumes R: "neper R" and mi: "rel_JTT R ii ii" and mj: "rel_JTT R jj jj" 
and ti: "ttr R ii" and tj: "ttr R jj" 
and m: "mmyrel R (hh R ii) (hh R jj)"
shows "rel_JTT R ii jj" 
unfolding rel_JTT_def  
  using m hh[OF R mi ti] hh[OF R mj tj] unfolding car_final_closure_mybis quot_def[symmetric] 
  apply auto apply(drule quot_mmyrel_myrel[OF R]) 
  apply(drule myrel_h_implies_mmybis_rlt[OF R]) apply auto
  using R mmybis_rlt_hh_aux by blast

lemma tr_quot_ttr: 
assumes R: "neper R" and t: "tr R j"
shows "ttr R (quotRlt R j)"
proof-
  obtain i where i: "i \<in> ccarT_rlt R" "rel_JT R i j" using t unfolding tr_iff by auto
  show ?thesis
  unfolding ttr_iff'[OF R] tr_iff quotRlt_def ccar_final_rlt'_def apply auto
  apply(rule exI[of _ "closure (rel_conj (rel_JT R) (mmybis_rlt R)) {i}"]) apply auto
    subgoal apply(rule exI[of _ j]) apply auto 
      subgoal apply(rule exI[of _ i]) using i by auto
      subgoal by (metis (no_types, opaque_lifting) R ccarT_rlt_param i(1) i(2) mmybis_rlt_param' 
                mmybis_rlt_refl quotRlt_def quotRlt_mmybis_rlt_rel_JTT rel_JTT_def rel_setD2 
              tr_iff tr_rel_JT) .
    subgoal unfolding rel_JTT_def rel_set_def closure_def apply auto 
    	apply (smt (verit, best) CollectD CollectI R i(2) neper_classes_eq neper_rel_JT relcomppI)
     by (smt (verit, ccfv_SIG) R i(2) mem_Collect_eq neper_classes_eq neper_rel_JT relcomppI) . 
qed

lemma hh_mmyrel_ex: 
assumes R: "neper R" and m: "mmyrel R ii ii" and ii: "ii \<in> car_final" 
shows "\<exists>jj. ttr R jj \<and> rel_JTT R jj jj \<and> mmyrel R ii (hh R jj)"
proof-
  obtain i where i: "i \<in> carT" and ii: "ii = quot i" 
  using ii unfolding car_final_closure_mybis quot_def by auto
  have m: "myrel R i i" using quot_mmyrel_myrel[OF R m[unfolded ii]] .
  obtain j where j: "tr R j" "myrel R i (h R j)" using ex_h_tr_myrel[OF R i m] by auto
  
  show ?thesis proof(rule exI[of _ "quotRlt R j"], safe)
    show 1: "ttr R (quotRlt R j)" by (simp add: R j(1) tr_quot_ttr)
    show 2: "rel_JTT R (quotRlt R j) (quotRlt R j)" 
    by (simp add: R j(1) mmybis_rlt_refl quotRlt_mmybis_rlt_rel_JTT)
    obtain j' where h: "hh R (quotRlt R j) = quot (h R j')"
    and 3: "tr R j'" "rel_set (rel_JT R) (quotRlt R j) (closure (rel_conj (rel_JT R) (mmybis_rlt R)) {j'})"
    using hh[OF R 2 1, unfolded quot_def[symmetric]] by auto

    have mb: "mmybis_rlt R j j'"  
    	by (metis "2" "3"(1) "3"(2) R j(1) mmybis_rlt_aux quotRlt_def rel_JTT_def)

    have "myrel R (h R j) (h R j')" using mmybis_rlt_implies_myrel_h[OF R j(1) 3(1) mb] .
    hence my: "myrel R i (h R j')" using j(2) R myrel_trans by blast
    show "mmyrel R ii (hh R (quotRlt R j))"
    unfolding h ii using quot_myrel_mmyrel[OF R my] .
  qed
qed 

proposition bij_upto_hh: 
assumes "neper R"
shows "bij_upto 
   (restr (rel_JTT R) (ttr R))
   (restr (mmyrel R) (\<lambda>i. i \<in> car_final))
   (hh R)"
apply(rule bij_uptoI)
  subgoal by (meson assms mmyrel.cases neper_Some neper_mmyrel neper_restr)
  subgoal unfolding restr_def  
  	by (metis assms hh_mmyrel mmyrel.cases)
  subgoal by (metis assms hh_mmyrel_back restr_def)
  subgoal by (metis assms hh_car_final hh_mmyrel_ex restr_def) .

lemma mmybis_rlt_eq[simp]: "mmybis_rlt (=) = mybis"
unfolding mmybis_rlt_def mybis_rlt_eq ..

lemmas rel_conj_eq = eq_comp_r[simp]

lemma h_eq[simp]: "h (=) = id" unfolding h_def fun_eq_iff getReprOn_def by auto

lemma ccar_final_rlt_eq[simp]: "ccar_final_rlt (=) = car_final"
unfolding ccar_final_rlt_def car_final_rlt_eq ..

lemma closure_eq[simp]: "closure (=) A = A"
unfolding closure_def by auto

lemma ttr_eq[simp]: "ttr (=) = (\<lambda>ii. ii \<in> car_final)" unfolding ttr_def by simp

lemma ccarT_rlt_eq[simp]: "ccarT_rlt (=) = carT"
unfolding ccarT_rlt_def carT_rlt_eq ..

lemma tr_eq[simp]: "tr (=) = (\<lambda>ii. ii \<in> carT)"
unfolding tr_def by simp

proposition hh_eq[simp]: "ii \<in> car_final \<Longrightarrow> hh (=) ii = ii"
unfolding hh_def closure_def fun_eq_iff apply auto 
	apply (metis (mono_tags, lifting) CollectI quot_def2 quot_surj verit_sko_ex') 
  by (metis (mono_tags, lifting) CollectD quot_def2 quot_surj someI2_ex)


(* *)

definition gg where 
"gg R = inv_upto 
         (restr (rel_JTT R) (ttr R))
         (restr (mmyrel R) (\<lambda>i. i \<in> car_final)) 
         (hh R)"

lemma neper_restr_mmyrel_car_final: 
"neper R \<Longrightarrow> neper (restr (mmyrel R) (\<lambda>i. i \<in> car_final))"
by (meson mmyrel.cases neper_Some neper_mmyrel neper_restr)

lemma neper_restr_rel_JTT_ttr: 
"neper R \<Longrightarrow> neper (restr (rel_JTT R) (ttr R))"
by (metis (no_types, lifting) hh_mmyrel_ex mmyrel.cases neper_Some 
 neper_mmyrel neper_rel_JTT neper_restr)

proposition bij_upto_gg: 
assumes "neper R"
shows "bij_upto 
   (restr (mmyrel R) (\<lambda>ii. ii \<in> car_final))
   (restr (rel_JTT R) (ttr R))
   (gg R)"
by (simp add: assms bij_upto_hh gg_def inv_upto_bij_upto neper_restr_mmyrel_car_final 
  neper_restr_rel_JTT_ttr)

lemma mmyrel_eq[simp]: "ii \<in> car_final \<Longrightarrow> jj \<in> car_final \<Longrightarrow> mmyrel (=) ii jj = (ii = jj)"
unfolding fun_eq_iff apply(standard)
  subgoal by (smt (verit, best) hh_eq hh_mmyrel_back mmyrel.cases neper_eq rel_JTT_eq ttr_eq)
  subgoal using hh_mmyrel by fastforce . 


lemma bij_betw_hh: "bij_betw (hh (=)) car_final car_final"
by (simp add: bij_betwI')

proposition gg_eq[simp]: "ii \<in> car_final \<Longrightarrow> gg (=) ii = ii"
unfolding gg_def[unfolded rrel_eq rel_JTT_def rel_JT_eq restr_def, simped, unfolded rel_JT_eq]
unfolding rel_JT_eq apply simp apply(rule inv_upto_eqI[of _ car_final])
unfolding perOfSet_def fun_eq_iff using bij_betw_hh by auto
 
(* *)

definition tt where "tt = (\<lambda>ii. ii \<in> car_final)"

lemma Collect_tt: "Collect tt = car_final"
unfolding tt_def by auto

thm JF.type_definition_JF[unfolded Collect_tt[symmetric]]

thm JFrel_inv_imagep_mmyrel

lemmas bij_uptoRep_JF = bij_upto_transportFromRaw
 [OF JF.type_definition_JF[unfolded Collect_tt[symmetric]] 
     JFrel_inv_imagep_mmyrel, unfolded tt_def, OF _ bij_upto_gg] 
      
wide_typedef JF rel: "\<lambda>R _ _ _ _ _. JFrel R" rep: "\<lambda>R _ _ _ _ _ . (gg R) o Rep_JF" 
cond: "\<lambda>R z1 z2 z3 z4 z5. z1 = Fmap \<and> z2 = Fmap \<and> z3 = Fset2 \<and> z4 = Fset1 \<and> z5 = Fset2" 
  subgoal for R unfolding rrel_eq by (auto simp: rel_fun_def)
  subgoal using JF.rel_eq .
  subgoal for R z1 z2 z3 z4 z5 unfolding rrel_eq apply simp
  unfolding ccar_final_rlt_def[symmetric]   
  unfolding rel_JT_def[symmetric] rel_JTT_def[symmetric] 
  using bij_uptoRep_JF[of R]
  unfolding closure_def ttr_def by auto 
  subgoal unfolding fun_eq_iff by simp 
  subgoal by simp .

(*<*)
end
(*>*)



(*  Title:       LFP
    Authors:     Jasmin Blanchette, Andrei Popescu, Dmitriy Traytel
    Maintainer:  Dmitriy Traytel <traytel at inf.ethz.ch>
*)

section \<open>Least Fixpoint (a.k.a. Datatype)\<close>

(*<*)
theory LFP
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

axiomatization where Frel_neper:
  "\<And>R1 R2. neper R1 \<Longrightarrow> neper R2 \<Longrightarrow> neper (Frel R1 R2)"
ML Wide_Database.register_wide
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


subsection\<open>Algebra\<close>

definition alg where
  "alg B s = ((\<forall>y \<in> Fin (UNIV :: 'a set) B. s y \<in> B))"

lemma alg_Fset: "\<lbrakk>alg B s; Fset2 x \<subseteq> B\<rbrakk> \<Longrightarrow> s x \<in> B"
  apply (tactic \<open>dtac @{context} @{thm iffD1[OF alg_def]} 1\<close>)
  apply (erule bspec)
  apply (rule CollectI)
  apply (rule conjI[OF subset_UNIV])
  apply assumption
  done

lemma alg_not_empty:
  "alg B s \<Longrightarrow> B \<noteq> {}"
   apply (rule notI)
   apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
   apply (frule alg_Fset)

(* ORELSE of the following three possibilities *)

     apply (rule subset_emptyI)
     apply (erule F.wit)

   apply (erule emptyE)
  done


subsection \<open>Morphism\<close>

definition mor where
  "mor B s B' s' f =
   ((\<forall>a \<in> B. f a \<in> B') \<and>
    (\<forall>z \<in> Fin (UNIV :: 'a set) B. f (s z) = s' (Fmap id f z)))"

lemma morE: "\<lbrakk>mor B s B' s' f; z \<in> Fin UNIV B\<rbrakk> \<Longrightarrow> f (s z) = s' (Fmap id f z)"
  apply (tactic \<open>dtac @{context} @{thm iffD1[OF mor_def]} 1\<close>)
  apply (erule conjE)
  apply (erule bspec)
  apply assumption
  done

lemma mor_incl: "\<lbrakk>B \<subseteq> B'\<rbrakk> \<Longrightarrow> mor B s B' s id"
  apply (tactic \<open>rtac @{context} (@{thm mor_def} RS iffD2) 1\<close>)
  apply (rule conjI)

    apply (rule ballI)
    apply (erule subsetD)
    apply (erule ssubst_mem[OF id_apply])

   apply (rule ballI)
   apply (rule trans)
    apply (rule id_apply)
   apply (tactic \<open>stac @{context} @{thm F.map_id} 1\<close>)
   apply (rule refl)
  done

lemma mor_comp:
  "\<lbrakk>mor B s B' s' f;
    mor B' s' B'' s'' f'\<rbrakk> \<Longrightarrow>
   mor B s B'' s'' (f' o f)"
  apply (tactic \<open>dtac @{context} (@{thm mor_def} RS iffD1) 1\<close>)
  apply (tactic \<open>dtac @{context} (@{thm mor_def} RS iffD1) 1\<close>)
  apply (tactic \<open>rtac @{context} (@{thm mor_def} RS iffD2) 1\<close>)
  apply (erule conjE)+
  apply (rule conjI)
    apply (rule ballI)
    apply (rule ssubst_mem[OF o_apply])
    apply (erule bspec)
    apply (erule bspec)
   apply assumption

   apply (rule ballI)
   apply (rule trans[OF o_apply])
   apply (rule trans)
    apply (rule trans)
     apply (drule bspec[rotated])
      apply assumption
     apply (erule arg_cong)
    apply (erule CollectE conjE)+
    apply (erule bspec)
    apply (rule CollectI)
    apply (rule conjI)
     apply (rule subset_UNIV)
     apply (rule ord_eq_le_trans)
      apply (rule F.set_map(2))
     apply (rule image_subsetI)
     apply (erule bspec)
     apply (erule subsetD)
     apply assumption
   apply (rule arg_cong[OF Fmap_comp_id])
  done

lemma mor_cong: "\<lbrakk> f' = f; g' = g; mor B s B' s' f\<rbrakk> \<Longrightarrow>
  mor B s B' s' f'"
  apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
  apply assumption
  done

lemma mor_str:
  "mor UNIV (Fmap id s) UNIV s s"
  apply (rule iffD2)
   apply (rule mor_def)
  apply (rule conjI)
    apply (rule ballI)
    apply (rule UNIV_I)
   apply (rule ballI)
  apply (rule refl)
  done


subsection\<open>Bounds\<close>

type_synonym bd_type_F' = "bd_type_F + (bd_type_F, bd_type_F) F"
type_synonym SucFbd_type = "(bd_type_F' set)"
type_synonym 'a1 ASucFbd_type = "(SucFbd_type \<Rightarrow> ('a1 + bool))"

abbreviation "Fbd' \<equiv> bd_F +c |UNIV :: (bd_type_F, bd_type_F) F set|"
lemma Fset1_bd_incr: "\<And>x. |Fset1 x| \<le>o Fbd'"
  by (rule ordLeq_transitive[OF F.set_bd(1) ordLeq_csum1[OF F.bd_Card_order]])
lemma Fset2_bd_incr: "\<And>x. |Fset2 x| \<le>o Fbd'"
  by (rule ordLeq_transitive[OF F.set_bd(2) ordLeq_csum1[OF F.bd_Card_order]])

lemmas Fbd'_Card_order = Card_order_csum
lemmas Fbd'_Cinfinite = Cinfinite_csum1[OF F.bd_Cinfinite]
lemmas Fbd'_Cnotzero = Cinfinite_Cnotzero[OF Fbd'_Cinfinite]
lemmas Fbd'_card_order = card_order_csum[OF F.bd_card_order card_of_card_order_on]

abbreviation SucFbd :: "SucFbd_type rel" where "SucFbd \<equiv> cardSuc (Fbd')"
abbreviation ASucFbd :: "('a1) ASucFbd_type rel" where "ASucFbd \<equiv> ( |UNIV| +c ctwo ) ^c SucFbd"

lemma Fset1_bd: "|Fset1 x| \<le>o bd_F"
   apply (rule F.set_bd(1))
  done

lemma Fset2_bd: "|Fset2 x| \<le>o bd_F"
   apply (rule F.set_bd(2))
  done

lemmas SucFbd_Card_order = cardSuc_Card_order[OF Card_order_csum]
lemmas SucFbd_Cinfinite = Cinfinite_cardSuc[OF Fbd'_Cinfinite]
lemmas SucFbd_Cnotzero = Cinfinite_Cnotzero[OF SucFbd_Cinfinite]
lemmas worel_SucFbd = Card_order_wo_rel[OF SucFbd_Card_order]
lemmas ASucFbd_Cinfinite = Cinfinite_cexp[OF ordLeq_csum2[OF Card_order_ctwo] SucFbd_Cinfinite]


subsection\<open>Minimal Algebras\<close>

(* These are algebras generated by the empty set. *)
abbreviation min_G where
  "min_G As1_As i \<equiv> (\<Union>j \<in> underS SucFbd i. As1_As j)"

abbreviation min_H where
  "min_H s As1_As i \<equiv> min_G As1_As i \<union> s ` Fin (UNIV :: 'a set) (min_G As1_As i)"

abbreviation min_algs where
  "min_algs s \<equiv> wo_rel.worec SucFbd (min_H s)"

definition min_alg :: "(('a, 'b) F \<Rightarrow> 'b) \<Rightarrow> 'b set" where
  "min_alg s = (\<Union>i \<in> Field (SucFbd :: SucFbd_type rel). min_algs s i)"

lemma min_algs:
  "i \<in> Field SucFbd \<Longrightarrow> min_algs s i = min_H s (min_algs s) i"
  apply (rule fun_cong[OF wo_rel.worec_fixpoint[OF worel_SucFbd]])
  apply (rule iffD2)
   apply (rule meta_eq_to_obj_eq)
   apply (rule wo_rel.adm_wo_def[OF worel_SucFbd])
  apply (rule allI)+
  apply (rule impI)

   apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])
    apply (rule SUP_cong)
     apply (rule refl)
    apply (drule bspec)
     apply assumption
    apply (erule arg_cong)

   apply (rule image_cong)
    apply (rule arg_cong[of _ _ "Fin UNIV"])
     apply (rule SUP_cong)
      apply (rule refl)
     apply (drule bspec)
      apply assumption
     apply (erule arg_cong)
     apply (rule refl)
  done

lemma min_algs_mono: "relChain SucFbd (%i. min_algs s i)"
  apply (tactic \<open>rtac @{context} @{thm iffD2[OF meta_eq_to_obj_eq[OF relChain_def]]} 1\<close>)
  apply (rule allI)+
  apply (rule impI)
  apply (rule case_split)
   apply (rule xt1(3))
    apply (rule min_algs)
    apply (erule FieldI2)
   apply (rule subsetI)
   apply (rule UnI1)
   apply (rule UN_I)
    apply (erule underS_I)
    apply assumption
   apply assumption
  apply (rule equalityD1)
  apply (drule notnotD)
  apply (erule arg_cong)
  done

lemma SucFbd_limit: "\<lbrakk>x1 \<in> Field SucFbd\<rbrakk>
 \<Longrightarrow> \<exists>y \<in> Field SucFbd. (x1 \<noteq> y \<and> (x1, y) \<in> SucFbd)"
  apply (rule rev_mp)
   apply (rule Cinfinite_limit_finite)
     apply (rule finite.insertI)
     apply (rule finite.emptyI)
    apply (erule insert_subsetI)
    apply (rule empty_subsetI)
   apply (rule SucFbd_Cinfinite)
  apply (rule impI)
  apply (erule bexE)
  apply (rule bexI)

    apply (erule bspec)
    apply (rule insertI1)
  apply assumption
  done

lemma alg_min_alg: "alg (min_alg s) s"
  apply (tactic \<open>rtac @{context} (@{thm alg_def} RS iffD2) 1\<close>)
   apply (rule ballI)
   apply (erule CollectE conjE)+

  apply (rule bexE)
   apply (rule cardSuc_UNION_Cinfinite)
      apply (rule Fbd'_Cinfinite)
     apply (rule min_algs_mono)

    apply (erule subset_trans[OF _ equalityD1[OF min_alg_def]])
   apply (rule ordLeq_transitive)
    apply (rule Fset2_bd_incr)
   apply (rule ordLeq_refl)
   apply (rule Fbd'_Card_order)

  apply (rule bexE)
   apply (rule cardSuc_UNION_Cinfinite)
      apply (rule Fbd'_Cinfinite)
     apply (rule min_algs_mono)

    apply (erule subset_trans[OF _ equalityD1[OF min_alg_def]])
   apply (rule ordLeq_transitive)
    apply (rule Fset2_bd_incr)
   apply (rule ordLeq_refl)
   apply (rule Fbd'_Card_order)

  apply (rule bexE)
   apply (rule SucFbd_limit)
   apply assumption
  apply (rule subsetD[OF equalityD2[OF min_alg_def]])
  apply (rule UN_I)
   apply (erule thin_rl)
   apply (erule thin_rl)
   apply (erule thin_rl)
   apply (erule thin_rl)
   apply (erule thin_rl)
   apply (erule thin_rl) (* m + 3 * n *)
   apply assumption
  apply (rule subsetD)
   apply (rule equalityD2)
   apply (rule min_algs)
   apply assumption
  apply (rule UnI2)
  apply (rule image_eqI)
   apply (rule refl)
  apply (rule CollectI)
  apply (rule conjI)
   apply assumption

  apply (erule thin_rl)
  apply (erule thin_rl)
  apply (erule thin_rl)
  apply (erule conjE)+
   apply (erule subset_trans)
   apply (rule UN_upper)
   apply (erule underS_I)
  apply assumption
  done

lemmas SucFbd_ASucFbd = ordLess_ordLeq_trans[OF
    ordLess_ctwo_cexp
    cexp_mono1[OF ordLeq_csum2[OF Card_order_ctwo]],
    OF SucFbd_Card_order SucFbd_Card_order]

lemma card_of_min_algs:
  fixes s :: "('a, 'b) F \<Rightarrow> 'b"
  shows "i \<in> Field (SucFbd :: SucFbd_type rel) \<longrightarrow>
    |min_algs s i| \<le>o (ASucFbd :: 'a ASucFbd_type rel)"
  apply (rule well_order_induct_imp[of _ "%i. |min_algs s i| \<le>o ASucFbd ", OF worel_SucFbd])
  apply (rule impI)
   apply (rule ordIso_ordLeq_trans)
    apply (rule card_of_ordIso_subst)
    apply (erule min_algs)
   apply (rule Un_Cinfinite_bound)

     apply (rule UNION_Cinfinite_bound)

       apply (rule ordLess_imp_ordLeq)
       apply (rule ordLess_transitive)
        apply (rule card_of_underS)
         apply (rule SucFbd_Card_order)
        apply assumption
       apply (rule SucFbd_ASucFbd)

      apply (rule ballI)
      apply (erule allE)
      apply (drule mp)
       apply (erule underS_E)
      apply (drule mp)
       apply (erule underS_Field)
      apply assumption

     apply (rule ASucFbd_Cinfinite)

    apply (rule ordLeq_transitive)
     apply (rule card_of_image)
    apply (rule ordLeq_transitive)
     apply (rule F.in_bd)
    apply (rule ordLeq_transitive)
     apply (rule cexp_mono1)
      apply (rule csum_mono1)
      apply (rule csum_mono2) (* REPEAT m *)
          apply (rule UNION_Cinfinite_bound)

            apply (rule ordLess_imp_ordLeq)
            apply (rule ordLess_transitive)
             apply (rule card_of_underS)
              apply (rule SucFbd_Card_order)
             apply assumption
            apply (rule SucFbd_ASucFbd)

           apply (rule ballI)
           apply (erule allE)
           apply (drule mp)
            apply (erule underS_E)
           apply (drule mp)
            apply (erule underS_Field)
           apply assumption

          apply (rule ASucFbd_Cinfinite)

     apply (rule Fbd'_Card_order)
    apply (rule ordIso_ordLeq_trans)
     apply (rule cexp_cong1)
      apply (rule ordIso_transitive)
       apply (rule csum_cong1)
       apply (rule ordIso_transitive)
        apply (tactic \<open>BNF_Tactics.mk_rotate_eq_tac @{context}
           (rtac @{context} @{thm ordIso_refl} THEN'
           FIRST' [rtac @{context} @{thm card_of_Card_order},
           rtac @{context} @{thm Card_order_csum},
           rtac @{context} @{thm Card_order_cexp}])
           @{thm ordIso_transitive} @{thm csum_assoc} @{thm csum_com} @{thm csum_cong}
           [1,2] [2,1] 1\<close>)
       apply (rule csum_absorb1)
        apply (rule ASucFbd_Cinfinite)

       apply (rule ordLeq_transitive)
        apply (rule ordLeq_csum1)
        apply (tactic \<open>FIRST' [rtac @{context} @{thm Card_order_csum}, rtac @{context} @{thm card_of_Card_order}] 1\<close>)
       apply (rule ordLeq_cexp1)
        apply (rule SucFbd_Cnotzero)
       apply (rule Card_order_csum)
      apply (rule csum_absorb1)
       apply (rule ASucFbd_Cinfinite)
      apply (rule ctwo_ordLeq_Cinfinite)
      apply (rule ASucFbd_Cinfinite)
     apply (rule Fbd'_Card_order)
    apply (rule ordIso_imp_ordLeq)
    apply (rule cexp_cprod_ordLeq)

       apply (rule Card_order_csum)
      apply (rule SucFbd_Cinfinite)
     apply (rule Fbd'_Cnotzero)
    apply (rule cardSuc_ordLeq)
    apply (rule Card_order_csum)

  apply (rule ASucFbd_Cinfinite)
  done

lemma card_of_min_alg:
  fixes s :: "('a, 'b) F \<Rightarrow> 'b"
  shows "|min_alg s| \<le>o (ASucFbd :: 'a ASucFbd_type rel)"
  apply (rule ordIso_ordLeq_trans)
   apply (rule card_of_ordIso_subst[OF min_alg_def])
  apply (rule UNION_Cinfinite_bound)

    apply (rule ordIso_ordLeq_trans)
     apply (rule card_of_Field_ordIso)
     apply (rule SucFbd_Card_order)
    apply (rule ordLess_imp_ordLeq)
    apply (rule SucFbd_ASucFbd)

   apply (rule ballI)
   apply (drule rev_mp)
    apply (rule card_of_min_algs)
   apply assumption
  apply (rule ASucFbd_Cinfinite)
  done

lemma least_min_algs: "alg B s \<Longrightarrow>
  i \<in> Field SucFbd \<longrightarrow> min_algs s i \<subseteq> B"
  apply (rule well_order_induct_imp[of _ "%i. min_algs s i \<subseteq> B", OF worel_SucFbd])
  apply (rule impI)
   apply (rule ord_eq_le_trans)
    apply (erule min_algs)
   apply (rule Un_least)
    apply (rule UN_least)
    apply (erule allE)
    apply (drule mp)
     apply (erule underS_E)
    apply (drule mp)
     apply (erule underS_Field)
    apply assumption
   apply (rule image_subsetI)
   apply (erule CollectE conjE)+
   apply (erule alg_Fset)

    apply (erule subset_trans)
    apply (rule UN_least)
    apply (erule allE)
    apply (drule mp)
     apply (erule underS_E)
    apply (drule mp)
     apply (erule underS_Field)
    apply assumption
  done

lemma least_min_alg: "alg B s \<Longrightarrow> min_alg s \<subseteq> B"
  apply (rule ord_eq_le_trans[OF min_alg_def])
  apply (rule UN_least)
  apply (drule least_min_algs)
  apply (drule mp)
   apply assumption
  apply assumption
  done

lemma mor_incl_min_alg:
  "alg B s \<Longrightarrow> mor (min_alg s) s B s id"
  apply (rule mor_incl)
  apply (erule least_min_alg)
  done

subsection \<open>Initiality\<close>

text\<open>The following ``happens" to be the type (for our particular construction)
of the initial algebra carrier:\<close>

type_synonym 'a1 Finit_type = "('a1, 'a1 ASucFbd_type) F \<Rightarrow> 'a1 ASucFbd_type"

type_synonym 'a IIT = "'a ASucFbd_type set \<times> 'a Finit_type"


subsection\<open>Initial Algebras\<close>

abbreviation II :: "'a1 IIT set" where
  "II \<equiv> {(B, s) |B s. alg B s}"

type_synonym 'a IT = "'a IIT \<Rightarrow> 'a ASucFbd_type" 


definition str_init :: "'a \<Rightarrow> ('a, 'a IT) F \<Rightarrow> ('a IT)"  
where
"str_init (dummy :: 'a) y (i :: 'a IIT) = snd i (Fmap id (\<lambda>f. f i) y)"

definition car_init :: "'a \<Rightarrow> ('a IT) set" 
where 
"car_init dummy \<equiv> min_alg (str_init dummy)"

term "min_alg :: (('a, 'a IIT) F \<Rightarrow> 'a IIT) \<Rightarrow> 'a IIT set"

lemma alg_select:
  "\<forall>i \<in> II. alg (fst i) (snd i)"
  apply (rule ballI)
  apply (erule CollectE exE conjE)+
  apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
  unfolding fst_conv snd_conv  
  apply assumption
  done

lemma mor_select:
  "\<lbrakk>i \<in> II;
    mor (fst i) (snd i) UNIV s' f\<rbrakk> \<Longrightarrow>
    mor(car_init dummy) (str_init dummy) UNIV s' (f \<circ> (\<lambda>h. h i))"
  unfolding car_init_def
  apply (rule mor_cong)
    apply (rule sym)
    apply (rule o_id)
   apply (rule sym)
   apply (rule o_id)
  apply (tactic \<open>rtac @{context} (Thm.permute_prems 0 1 @{thm mor_comp}) 1\<close>)
   apply (tactic \<open>etac @{context} (Thm.permute_prems 0 1 @{thm mor_comp}) 1\<close>)
   apply (tactic \<open>rtac @{context} (@{thm mor_def} RS iffD2) 1\<close>)
   apply (rule conjI)

     apply (rule ballI)
     apply (erule bspec[rotated])
     apply (erule CollectE)
    apply assumption

    apply (rule ballI)
   apply (rule str_init_def)

  apply (rule mor_incl_min_alg)
    (*alg_epi*)
  apply (erule thin_rl)+
  apply (tactic \<open>rtac @{context} (@{thm alg_def} RS iffD2) 1\<close>)
   apply (rule ballI)
   apply (erule CollectE conjE)+
   apply (rule CollectI)
   apply (rule ballI)
   apply (frule bspec[OF alg_select])
   apply (rule ssubst_mem[OF str_init_def])
   apply (erule alg_Fset)

    apply (rule ord_eq_le_trans)
     apply (rule F.set_map(2))
    apply (rule subset_trans)
     apply (erule image_mono)
    apply (rule image_Collect_subsetI)
    apply (erule bspec)
    apply assumption
  done

lemma init_unique_mor:
  "\<lbrakk>a \<in> car_init dummy;
    mor (car_init dummy) (str_init dummy) B s f;
    mor (car_init dummy) (str_init dummy) B s g\<rbrakk> \<Longrightarrow>
  f a = g a"
  unfolding car_init_def
   apply (erule prop_restrict)
   apply (rule least_min_alg)
   apply (tactic \<open>rtac @{context} (@{thm alg_def} RS iffD2) 1\<close>)
    apply (rule ballI)
    apply (rule CollectI)
    apply (erule CollectE conjE)+
    apply (rule conjI)

     apply (rule alg_Fset[OF alg_min_alg])
      apply (erule subset_trans)
      apply (rule Collect_restrict)

    apply (rule trans)
     apply (erule morE)
     apply (rule subsetD)
      apply (rule Fin_mono2)
       apply (rule Collect_restrict)
     apply (rule CollectI)
     apply (rule conjI)
      apply assumption
      apply assumption

    apply (rule trans)
     apply (rule arg_cong[OF F.map_cong0])
       apply (rule refl)
      apply (erule prop_restrict)
      apply assumption

    apply (rule sym)
    apply (erule morE)
    apply (rule subsetD)
     apply (rule Fin_mono2)
      apply (rule Collect_restrict)
    apply (rule CollectI)
    apply (rule conjI)
     apply assumption
     apply assumption
  done

abbreviation closed where
  "closed dummy phi \<equiv> ((\<forall>x \<in> Fin UNIV (car_init dummy).
   (\<forall>z \<in> Fset2 x. phi z) \<longrightarrow> phi (str_init dummy x)))"

lemma init_induct: "closed dummy phi \<Longrightarrow> (\<forall>x \<in> car_init dummy. phi x)"
  unfolding car_init_def
   apply (rule ballI)
   apply (erule prop_restrict)
   apply (rule least_min_alg)
   apply (tactic \<open>rtac @{context} (@{thm alg_def} RS iffD2) 1\<close>)

    apply (rule ballI)
    apply (rule CollectI)
    apply (erule CollectE conjE)+
    apply (rule conjI)

     apply (rule alg_Fset[OF alg_min_alg])
      apply (erule subset_trans)
      apply (rule Collect_restrict)

    apply (rule mp)
     apply (erule bspec)
     apply (rule CollectI)
     apply (rule conjI)
      apply assumption
      apply (erule subset_trans)
      apply (rule Collect_restrict)

     apply (rule ballI)
     apply (erule prop_restrict)
     apply assumption
  done


subsection \<open>The datatype\<close>

typedef (overloaded) 'a1 IF = "car_init (undefined :: 'a1)"
  unfolding car_init_def
  apply (rule iffD2)
   apply (rule ex_in_conv)
  apply (rule alg_not_empty)
  apply (rule alg_min_alg)
  done

definition ctor where "ctor = Abs_IF o str_init undefined o Fmap id Rep_IF"

lemma mor_Rep_IF:
  "mor (UNIV :: 'a IF set) ctor (car_init undefined) (str_init undefined) Rep_IF"
  unfolding mor_def ctor_def o_apply
  apply (rule conjI)
    apply (rule ballI)
    apply (rule Rep_IF)

   apply (rule ballI)
   apply (rule Abs_IF_inverse)
  unfolding car_init_def
   apply (rule alg_Fset[OF alg_min_alg])
    apply (rule ord_eq_le_trans[OF F.set_map(2)])
    apply (rule image_subsetI)
    apply (rule Rep_IF[unfolded car_init_def])
  done

lemma mor_Abs_IF:
  "mor (car_init undefined) (str_init undefined) UNIV ctor Abs_IF"
  unfolding mor_def ctor_def o_apply
  apply (rule conjI)
    apply (rule ballI)
    apply (rule UNIV_I)

   apply (rule ballI)
   apply (erule CollectE conjE)+
   apply (rule sym[OF arg_cong[OF trans[OF Fmap_comp_id Fmap_congL]]])
    apply (rule ballI[OF trans[OF o_apply]])
    apply (erule Abs_IF_inverse[OF subsetD])
    apply assumption
  done

lemma copy:
  "\<lbrakk>alg B s; bij_betw f B' B\<rbrakk> \<Longrightarrow>
   \<exists>f'. alg B' f' \<and> mor B' f' B s f"
  apply (rule exI)+
  apply (rule conjI)
   apply (tactic \<open>rtac @{context} (@{thm alg_def} RS iffD2) 1\<close>)
    apply (rule ballI)
    apply (erule CollectE conjE)+
    apply (rule subsetD)
    apply (rule equalityD1)
     apply (erule bij_betw_imp_surj_on[OF bij_betw_the_inv_into])
    apply (rule imageI)
    apply (erule alg_Fset)
     apply (rule ord_eq_le_trans)
      apply (rule F.set_map(2))
     apply (rule subset_trans)
      apply (erule image_mono)
     apply (rule equalityD1)
     apply (erule bij_betw_imp_surj_on)

  apply (tactic \<open>rtac @{context} (@{thm mor_def} RS iffD2) 1\<close>)
  apply (rule conjI)
    apply (erule bij_betwE)

   apply (rule ballI)
   apply (erule CollectE conjE)+
   apply (erule f_the_inv_into_f_bij_betw)
   apply (erule alg_Fset)
    apply (rule ord_eq_le_trans)
     apply (rule F.set_map(2))
    apply (rule subset_trans)
     apply (erule image_mono)
    apply (rule equalityD1)
    apply (erule bij_betw_imp_surj_on)
  done

lemma init_ex_mor:
  "\<exists>f. mor UNIV ctor UNIV s f"
  apply (insert ex_bij_betw[OF card_of_min_alg, of s])
  apply (erule exE)+
  apply (rule rev_mp)
   apply (rule copy[OF alg_min_alg])
    apply assumption
  apply (rule impI)
  apply (erule exE conjE)+

  apply (rule exI)+
  apply (rule mor_comp)
   apply (rule mor_Rep_IF)
  apply (rule mor_select)
   apply (rule CollectI)
   apply (rule exI)+
   apply (rule conjI)
    apply (rule refl)
   apply assumption
  unfolding fst_conv snd_conv
  apply (erule mor_comp)
  apply (rule mor_incl)
   apply (rule subset_UNIV)
  done

text \<open>Iteration\<close>

definition fold where
  "fold s = (SOME f. mor UNIV ctor UNIV s f)"

lemma mor_fold:
  "mor UNIV ctor UNIV s (fold s)"
  unfolding fold_def
  apply (rule rev_mp)
   apply (rule init_ex_mor)
  apply (rule impI)
  apply (erule exE)
  apply (rule someI[of "%(f :: ('a IF \<Rightarrow> 'b)).  mor UNIV ctor UNIV s f"])
  apply (erule mor_cong[OF fst_conv snd_conv])
  done

theorem fold:
  "(fold s) (ctor x) = s (Fmap id (fold s) x)"
  apply (rule morE)
   apply (rule mor_fold)
  apply (rule CollectI)
  apply (rule conjI)
   apply (rule subset_UNIV)
   apply (rule subset_UNIV)
  done


lemma mor_UNIV: "mor UNIV s UNIV s' f \<longleftrightarrow> f o s = s' o Fmap id f"
  apply (rule iffI)
    apply (rule ext)
    apply (rule trans)
     apply (rule o_apply)
    apply (rule trans)
     apply (erule morE)
     apply (rule CollectI)
     apply (rule conjI)
      apply (rule subset_UNIV)
      apply (rule subset_UNIV)
    apply (rule sym[OF o_apply])

  apply (tactic \<open>rtac @{context} (@{thm mor_def} RS iffD2) 1\<close>)
  apply (rule conjI)
    apply (rule ballI)
    apply (rule UNIV_I)
   apply (rule ballI)
  apply (drule iffD1[OF fun_eq_iff])
   apply (erule allE)+
   apply (rule trans)
    apply (erule trans[OF sym[OF o_apply]])
   apply (rule o_apply)
  done

lemma fold_unique_mor: "mor UNIV ctor UNIV s f \<Longrightarrow> f = fold s"
   apply (rule surj_fun_eq)
    apply (rule type_definition.Abs_image[OF type_definition_IF])
   apply (rule ballI)
   apply (rule init_unique_mor)
      apply assumption
    apply (rule mor_comp)
     apply (rule mor_Abs_IF)
    apply assumption
   apply (rule mor_comp)
    apply (rule mor_Abs_IF)
   apply (rule mor_fold)
  done

lemmas fold_unique = fold_unique_mor[OF iffD2[OF mor_UNIV]]

lemmas fold_ctor = sym[OF fold_unique_mor[OF mor_incl[OF subset_UNIV]]]

text \<open>Case distinction\<close>

lemmas ctor_o_fold =
  trans[OF fold_unique_mor[OF mor_comp[OF mor_fold mor_str]] fold_ctor]

(* unfold *)
definition "dtor = fold (Fmap id ctor)"

ML \<open>Local_Defs.fold @{context} @{thms dtor_def} @{thm ctor_o_fold}\<close>

lemma ctor_o_dtor: "ctor o dtor = id"
  unfolding dtor_def
  apply (rule ctor_o_fold)
  done

lemma dtor_o_ctor: "dtor o ctor = id"
  apply (rule ext)
  apply (rule trans[OF o_apply])
  apply (rule trans[OF fun_cong[OF dtor_def]])
  apply (rule trans[OF fold])
  apply (rule trans[OF Fmap_comp_id])
  apply (rule trans[OF Fmap_congL])
    apply (rule ballI)
    apply (rule trans[OF fun_cong[OF ctor_o_fold] id_apply])
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

text \<open>Primitive recursion\<close>

definition rec where
  "rec s = snd o fold (<ctor o Fmap id fst, s>)"

lemma fold_o_ctor: "fold s \<circ> ctor = s \<circ> Fmap id (fold s)"
  by (tactic \<open>rtac @{context} (BNF_Tactics.mk_pointfree2 @{context} @{thm fold}) 1\<close>)

lemmas fst_rec_pair =
  trans[OF fold_unique[OF
        trans[OF o_assoc[symmetric] trans[OF arg_cong2[of _ _ _ _ "(o)", OF refl
              trans[OF fold_o_ctor convol_o]]], OF trans[OF fst_convol]]]
    fold_ctor, unfolded F.map_comp0[of id, unfolded id_o] o_assoc,
    OF refl]

theorem rec: "rec s (ctor x) = s (Fmap id (<id, rec s>) x)"
  unfolding rec_def o_apply fold snd_convol'
    convol_expand_snd[OF fst_rec_pair] ..

lemma rec_unique:
  "f \<circ> ctor = s \<circ> Fmap id <id , f> \<Longrightarrow> f = rec s"
  unfolding rec_def convol_expand_snd'[OF fst_rec_pair]
  apply (rule fold_unique)
   apply (unfold convol_o id_o o_id F.map_comp0[symmetric]
      F.map_id0 o_assoc[symmetric] fst_convol)
   apply (erule arg_cong2[of _ _ _ _ BNF_Def.convol, OF refl])
  done


text \<open>Induction\<close>

theorem ctor_induct:
  "\<lbrakk>\<And>x. (\<And>a. a \<in> Fset2 x \<Longrightarrow> phi a) \<Longrightarrow> phi (ctor x)\<rbrakk> \<Longrightarrow> phi a"
  apply (rule mp)

   apply (rule impI)
    apply (rule iffD1[OF arg_cong[OF Rep_IF_inverse]])
    apply (erule bspec[OF _ Rep_IF])
  apply (rule init_induct)
   apply (rule ballI)
   apply (rule impI)
   apply (rule iffD2[OF arg_cong[OF morE[OF mor_Abs_IF]]])
    apply assumption
   apply (erule CollectE conjE)+
   apply (drule meta_spec)
   apply (drule meta_mp)
    apply (rule iffD1[OF arg_cong[OF Rep_IF_inverse]])
    apply (erule bspec)
    apply (drule rev_subsetD)
     apply (rule equalityD1)
     apply (rule F.set_map(2))
    apply (erule imageE)
    apply (tactic \<open>hyp_subst_tac @{context} 1\<close>)
    apply (rule ssubst_mem[OF Abs_IF_inverse])
     apply (erule subsetD)
     apply assumption
    apply assumption
    apply assumption
  done

theorem ctor_induct2:
  "\<lbrakk>\<And>x y. (\<And>a b. a \<in> Fset2 x \<Longrightarrow> b \<in> Fset2 y \<Longrightarrow> phi a b) \<Longrightarrow> phi (ctor x) (ctor y)\<rbrakk> \<Longrightarrow> phi a b"
  apply (rule rev_mp)
   apply (rule ctor_induct[of "\<lambda>a. (\<forall>x. phi a x)" a])
    apply (rule allI[OF ctor_induct])
    apply (drule meta_spec2)
    apply (tactic \<open>(dtac @{context} @{thm meta_mp} THEN_ALL_NEW Goal.norm_hhf_tac @{context}) 1\<close>)
     apply (drule meta_spec)+
     apply (erule meta_mp[OF spec])
     apply assumption
     apply assumption

  apply (rule impI)
  apply (erule conjE allE)+
   apply assumption
  done


subsection \<open>The Result as an BNF\<close>

text\<open>The map operator\<close>

abbreviation IFmap where "IFmap f \<equiv> fold (ctor o Fmap f id)"

theorem IFmap:
  "(IFmap f) o ctor = ctor o (Fmap f (IFmap f))"
  apply (rule ext)
  apply (rule trans[OF o_apply])
  apply (rule trans[OF fold])
  apply (rule trans[OF o_apply])
  apply (rule trans[OF arg_cong[OF Fmap_comp_id]])
  apply (rule trans[OF arg_cong[OF F.map_cong0]])
     apply (rule refl)
    apply (rule trans[OF o_apply])
    apply (rule id_apply)
  apply (rule sym[OF o_apply])
  done

lemmas IFmap_simps = o_eq_dest[OF IFmap]

lemma IFmap_unique:
  "\<lbrakk>u o ctor = ctor o Fmap f u\<rbrakk> \<Longrightarrow> u = IFmap f"
  apply (rule fold_unique)
  unfolding o_assoc[symmetric] F.map_comp0[symmetric] id_o o_id
   apply assumption
  done

theorem IFmap_id: "IFmap id = id"
  apply (rule sym)
  apply (rule IFmap_unique)
   apply (rule trans[OF id_o])
   apply (rule trans[OF sym[OF o_id]])
   apply (rule arg_cong[OF sym[OF F.map_id0]])
  done

theorem IFmap_comp: "IFmap (g o f) = IFmap g o IFmap f"
  apply (rule sym)
  apply (rule IFmap_unique)
   apply (rule ext)
   apply (rule trans[OF o_apply])
   apply (rule trans[OF o_apply])
   apply (rule trans[OF arg_cong[OF IFmap_simps]])
   apply (rule trans[OF IFmap_simps])
   apply (rule trans[OF arg_cong[OF F.map_comp]])
   apply (rule sym[OF o_apply])
  done


text\<open>The bound\<close>

abbreviation IFbd where "IFbd \<equiv> bd_F"

lemmas IFbd_card_order = F.bd_card_order
lemmas IFbd_Cinfinite = F.bd_Cinfinite
lemmas IFbd_cinfinite = conjunct1[OF IFbd_Cinfinite]


text \<open>The set operator\<close>

(* "IFcol" stands for "collect"  *)

abbreviation IFcol where "IFcol \<equiv> (\<lambda>X. Fset1 X \<union> (\<Union>(Fset2 X)))"

abbreviation IFset where "IFset \<equiv> fold IFcol"

abbreviation IFin where "IFin A \<equiv> {x. IFset x \<subseteq> A}"

lemma IFset: "IFset o ctor = IFcol o (Fmap id IFset)"
  apply (rule ext)
  apply (rule trans[OF o_apply])
  apply (rule trans[OF fold])
  apply (rule sym[OF o_apply])
  done

theorem IFset_simps:
  "IFset (ctor x) = Fset1 x \<union> ((\<Union>a \<in> Fset2 x. IFset a))"
  apply (rule trans[OF o_eq_dest[OF IFset]])
  apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])
   apply (rule trans[OF F.set_map(1) trans[OF fun_cong[OF image_id] id_apply]])
   apply (rule arg_cong[OF F.set_map(2)])
  done

lemmas Fset1_IFset = xt1(3)[OF IFset_simps Un_upper1]
lemmas Fset2_IFset = subset_trans[OF UN_upper xt1(3)[OF IFset_simps Un_upper2]]

text \<open>The BNF conditions for IF\<close>

lemma IFset_natural0:
  fixes x :: "'a IF"
  shows "f ` (IFset x) = IFset (IFmap f x)"
  apply (rule ctor_induct[of _ x])

   apply (rule trans)
    apply (rule image_cong)
     apply (rule IFset_simps)
    apply (rule refl)
   apply (rule sym)
   apply (rule trans[OF arg_cong[of _ _ IFset, OF IFmap_simps] trans[OF IFset_simps]])

   apply (rule sym)
   apply (rule trans)
    apply (rule image_Un)
   apply (rule arg_cong2[of _ _ _ _ "(\<union>)"])
    apply (rule sym)
    apply (rule F.set_map(1))

    apply (rule trans)
     apply (rule image_UN)
    apply (rule trans)
     apply (rule SUP_cong)
      apply (rule refl)
     apply (tactic \<open>Goal.assume_rule_tac @{context} 1\<close>) (* IH *)
    apply (rule sym)
    apply (rule trans)
     apply (rule SUP_cong)
      apply (rule F.set_map(2))
     apply (rule refl)
    apply (rule UN_simps(10))
  done

theorem IFset_natural: "IFset o (IFmap f) = image f o IFset"
  apply (rule ext)
  apply (rule trans)
   apply (rule o_apply)
  apply (rule sym)
  apply (rule trans)
   apply (rule o_apply)
  apply (rule IFset_natural0)
  done

lemma IFmap_cong0:
  fixes x :: "'a IF"
  shows "((\<forall>a \<in> IFset x. f a = g a) \<longrightarrow> IFmap f x = IFmap g x)"
  apply (rule ctor_induct[of _ x])

   apply (rule impI)
   apply (rule trans)
    apply (rule IFmap_simps)
   apply (rule trans)
    apply (rule arg_cong[OF F.map_cong0])
      apply (erule bspec)
      apply (erule rev_subsetD)
      apply (rule Fset1_IFset)
     apply (rule mp)
      apply (tactic \<open>Goal.assume_rule_tac @{context} 1\<close>) (* IH *)
     apply (rule ballI)
     apply (erule bspec)
     apply (erule rev_subsetD)
     apply (erule Fset2_IFset)
   apply (rule sym)
   apply (rule IFmap_simps)
  done

theorem IFmap_cong:
  "(\<And>a. a \<in> IFset x \<Longrightarrow> f a = g a) \<Longrightarrow> IFmap f x = IFmap g x"
  apply (rule mp)
   apply (rule IFmap_cong0)
  apply (rule ballI)
  apply (tactic \<open>Goal.assume_rule_tac @{context} 1\<close>)
  done

lemma IFset_bd:
  fixes x :: "'a IF"
  shows " |IFset x| \<le>o (IFbd :: (bd_type_F) rel)"
  apply (rule ctor_induct[of _ x])

   apply (rule ordIso_ordLeq_trans)
    apply (rule card_of_ordIso_subst)
    apply (rule IFset_simps)
   apply (rule Un_Cinfinite_bound)
     apply (rule Fset1_bd)
      apply (rule UNION_Cinfinite_bound)
        apply (rule Fset2_bd)
       apply (rule ballI)
       apply (tactic \<open>Goal.assume_rule_tac @{context} 1\<close>) (* IH *)
      apply (rule IFbd_Cinfinite)
      apply (rule IFbd_Cinfinite)
  done

definition IFrel where
  "IFrel R =
     (BNF_Def.Grp (IFin (Collect (case_prod R))) (IFmap fst))^--1 OO
     (BNF_Def.Grp (IFin (Collect (case_prod R))) (IFmap snd))"

lemma in_IFrel:
  "IFrel R x y \<longleftrightarrow> (\<exists> z. z \<in> IFin (Collect (case_prod R)) \<and> IFmap fst z = x \<and> IFmap snd z = y)"
  unfolding IFrel_def by (rule predicate2_eqD[OF OO_Grp_alt])

lemma IFrel_Frel: "IFrel R (ctor a) (ctor b) \<longleftrightarrow> Frel R (IFrel R) a b"
  apply (rule iffI)
   apply (tactic \<open>dtac @{context} (@{thm in_IFrel[THEN iffD1]}) 1\<close>)+
   apply (erule exE conjE CollectE)+
   apply (rule iffD2)
    apply (rule F.in_rel)
   apply (rule exI)
   apply (rule conjI)
    apply (rule CollectI)
    apply (rule conjI)
     apply (rule ord_eq_le_trans)
      apply (rule F.set_map(1))
     apply (rule ord_eq_le_trans)
      apply (rule trans[OF fun_cong[OF image_id] id_apply])
     apply (rule subset_trans)
      apply (rule Fset1_IFset)
     apply (erule ord_eq_le_trans[OF arg_cong[OF ctor_dtor]])

     apply (rule ord_eq_le_trans)
      apply (rule F.set_map(2))
     apply (rule image_subsetI)
     apply (rule CollectI)
     apply (rule case_prodI)
     apply (rule iffD2)
      apply (rule in_IFrel)
     apply (rule exI)
     apply (rule conjI)
      apply (rule CollectI)
      apply (erule subset_trans[OF Fset2_IFset])
      apply (erule ord_eq_le_trans[OF arg_cong[OF ctor_dtor]])
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
    apply (rule iffD1[OF ctor_diff])
    apply (rule trans)
     apply (rule sym)
     apply (rule IFmap_simps)
    apply (erule trans[OF arg_cong[OF ctor_dtor]])


   apply (rule trans)
    apply (rule F.map_comp)
   apply (rule trans)
    apply (rule F.map_cong0)
      apply (rule fun_cong[OF o_id])
     apply (rule trans)
      apply (rule o_apply)
     apply (rule snd_conv)
   apply (rule iffD1[OF ctor_diff])
   apply (rule trans)
    apply (rule sym)
    apply (rule IFmap_simps)
   apply (erule trans[OF arg_cong[OF ctor_dtor]])

  apply (tactic \<open>dtac @{context} (@{thm F.in_rel[THEN iffD1]}) 1\<close>)
  apply (erule exE conjE CollectE)+
  apply (rule iffD2)
   apply (rule in_IFrel)
  apply (rule exI)
  apply (rule conjI)
   apply (rule CollectI)
   apply (rule ord_eq_le_trans)
    apply (rule IFset_simps)
   apply (rule Un_least)
    apply (rule ord_eq_le_trans)
     apply (rule box_equals[OF _ refl])
      apply (rule F.set_map(1))
     apply (rule trans[OF fun_cong[OF image_id] id_apply])
    apply assumption
    apply (rule ord_eq_le_trans)
     apply (rule SUP_cong[OF _ refl])
     apply (rule F.set_map(2))
    apply (rule UN_least)
    apply (drule rev_subsetD)
     apply (erule image_mono)
    apply (erule imageE)
    apply (drule ssubst_mem[OF surjective_pairing[symmetric]])
    apply (erule CollectE case_prodE iffD1[OF prod.inject, elim_format] conjE)+
    apply hypsubst
    apply (tactic \<open>dtac @{context} (@{thm in_IFrel[THEN iffD1]}) 1\<close>)
    apply (drule someI_ex)
    apply (erule conjE)+
    apply (erule CollectD)

  apply (rule conjI)
   apply (rule trans)
    apply (rule IFmap_simps)
   apply (rule iffD2[OF ctor_diff])
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
     apply (tactic \<open>dtac @{context} (@{thm in_IFrel[THEN iffD1]}) 1\<close>)
     apply (drule someI_ex)
     apply (erule conjE)+
     apply assumption
     apply assumption

  apply (rule trans)
   apply (rule IFmap_simps)
  apply (rule iffD2[OF ctor_diff])
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
    apply (tactic \<open>dtac @{context} (@{thm in_IFrel[THEN iffD1]}) 1\<close>)
    apply (drule someI_ex)
    apply (erule conjE)+
    apply assumption
    apply assumption
  done

lemma Irel_induct:
  assumes IH: "\<forall>x y. Frel P1 P2 x y \<longrightarrow> P2 (ctor x) (ctor y)"
  shows   "IFrel P1 \<le> P2"
  unfolding le_fun_def le_bool_def all_simps(1,2)[symmetric]
  apply (rule allI)+
  apply (rule ctor_induct2)
   apply (rule impI)
   apply (drule iffD1[OF IFrel_Frel])
   apply (rule mp[OF spec2[OF IH]])
   apply (erule F.rel_mono_strong0)
     apply (rule ballI[OF ballI[OF imp_refl]])
    apply (rule ballI[OF ballI])
    apply assumption
  done

lemma le_IFrel_Comp0:
  fixes x :: "'a IF" and y :: "'b IF"
  shows "((IFrel R OO IFrel S) x y \<longrightarrow> IFrel (R OO S) x y)"
  apply (rule ctor_induct2[of _ x y])
   apply (rule impI)
   apply (erule nchotomy_relcomppE[OF ctor_nchotomy])
   apply (drule iffD1[OF IFrel_Frel])
   apply (drule iffD1[OF IFrel_Frel])
   apply (rule iffD2[OF IFrel_Frel])
   apply (rule F.rel_mono_strong0)
      apply (rule iffD2[OF predicate2_eqD[OF F.rel_compp]])
      apply (rule relcomppI)
       apply assumption
      apply assumption
     apply (rule ballI impI)+
     apply assumption
    apply (rule ballI)+
    apply assumption
  done

lemma le_IFrel_Comp: "IFrel R1 OO IFrel R2 \<le> IFrel (R1 OO R2)"
  by (rule predicate2I) (erule mp[OF le_IFrel_Comp0])

context includes lifting_syntax
begin

lemma fold_transfer:
  "((Frel R S ===> S) ===> IFrel R ===> S)
  (fold :: (('a, 'b) F \<Rightarrow> 'b) \<Rightarrow> 'a IF \<Rightarrow> 'b)
  (fold :: (('a', 'b') F \<Rightarrow> 'b') \<Rightarrow> 'a' IF \<Rightarrow> 'b')"
  unfolding rel_fun_def_butlast all_conj_distrib[symmetric] imp_conjR[symmetric]
  unfolding rel_fun_iff_leq_vimage2p
  apply (rule allI impI)+
  apply (rule Irel_induct)
   apply (rule allI impI vimage2pI)+
   apply (unfold fold) [1]
   apply (erule predicate2D_vimage2p)
   apply (rule rel_funD[OF rel_funD[OF rel_funD[OF F.map_transfer]]])
      apply (rule id_transfer)
     apply (rule vimage2p_rel_fun)
   apply assumption
  done

end

definition "IFwit = ctor wit_F"

lemma IFwit: "x \<in> IFset IFwit \<Longrightarrow> False"
  unfolding IFwit_def
  by (elim UnE F.wit[elim_format] UN_E FalseE |
      rule refl |  hypsubst | assumption | unfold IFset_simps)+

ML \<open>
  BNF_FP_Util.mk_xtor_co_iter_o_map_thms BNF_Util.Least_FP false 1 @{thm fold_unique}
    @{thms IFmap} (map (BNF_Tactics.mk_pointfree2 @{context}) @{thms fold})
    @{thms F.map_comp0[symmetric]} @{thms F.map_cong0}
\<close>

ML \<open>
  BNF_FP_Util.mk_xtor_co_iter_o_map_thms BNF_Util.Least_FP true 1 @{thm rec_unique}
    @{thms IFmap} (map (BNF_Tactics.mk_pointfree2 @{context}) @{thms rec})
    @{thms F.map_comp0[symmetric]} @{thms F.map_cong0}
\<close>

bnf "'a IF"
  map: IFmap
  sets: IFset
  bd: "IFbd :: bd_type_F rel"
  wits: IFwit
  rel: IFrel
           apply -
           apply (rule IFmap_id)
          apply (rule IFmap_comp)
         apply (erule IFmap_cong)
        apply (rule IFset_natural)
       apply (rule IFbd_card_order)
      apply (rule IFbd_cinfinite)
     apply (rule IFset_bd)
    apply (rule le_IFrel_Comp)
   apply (rule IFrel_def[unfolded OO_Grp_alt mem_Collect_eq])
  apply (erule IFwit)
  done


(**********)
(* Datatypes are wide with their standard relators! *)

(* Preliminaries: *)
lemma str_init_any: "str_init dummy = str_init undefined"
unfolding str_init_def by auto

lemma car_init_any: "car_init dummy = car_init undefined"
unfolding car_init_def str_init_def by auto

lemma is_car_init: 
"alg (car_init dummy) (str_init dummy)"
by (simp add: alg_min_alg car_init_def)

lemma least_car_init: 
"alg B (str_init dummy) \<Longrightarrow> car_init dummy \<subseteq> B"
by (simp add: car_init_def least_min_alg)

lemmas IFrel_induct2 = Irel_induct[unfolded le_fun_def le_bool_def, rule_format, rotated]

lemma car_init_induct[consumes 1, induct set: car_init]: 
assumes 0: "ii \<in> car_init dummy"
and 1: "\<And>y. Fset2 y \<subseteq> car_init dummy \<Longrightarrow> (\<forall>ii \<in> Fset2 y. \<phi> ii) \<Longrightarrow> \<phi> (str_init dummy y)"
shows "\<phi> ii"
proof-
  have "alg (Collect \<phi> \<inter> car_init dummy) (str_init dummy)"
  unfolding alg_def using 1 by (auto simp: alg_Fset is_car_init)  
  thus ?thesis using 0 using car_init_def  
  	using least_car_init by fastforce
qed

lemma car_init_elim[elim]: 
assumes 0: "ii \<in> car_init dummy"
obtains y where "ii = str_init dummy y" and "Fset2 y \<subseteq> car_init dummy"
proof-
  have "\<exists>y. ii = str_init dummy y \<and> Fset2 y \<subseteq> car_init dummy"
  using 0 apply induct by auto
  thus ?thesis using that by auto
qed

lemma str_init_inj: 
"Fset2 x \<subseteq> car_init dummy \<Longrightarrow> Fset2 y \<subseteq> car_init dummy \<Longrightarrow> 
 str_init dummy x = str_init dummy y \<Longrightarrow> x = y" 
unfolding car_init_any[of dummy]
using ctor_diff[of "Fmap id Abs_IF x" "Fmap id Abs_IF y", unfolded ctor_def comp_def]
unfolding Fmap_comp_id 
by (smt (verit) Abs_IF_inverse Fmap_comp_id Fmap_congL comp_eq_dest_lhs str_init_any subset_eq)

lemma str_init_surj: "ii \<in> car_init dummy \<Longrightarrow> \<exists>y. ii = str_init dummy y \<and> Fset2 y \<subseteq> car_init dummy"
unfolding car_init_any[of dummy] str_init_any[of dummy]
using surj_ctor unfolding surj_def ctor_def apply - apply(erule allE[of _ "Abs_IF ii"])
apply safe subgoal for x  apply(rule exI[of _ "Fmap id Rep_IF x"])
apply safe 
	apply (simp add: Abs_IF_inject F.set_map(2) Rep_IF alg_Fset image_subset_iff is_car_init)
	by (metis F.set_map(2) Rep_IF image_iff) .


(* *)

local_setup \<open>Wide_Database.register_wide @{type_name bd_type_F}
  {T = @{typ "bd_type_F"}, axioms = {bij_upto = refl,
    rel_eq = @{thm refl[of "(=)"]}, rel_per = @{thm neper_eq}, rep_eq = refl, cond_eq = NONE},
    facts = (), rel = @{term "(=) :: bd_type_F \<Rightarrow> bd_type_F \<Rightarrow> bool"}, cond = NONE, deps = []}\<close>

term alg

declare F.rel_eq[rrel_eq]

lemma alg_aux: "alg = alg" ..
local_setup \<open>RLTHM @{binding alg_rlt_neper_param} @{thm alg_aux}\<close>
thm alg_rlt_neper_param

thm alg_def[no_vars]
thm alg_rlt_def

lemma alg_alt: "alg B s = (\<forall>y. (\<forall>b. b \<in> Fset2 y \<longrightarrow> b \<in> B) \<longrightarrow> s y \<in> B)"
unfolding alg_def by auto
local_setup \<open>RLTHM @{binding alg_rlt_alt} @{thm alg_alt}\<close>
thm alg_rlt_alt[no_vars, simped]

declare Frel_neper[simp]

thm F.set_transfer

term closure
thm closure_def

lemma alg_rlt_simp: "neper R1 \<Longrightarrow>
neper R2 \<Longrightarrow>
rel_fun (Frel R1 R2) (rel_set R1) z1 z1 \<Longrightarrow>
rel_fun (Frel R1 R2) (rel_set R2) z2 z2 \<Longrightarrow>
rel_fun (Frel R1 R2) R2 s s \<Longrightarrow>
rel_set R2 B B \<Longrightarrow>
alg_rlt R2 R1 z2 z1 B s = 
(\<forall>x. Frel R1 R2 x x \<and> closure R2 (z2 x) \<subseteq> closure R2 B \<longrightarrow> 
     s x \<in> closure R2 B)"
unfolding closure_def 
apply(subst alg_rlt_alt, auto)  
	apply blast
	by (smt (verit, ccfv_threshold) Collect_mono_iff neper_classes_eq)+

(* NB: I switch the order of the relation arguments too: *)
definition aalg_rlt where 
"aalg_rlt R1 R2 \<equiv> alg_rlt R2 R1 Fset2 Fset1"

lemma aalg_rlt_simp: "neper R1 \<Longrightarrow>
neper R2 \<Longrightarrow> rel_fun (Frel R1 R2) R2 s s \<Longrightarrow> rel_set R2 B B \<Longrightarrow>
aalg_rlt R1 R2 B s = 
(\<forall>x. Frel R1 R2 x x \<and> closure R2 (Fset2 x) \<subseteq> closure R2 B \<longrightarrow> 
     s x \<in> closure R2 B)"
unfolding aalg_rlt_def apply(rule alg_rlt_simp) 
by (auto simp add: F.set_transfer)

(* *)
lemma min_alg_aux: "min_alg = min_alg" ..
local_setup \<open>RLTHM @{binding min_alg_rlt_neper_param} @{thm min_alg_aux}\<close>
thm min_alg_rlt_neper_param

definition min_aalg_rlt where 
"min_aalg_rlt R1 R2 \<equiv> min_alg_rlt R1 R2 Fset2 Fset1 bd_F"

thm alg_min_alg
local_setup \<open>RLTHM @{binding alg_min_alg_rlt} @{thm alg_min_alg}\<close>
thm alg_min_alg_rlt[no_vars,simped]

lemma aalg_rlt_min_aalg_rlt: 
"neper R1 \<Longrightarrow> neper R2 \<Longrightarrow> rel_fun (Frel R1 R2) R2 s s \<Longrightarrow> 
 aalg_rlt R1 R2 (min_aalg_rlt R1 R2 s) s"
unfolding aalg_rlt_def min_aalg_rlt_def
apply(subst alg_min_alg_rlt)
by (auto simp add: F.set_transfer prod.rel_eq)

lemma least_min_alg': "alg B s \<Longrightarrow> (\<forall>b. b \<in> min_alg s \<longrightarrow> b \<in> B)"
using least_min_alg by auto
local_setup \<open>RLTHM @{binding least_min_alg'_rlt} @{thm least_min_alg'}\<close>
thm least_min_alg'_rlt[no_vars,simped]

lemma least_min_alg_rlt: "neper R1 \<Longrightarrow>
neper R2 \<Longrightarrow>
rel_fun (Frel R1 R2) (rel_set R2) z1 z1 \<Longrightarrow>
rel_fun (Frel R1 R2) (rel_set R1) z2 z2 \<Longrightarrow>
rel_set (rel_prod (=) (=)) z3 z3 \<Longrightarrow>
rel_fun (Frel R1 R2) R2 s s \<Longrightarrow>
rel_set R2 B B \<Longrightarrow>
alg_rlt R2 R1 z1 z2 B s \<Longrightarrow>
closure R2 (min_alg_rlt R1 R2 z1 z2 z3 s) \<subseteq> closure R2 B"
using least_min_alg'_rlt[of R1 R2, simped] unfolding closure_def
by auto (metis (no_types, lifting) mem_Collect_eq neper_classes_eq)

lemma least_min_aalg_rlt: 
"neper R1 \<Longrightarrow> neper R2 \<Longrightarrow> rel_fun (Frel R1 R2) R2 s s \<Longrightarrow> rel_set R2 B B \<Longrightarrow>
 aalg_rlt R1 R2 B s \<Longrightarrow>
 closure R2 (min_aalg_rlt R1 R2 s) \<subseteq> closure R2 B"
unfolding aalg_rlt_def min_aalg_rlt_def apply(rule least_min_alg_rlt) 
by (auto simp add: F.set_transfer prod.rel_eq)

(* *)

definition rel_IIT :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a IIT \<Rightarrow> 'a IIT \<Rightarrow> bool)"
where 
"rel_IIT R = rel_prod 
   (rel_set (rel_fun (=) (rel_sum R (=))))
   (rel_fun (Frel (R::'a\<Rightarrow>'a\<Rightarrow>bool) (rel_fun (=) (rel_sum R (=)))) (rel_fun (=) (rel_sum R (=))))"

definition rel_IT :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a IT \<Rightarrow> 'a IT \<Rightarrow> bool)"
where 
"rel_IT R = rel_fun (rel_IIT R) (rel_fun (=) (rel_sum R (=)))"

lemma rel_IT_def2: 
"rel_IT R ii ii' =
(\<forall>B s B' s'. 
   rel_set (rel_fun (=) (rel_sum R (=))) B B' \<and> 
   (\<forall>x y. Frel R (rel_fun (=) (rel_sum R (=))) x y \<longrightarrow> 
          rel_fun (=) (rel_sum R (=)) (s x) (s' y)) 
   \<longrightarrow> 
   rel_fun (=) (rel_sum R (=)) (ii (B, s)) (ii' (B', s')))"
using rel_IT_def[unfolded rel_fun_def, 
   unfolded fun_eq_iff, rule_format, simped] unfolding rel_IIT_def rel_fun_def by auto

lemma neper_rel_IIT[simp]: "neper R \<Longrightarrow> neper (rel_IIT R)"
unfolding rel_IIT_def by (simp add: prod.rrel_neper sum.rrel_neper)

lemma neper_rel_IT[simp]: "neper R \<Longrightarrow> neper (rel_IT R)"
unfolding rel_IT_def by (simp add: prod.rrel_neper sum.rrel_neper)

lemma rel_IIT_eq[simp]: "rel_IIT (=) = (=)" 
unfolding rel_IIT_def rrel_eq ..

lemma rel_IT_eq[simp]: "rel_IT (=) = (=)" 
unfolding rel_IT_def rel_IIT_def rrel_eq ..

(* *)

lemma str_init_aux: "str_init = str_init" ..
local_setup \<open>RLTHM @{binding str_init_rlt_neper_param} @{thm str_init_aux}\<close>
thm str_init_rlt_neper_param

(* LOF *)
lemma 
  fst_rlt[simp]: "neper R1 \<Longrightarrow> neper R2 \<Longrightarrow> fst_rlt R1 R2 = fst" and 
  snd_rlt[simp]: "neper R1 \<Longrightarrow> neper R2 \<Longrightarrow> snd_rlt R1 R2 = snd"
  by (erule (1) rlt_param)+

lemma str_init_rlt_simp[simp]:
"neper R \<Longrightarrow> str_init_rlt R z dummy y i = snd i (z (\<lambda>x. x) (\<lambda>f. f i) y)"
unfolding str_init_rlt_def by (simp add: id_rlt_def neper)

definition sstr_init_rlt where 
"sstr_init_rlt R = str_init_rlt R Fmap"

lemma sstr_init_rlt_simp[simp]:
"neper R \<Longrightarrow> sstr_init_rlt R = str_init"
unfolding sstr_init_rlt_def fun_eq_iff apply (intro allI) 
apply(subst str_init_rlt_simp) unfolding str_init_def id_def by auto

(* *)
lemma car_init_aux: "car_init = car_init" ..
local_setup \<open>RLTHM @{binding car_init_rlt_neper_param} @{thm car_init_aux}\<close>
thm car_init_rlt_neper_param

definition ccar_init_rlt where 
"ccar_init_rlt R = car_init_rlt R Fmap bd_F Fset1 Fset2"

lemma ccar_init_rlt_simp: 
"neper R \<Longrightarrow> 
 ccar_init_rlt R dummy = 
   min_aalg_rlt R
    (rel_IT R)
    (str_init dummy)"
unfolding rel_IT_def rel_IIT_def
unfolding ccar_init_rlt_def min_aalg_rlt_def 
unfolding car_init_rlt_def 
unfolding sstr_init_rlt_def[symmetric] sstr_init_rlt_simp
unfolding rrel_eq ..

lemma str_init_param: 
"neper (R::'a\<Rightarrow>'a\<Rightarrow>bool) \<Longrightarrow> 
rel_fun (Frel R (rel_IT R)) (rel_IT R) (str_init (SOME a. R a a)) (str_init (SOME a. R a a))"
unfolding sstr_init_rlt_simp[of R, symmetric] 
apply(rule str_init_rlt_neper_param[of R Fmap, unfolded F.rel_eq rrel_eq, simped, 
unfolded ccar_init_rlt_def[symmetric] sstr_init_rlt_def[symmetric]
rel_IIT_def[symmetric] rel_IT_def[symmetric], unfolded rel_fun_def[of R], rule_format])
unfolding rel_fun_def[symmetric] by (auto simp: F.map_transfer neper_Some)

(*  *) 
term IFrel
find_theorems IFrel IFset

lemma IFrel_IFwit: "IFrel (R::'a\<Rightarrow>'a\<Rightarrow>bool) IFwit IFwit"
apply(rule IF.rel_refl_strong) 
using IF.wit by fastforce

lemma neper_IFrel[simp]: "neper (R::'a\<Rightarrow>'a\<Rightarrow>bool) \<Longrightarrow> neper (IFrel R)"
apply(rule relator_pres_neper[of IFrel])
  subgoal using IF.rel_compp .
  subgoal using IF.rel_conversep .
  subgoal using IFrel_IFwit by auto
  subgoal by auto .

(* *)

term "min_alg :: (('a, 'a IT) F \<Rightarrow> 'a IT) \<Rightarrow> 'a IT set"

term "str_init :: 'a \<Rightarrow> ('a, 'a IT) F \<Rightarrow> ('a IT)"  
term "car_init :: 'a \<Rightarrow> ('a IT) set"  
thm car_init_def

lemma aalg_rlt_ccar_init_rlt: 
"neper R \<Longrightarrow> 
 aalg_rlt R (rel_IT R) (ccar_init_rlt R dummy) (str_init dummy)"
unfolding ccar_init_rlt_simp apply(rule aalg_rlt_min_aalg_rlt)
apply auto unfolding rel_fun_def rel_IT_def rel_IIT_def str_init_def  
by (simp add: F.rel_map(1) F.rel_map(2) F.rel_mono_strong0)

lemma least_ccar_init_rlt: "neper R \<Longrightarrow> 
    rel_set (rel_IT R) B B \<Longrightarrow>
    aalg_rlt R (rel_IT R) B (str_init dummy) \<Longrightarrow>
    closure (rel_IT R) (ccar_init_rlt R dummy) \<subseteq> closure (rel_IT R) B"
unfolding ccar_init_rlt_simp apply(rule least_min_aalg_rlt)
apply auto unfolding rel_fun_def rel_IT_def rel_IIT_def str_init_def  
by (simp add: F.rel_map(1) F.rel_map(2) F.rel_mono_strong0)

lemma aalg_rlt_str_init_simp: 
"neper R \<Longrightarrow> rel_set (rel_IT R) B B \<Longrightarrow> 
 aalg_rlt R (rel_IT R) B (str_init dummy) = 
 (\<forall>x. Frel R (rel_IT R) x x \<and> closure (rel_IT R) (Fset2 x) \<subseteq> closure (rel_IT R) B \<longrightarrow>
      str_init dummy x \<in> closure (rel_IT R) B)"
apply(subst aalg_rlt_simp) apply auto 
unfolding rel_fun_def rel_IT_def rel_IIT_def str_init_def  
 by (simp add: F.rel_map(1) F.rel_map(2) F.rel_mono_strong0) 

lemma aalg_rlt_closure: "neper R \<Longrightarrow> rel_set (rel_IT R) B B \<Longrightarrow>  
 aalg_rlt R (rel_IT R) B (str_init dummy) \<Longrightarrow> 
 aalg_rlt R (rel_IT R) (closure (rel_IT R) B) (str_init dummy)"
apply(subst aalg_rlt_str_init_simp)
  subgoal by auto
  subgoal by simp
  subgoal unfolding aalg_rlt_str_init_simp apply safe
   subgoal for x apply(erule allE[of _ x]) by simp . .

(* *)
thm str_init_inj
local_setup \<open>RLTHM @{binding str_init_inj_rlt'} @{thm str_init_inj}\<close>

thm str_init_inj_rlt'[of R Fmap bd_F Fset1 Fset2, unfolded F.rel_eq rrel_eq, simped, 
unfolded ccar_init_rlt_def[symmetric] sstr_init_rlt_def[symmetric]
rel_IIT_def[symmetric] rel_IT_def[symmetric],no_vars]

lemma auxx: "neper R \<Longrightarrow> 
ord_set_inst.less_eq_set_rlt (rel_IT R) (Fset2 x) (ccar_init_rlt R dummy) \<longleftrightarrow>
 closure (rel_IT R) (Fset2 x) \<subseteq> closure (rel_IT R) (ccar_init_rlt R dummy)"
unfolding ord_set_inst.less_eq_set_rlt_def Set.less_eq_set_rlt_def
less_eq_fun_rlt_def less_eq_bool_rlt_def le_fun_rlt_def le_bool_rlt_def apply simp
unfolding closure_def apply auto  
by (metis (no_types, opaque_lifting) mem_Collect_eq neper_classes_eq neper_rel_IT)

(* The relativization of the injectiveness theorem is crucial: *)
lemma str_init_inj_rlt: "neper R \<Longrightarrow> 
Frel R (rel_IT R) y y \<Longrightarrow>
Frel R (rel_IT R) x x \<Longrightarrow>
closure (rel_IT R) (Fset2 x) \<subseteq> closure (rel_IT R) (ccar_init_rlt R (SOME a. R a a)) \<Longrightarrow>
closure (rel_IT R) (Fset2 y) \<subseteq> closure (rel_IT R) (ccar_init_rlt R (SOME a. R a a)) \<Longrightarrow>
rel_IT R (str_init (SOME a. R a a) x) (str_init (SOME a. R a a) y) \<Longrightarrow> Frel R (rel_IT R) x y"
apply(subst str_init_inj_rlt'[of R Fmap bd_F Fset1 Fset2 , unfolded F.rel_eq rrel_eq, simped, 
unfolded ccar_init_rlt_def[symmetric] sstr_init_rlt_def[symmetric]
rel_IIT_def[symmetric] rel_IT_def[symmetric]])
using F.map_transfer F.set_transfer apply (auto simp: auxx) 
	apply blast+
	using neper_Some by fastforce

(* *)

thm str_init_surj
local_setup \<open>RLTHM @{binding str_init_surj_rlt'} @{thm str_init_surj}\<close>

thm str_init_surj_rlt'[of R Fmap bd_F Fset1 Fset2, unfolded F.rel_eq rrel_eq, simped, 
unfolded ccar_init_rlt_def[symmetric] sstr_init_rlt_def[symmetric]
rel_IIT_def[symmetric] rel_IT_def[symmetric],no_vars, simped]

lemma str_init_surj_rlt: "neper R \<Longrightarrow> 
rel_IT R ii ii \<Longrightarrow>
ii \<in> closure (rel_IT R) (ccar_init_rlt R dummy) \<Longrightarrow>
\<exists>x. Frel R (rel_IT R) x x \<and>
    rel_IT R ii (str_init dummy x) \<and>
    closure (rel_IT R) (Fset2 x) \<subseteq> closure (rel_IT R) (ccar_init_rlt R dummy)"
using str_init_surj_rlt'[of R Fmap bd_F Fset1 Fset2, unfolded F.rel_eq rrel_eq, simped, 
unfolded ccar_init_rlt_def[symmetric] sstr_init_rlt_def[symmetric]
rel_IIT_def[symmetric] rel_IT_def[symmetric], simped]
apply (auto simp: F.map_transfer F.set_transfer auxx ccar_init_rlt_simp) 
by (smt (z3) CollectD auxx ccar_init_rlt_simp closure_def neper_Some str_init_any)

(* *)

definition tr :: "('a\<Rightarrow>'a\<Rightarrow>bool) \<Rightarrow> 'a IT \<Rightarrow> bool"
where "tr R y = (y \<in> closure (rel_IT R) (ccar_init_rlt R (SOME a. R a a)))"

lemma rel_set_rel_IT_ccar_init_rlt: 
"neper R \<Longrightarrow> 
 rel_set (rel_IT R) (ccar_init_rlt R (SOME a. R a a)) (ccar_init_rlt R (SOME a. R a a))"
unfolding ccar_init_rlt_def unfolding rel_IT_def rel_IIT_def
apply(rule car_init_rlt_neper_param[of R, unfolded rel_fun_def[of R], rule_format, unfolded rrel_eq])
unfolding rel_fun_def[symmetric] 
by (auto simp add: F.map_transfer  F.set_transfer neper_Some) 

lemma is_tr: "neper R \<Longrightarrow> 
    rel_set (rel_IT R) (Collect (tr R)) (Collect (tr R)) \<and> 
    aalg_rlt R (rel_IT R) (Collect (tr R)) (str_init (SOME a. R a a)) \<and> 
    Types_to_PERs.closed (rel_IT R) (Collect (tr R))"
apply safe
  subgoal unfolding tr_def apply auto 
  apply(subgoal_tac "rel_set (rel_IT R) (ccar_init_rlt R (SOME a. R a a))
                        (ccar_init_rlt R (SOME a. R a a))")
    subgoal by auto
    subgoal using rel_set_rel_IT_ccar_init_rlt . . 
    subgoal unfolding tr_def apply simp apply(rule aalg_rlt_closure)
      subgoal by auto
      subgoal using rel_set_rel_IT_ccar_init_rlt . 
      subgoal using aalg_rlt_ccar_init_rlt . .
    subgoal unfolding tr_def 
    by (smt (z3) closed_def closure_def mem_Collect_eq neper_classes_eq neper_rel_IT) .

lemmas rel_set_rel_IT_tr = is_tr[THEN conjunct1]
lemmas aalg_rlt_tr = is_tr[THEN conjunct2, THEN conjunct1]
lemmas closed_tr = is_tr[THEN conjunct2, THEN conjunct2]

lemma aalg_rlt_closed: 
"neper R1 \<Longrightarrow> neper R2 \<Longrightarrow> rel_fun (Frel R1 R2) R2 s s \<Longrightarrow> rel_set R2 B B \<Longrightarrow> Types_to_PERs.closed R2 B \<Longrightarrow> 
 aalg_rlt R1 R2 B s = (\<forall>x. Frel R1 R2 x x \<and> Fset2 x \<subseteq> B \<longrightarrow> s x \<in> B)"
unfolding aalg_rlt_simp 
by (metis F.set_transfer(2) closed_iff_eq_closure closure_Un closure_ext rel_fun_def 
 subset_Un_eq subset_trans)

lemma tr_stable': 
"neper R \<Longrightarrow> Frel R (rel_IT R) x x \<Longrightarrow> Fset2 x \<subseteq> Collect (tr R) \<Longrightarrow> 
 tr R (str_init (SOME a. R a a) x)"
using aalg_rlt_closed[of R "rel_IT R" "str_init (SOME a. R a a)" "Collect (tr R)"]
aalg_rlt_tr[of R]  
by (smt (z3) CollectD aalg_rlt_str_init_simp closed_iff_eq_closure closed_tr closure_Un le_iff_sup rel_set_rel_IT_tr)

lemma tr_stable: 
"neper R \<Longrightarrow> Frel R (rel_IT R) x x \<Longrightarrow> (\<forall>a\<in>Fset2 x. tr R a) \<Longrightarrow> 
 tr R (str_init dummy x)"
using tr_stable'
by (metis (mono_tags, lifting) Ball_Collect str_init_any)

lemma tr_stable_Fset: 
"neper R \<Longrightarrow> Fset1 x \<subseteq> {a. R a a} \<Longrightarrow> Fset2 x \<subseteq> {a. rel_IT R a a} \<Longrightarrow> (\<forall>a\<in>Fset2 x. tr R a) \<Longrightarrow> 
 tr R (str_init dummy x)"
apply(rule tr_stable) by (auto intro: F.rel_refl_strong) 

lemma least_tr: "neper R \<Longrightarrow> 
    rel_set (rel_IT R) B B \<Longrightarrow>
    aalg_rlt R (rel_IT R) B (str_init (SOME a. R a a)) \<Longrightarrow> 
    Types_to_PERs.closed (rel_IT R) B \<Longrightarrow> 
    Collect (tr R) \<subseteq> B"
using least_ccar_init_rlt[of R B "SOME x. R x x"] unfolding tr_def  
using closed_iff_eq_closure by blast

lemma aalg_rlt_str_init_closed: 
assumes "neper R" "rel_set (rel_IT R) B B" "Types_to_PERs.closed (rel_IT R) B"
shows  
"aalg_rlt R (rel_IT R) B (str_init dummy) = 
 (\<forall>x. Frel R (rel_IT R) x x \<and> Fset2 x \<subseteq> B \<longrightarrow> str_init dummy x \<in> B)"
proof-
  have 0: "closure (rel_IT R) B = B"  
  	using assms(2) assms(3) closed_iff_eq_closure by blast
  show ?thesis apply(subst aalg_rlt_str_init_simp[of R B dummy]) 
  using assms apply auto  
  apply (metis "0" closure_Un subset_Un_eq)  
  by (metis (no_types, opaque_lifting) "0" F.set_transfer(2) closure_ext rel_fun_def subset_trans)
qed

lemma str_init_inj_rlt_tr: "neper R \<Longrightarrow> 
Frel R (rel_IT R) x x \<Longrightarrow> Frel R (rel_IT R) y y \<Longrightarrow>
Fset2 x \<subseteq> Collect (tr R) \<Longrightarrow> Fset2 y \<subseteq> Collect (tr R) \<Longrightarrow>
rel_IT R (str_init (SOME a. R a a) x) (str_init (SOME a. R a a) y) \<Longrightarrow> Frel R (rel_IT R) x y"
apply(subst str_init_inj_rlt)
apply auto unfolding tr_def apply auto 
	apply (smt (verit, best) closure_Un closure_idem in_mono neper_rel_IT subset_Un_eq)
  by (smt (verit, best) closure_Un closure_idem le_iff_sup neper_rel_IT subsetD)

lemma str_init_surj_rlt_tr: 
assumes "neper R" "rel_IT R ii ii" "tr R ii"
shows "\<exists>x. Frel R (rel_IT R) x x \<and>
    rel_IT R ii (str_init (SOME a. R a a) x) \<and>
    Fset2 x \<subseteq> Collect (tr R)" 
using str_init_surj_rlt[OF assms(1,2) assms(3)[unfolded tr_def]] 
apply safe subgoal for x
apply(rule exI[of _ x]) unfolding tr_def 
by simp (smt (verit) F.set_transfer(2) closure_ext rel_fun_def subset_eq) .

lemma neper_restr_rel_IT_tr: 
assumes R: "neper R"
shows "neper (restr (rel_IT R) (tr R))"
apply(rule neper_restr)
  subgoal using R by simp
  subgoal  apply(rule exI[of _ "str_init (SOME a. R a a) wit_F"], safe)
    subgoal using aalg_rlt_tr[OF R] 
    using aalg_rlt_str_init_closed[of R "Collect (tr R)" "SOME x. R x x"] R is_tr[OF R] 
    by simp (metis (mono_tags, lifting) F.rel_refl_strong axiom13_F axiom14_F subset_iff)
    subgoal using R by (smt (verit, best) \<open>neper (rel_IT R)\<close> rel_set_rel_IT_tr
        \<open>tr R (str_init (SOME a. R a a) wit_F)\<close> mem_Collect_eq neper_classes_eq rel_setD2) . .

lemma tr_induct[consumes 2, induct pred: tr]: 
assumes R: "neper R"
and 0: "tr R ii"
and 1: "\<And>y. Frel R (rel_IT R) y y \<Longrightarrow> (\<forall>ii \<in> Fset2 y. tr R ii \<and> \<phi> ii) \<Longrightarrow> \<phi> (str_init (SOME a. R a a) y)"
and 2: "\<And>ii jj. tr R ii \<Longrightarrow> \<phi> ii \<Longrightarrow> rel_IT R ii jj \<Longrightarrow> \<phi> jj"
shows "\<phi> ii"
proof-  
  have r: "rel_set (rel_IT R) {ii. tr R ii \<and> \<phi> ii} {ii. tr R ii \<and> \<phi> ii}"
  using R unfolding rel_set_def using 2 closed_tr[OF R, unfolded Types_to_PERs.closed_def]
    by (smt (z3) CollectD CollectI closure_def neper_classes_eq neper_rel_IT tr_def) 

  have c: "Types_to_PERs.closed (rel_IT R) {ii. tr R ii \<and> \<phi> ii}"
  using closed_tr 2 unfolding Types_to_PERs.closed_def apply auto  
  using R by blast

  have a: "aalg_rlt R (rel_IT R) {ii. tr R ii \<and> \<phi> ii} (str_init (SOME a. R a a))"
  using R apply(subst aalg_rlt_closed[OF _ _ _ _ c])
    subgoal .
    subgoal using R by simp
    subgoal using str_init_param[OF R] .
    subgoal using r . 
    subgoal using 1 by auto (metis (mono_tags, lifting) Ball_Collect tr_stable) . 

  have "Collect (tr R) \<subseteq> {ii. tr R ii \<and> \<phi> ii}"
  using least_tr[OF R r a c] .
 
  thus ?thesis using 0 by auto 
qed

lemma tr_elim[elim]: 
assumes R: "neper R"
and 0: "tr R ii" 
obtains y where "ii = str_init (SOME a. R a a) y" and "Frel R (rel_IT R) y y" and "\<forall>jj\<in>Fset2 y. tr R jj"
      |jj where "tr R jj" and "rel_IT R ii jj"
proof-
  have "(\<exists>y. ii = str_init (SOME a. R a a) y \<and> Frel R (rel_IT R) y y \<and> (\<forall>jj\<in>Fset2 y. tr R jj)) \<or>
        (\<exists>jj. tr R jj \<and> rel_IT R ii jj)"
  using R 0 apply(induct rule: tr_induct) 
  apply auto  
  apply (metis (mono_tags, lifting) CollectD CollectI R closed_def closed_tr rel_set_def rel_set_rel_IT_tr)
  by (metis (no_types, opaque_lifting) CollectD CollectI R neper_classes_eq neper_rel_IT)
  thus ?thesis using that by auto
qed

inductive myrel :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a IT \<Rightarrow> 'a IT \<Rightarrow> bool)" 
for R :: "('a \<Rightarrow> 'a \<Rightarrow> bool)" 
where 
"Fset2 y \<subseteq> car_init undefined \<Longrightarrow> Fset2 y' \<subseteq> car_init undefined \<Longrightarrow> 
 Frel R (myrel R) y y' \<Longrightarrow> myrel R (str_init undefined y) (str_init undefined y')"

lemma IFrel_inv_imagep_myrel: 
assumes R: "neper R" 
shows "IFrel R = inv_imagep (myrel R) Rep_IF"
unfolding inv_imagep_def fun_eq_iff restr_def proof safe
  fix ii ii'
  assume 0: "IFrel R ii ii'"
  show "myrel R (Rep_IF ii) (Rep_IF ii')"
  apply(rule IFrel_induct2[OF 0])  
  unfolding ctor_def o_def apply(subst IF.Abs_IF_inverse)
    subgoal by (smt (verit, best) F.set_map(2) Rep_IF alg_alt imageE is_car_init)
    subgoal for x x' apply(subst IF.Abs_IF_inverse)
      subgoal by (smt (verit, best) F.set_map(2) Rep_IF alg_alt imageE is_car_init)
    subgoal apply(rule myrel.intros) unfolding F.set_map F.rel_map 
    	using Rep_IF by auto . .
next 
  fix jj jj'
  assume 1: "myrel R (Rep_IF jj) (Rep_IF jj')"
  hence 2: "Rep_IF jj \<in> car_init undefined" "Rep_IF jj' \<in> car_init undefined"
  by (auto simp: Rep_IF)
  define ii and ii' where defs: "ii = Rep_IF jj" "ii' = Rep_IF jj'"
  have 3: "jj = Abs_IF ii"  "jj' = Abs_IF ii'"
  	by (auto simp add: Rep_IF_inverse defs)
  show "IFrel R jj jj'"
  unfolding 3 using 1[unfolded defs[symmetric]] 2[unfolded defs[symmetric]]
  proof induct
  	case (1 y y')  

    have y2: "Fset2 y \<subseteq> range Rep_IF"  
    	using 1 by (metis (no_types, lifting) type_definition.Rep_range type_definition_IF)  
    define x where "x = Fmap id Abs_IF y" 
    have y: "y = Fmap id Rep_IF x" unfolding x_def Fmap_comp_id
    apply(rule Fmap_congL[symmetric]) using y2  
    using Abs_IF_inverse Rep_IF by auto

    have y'2: "Fset2 y' \<subseteq> range Rep_IF"  
    	using 1 by (metis (no_types, lifting) type_definition.Rep_range type_definition_IF)  
    define x' where "x' = Fmap id Abs_IF y'" 
    have y': "y' = Fmap id Rep_IF x'" unfolding x'_def Fmap_comp_id
    apply(rule Fmap_congL[symmetric]) using y'2  
    using Abs_IF_inverse Rep_IF by auto

    note yy' = y y' 

  	show ?case 
    apply(subst str_init_any) 
    unfolding yy'
    unfolding ctor_def[unfolded o_def fun_eq_iff,rule_format,symmetric]
    unfolding IFrel_Frel using 1(3) unfolding yy' F.rel_map
    apply - apply(drule F.rel_mono_strong[of _ _ _ _ R "IFrel R"])  
    using Rep_IF car_init_any  
    by (fastforce simp add: Rep_IF_inverse)+
  qed
qed

lemma myrel_sym: "neper R \<Longrightarrow> myrel R ii ii' \<Longrightarrow> myrel R ii' ii"
apply rotate_tac apply(induct rule: myrel.induct, auto intro!: myrel.intros)
subgoal for y y'
  apply(subgoal_tac "Frel (conversep R) (conversep (myrel R)) y y'")
  subgoal unfolding F.rel_conversep by auto
  subgoal apply(rule F.rel_mono_strong[of R "\<lambda>x1 x2. myrel R x1 x2 \<and> myrel R x2 x1"]) 
  by auto (metis conversepD neper_conversep) . .

lemma str_init_inj': "Fset2 x \<subseteq> car_init dummy \<Longrightarrow>
  Fset2 y \<subseteq> car_init dummy \<Longrightarrow> str_init dummy x = str_init dummy y \<longleftrightarrow> x = y"
using str_init_inj by auto

lemma myrel_trans: 
assumes R: "neper (R::'a\<Rightarrow>'a\<Rightarrow>bool)" 
and 0: "myrel R ii ii'" "myrel R ii' ii''"
shows "myrel R ii ii''"
using 0 proof(induct arbitrary: ii'')
  case (1 y y' ii'') note 0 = 1
  define Q where "Q \<equiv> \<lambda>x1 x2. myrel R x1 x2 \<and> (\<forall>x. myrel R x2 x \<longrightarrow> myrel R x1 x)"
  show ?case using 1(4) proof cases
  	case (1 yy' y'')
      hence yy'[simp]: "yy' = y'" by (simp add: "1.hyps"(2) str_init_inj')
  	  show ?thesis unfolding 1 proof(rule myrel.intros)
        show "Fset2 y \<subseteq> car_init undefined" by fact
        show "Fset2 y'' \<subseteq> car_init undefined" using "1"(4) by auto        
        have "(Frel R Q OO Frel R (myrel R)) y y''"  
        	using "1"(5) "1.hyps"(3) Q_def yy' by blast
        hence "Frel R (Q OO myrel R) y y''"   
        	using "1.prems"(1) axiom10_F neper_relcompp_leq[OF R] by fastforce
        thus "Frel R (myrel R) y y''"  
        	using F.rel_mono_strong Q_def by blast
      qed
  qed
qed
  
lemma neper_myrel: 
"neper R \<Longrightarrow> neper (myrel R)" 
using IFrel_inv_imagep_myrel[of R, unfolded inv_imagep_def fun_eq_iff]
using neper_IFrel[of R] unfolding neper_def per_def apply safe
apply (metis myrel_sym neper_def per_def)
apply (metis myrel_trans neper_def per_def)
by blast

(* *)

lemma myrel_implies_car_init: 
assumes 0: "myrel R ii ii'" 
shows "ii \<in> car_init undefined \<and> ii' \<in> car_init undefined"
using 0 by induct (auto simp: alg_Fset is_car_init)

lemma myrel_implies_rel_IT: 
assumes 0: "myrel R ii ii'" 
shows "rel_IT R ii ii'" 
using 0 proof (induction)
  case (1 y y')
  show "rel_IT R (str_init undefined y) (str_init undefined y')" 
  unfolding rel_IT_def2 proof safe
    fix B B' :: "'a ASucFbd_type set" and s s' :: "('a,'a ASucFbd_type)F \<Rightarrow> 'a ASucFbd_type" 
    assume 2: "rel_set (rel_fun (=) (rel_sum R (=))) B B'" and 
    3: "\<forall>x y. Frel R (rel_fun (=) (rel_sum R (=))) x y \<longrightarrow> rel_fun (=) (rel_sum R (=)) (s x) (s' y)"
    show "rel_fun (=) (rel_sum R (=)) (str_init undefined y (B, s)) (str_init undefined y' (B', s'))"
    unfolding str_init_def apply simp
    apply(rule 3[rule_format]) unfolding F.rel_map  
    apply(rule F.rel_mono_strong0[OF 1(3)])
      subgoal by auto
      subgoal using 1  
      using "2" "3" rel_IT_def2 by blast . 
  qed
qed

lemma myrel_implies_tr: 
assumes R: "neper R" 
and 0: "myrel R ii ii'" 
shows "tr R ii \<and> tr R ii'"
using 0 proof induction
  case (1 y y')
  have "Frel R (rel_IT R) y y'"
  apply(rule F.rel_mono_strong0[OF 1(3)])
  subgoal by auto
  subgoal using 1  
  using myrel_implies_rel_IT by auto . 
  hence "Frel R (rel_IT R) y y" "Frel R (rel_IT R) y' y'"
  using Frel_neper[OF R neper_rel_IT[OF R]] unfolding neper_def per_def 
  by meson+
  show ?case apply safe 
    subgoal apply(rule tr_stable[OF R])
      subgoal by fact
      subgoal using F.set_transfer(2)[unfolded rel_fun_def rel_set_def, rule_format, OF 1(3)]
      using 1(1,2) by auto .
    subgoal apply(rule tr_stable[OF R])
      subgoal by fact
      subgoal using F.set_transfer(2)[unfolded rel_fun_def rel_set_def, rule_format, OF 1(3)]
      using 1(1,2) by auto . .
qed

lemma myrel_str_init_Fset2: 
assumes R: "neper R" and m: "myrel R (str_init undefined y) (str_init undefined y)"
and y: "Fset2 y \<subseteq> car_init undefined"
and ii: "ii \<in> Fset2 y"
shows "myrel R ii ii"
using m proof cases
  case (1 yy yy')
  hence 0: "yy = y" "yy' = y" by (simp_all add: str_init_inj y)
  show ?thesis using ii
  using F.set_transfer(2)[unfolded rel_fun_def rel_set_def, rule_format, OF 1(5), unfolded 0]
  using R myrel_sym myrel_trans by blast
qed 

lemma rel_IT_implies_myrel: 
assumes R: "neper R" 
and 0: "myrel R ii ii" "myrel R ii' ii'"  "rel_IT R ii ii'" 
shows "myrel R ii ii'"  
proof-
  have "ii \<in> car_init undefined" 
  	using assms(2) myrel_implies_car_init by blast
  thus ?thesis using 0 proof(induction arbitrary: ii')
  	case (1 y i')
    obtain y' where i': "i' = str_init undefined y'"  
    and "Fset2 y' \<subseteq> car_init undefined" 
    	by (meson "1.prems"(2) myrel.cases)
  	show ?case unfolding i' proof(intro myrel.intros)
      show y: "Fset2 y \<subseteq> car_init undefined" by fact
      show y': "Fset2 y' \<subseteq> car_init undefined" by fact
      have 2: "Frel R (rel_IT R) y y'"  
      proof(rule str_init_inj_rlt_tr[OF R, unfolded str_init_any[of "SOME a. R a a"], 
        OF _ _ _ _ 1(5)[unfolded i']])
        show 3: "Frel R (rel_IT R) y y" 
        	by (smt (verit, best) "1.prems"(1) F.rel_mono_strong R myrel.simps 
           myrel_implies_rel_IT str_init_inj' y)
        show "Frel R (rel_IT R) y' y'" 
        	by (smt (verit, best) "1.prems"(2) F.rel_mono_strong R i' 
            myrel.simps myrel_implies_rel_IT str_init_inj y')
        show "Fset2 y \<subseteq> Collect (tr R)" 
        	using "1.prems"(1) R myrel_implies_tr myrel_str_init_Fset2 y by auto blast
        show "Fset2 y' \<subseteq> Collect (tr R)" 
        	using "1.prems"(2) R i' myrel_implies_tr myrel_str_init_Fset2 y' by auto blast
      qed
      show "Frel R (myrel R) y y'" proof(rule F.rel_mono_strong[OF 2], safe) 
        fix ii ii' assume ii: "ii \<in> Fset2 y" and ii': "ii' \<in> Fset2 y'" and r: "rel_IT R ii ii'"
        show "myrel R ii ii'"
        apply(rule 1(2)[rule_format, OF ii _ _ r])
          subgoal using myrel_str_init_Fset2[OF R 1(3) y ii] .
          subgoal using myrel_str_init_Fset2[OF R 1(4)[unfolded i'] y' ii'] . .
      qed
    qed
  qed
qed

lemma str_init_param2: 
"neper R \<Longrightarrow> Frel R (rel_IT R) x y \<Longrightarrow> rel_IT R (str_init undefined x) (str_init undefined y)"
using str_init_param[of R, unfolded str_init_any[of "SOME a. R a a"], unfolded rel_fun_def, rule_format]
by auto  

lemma tr_rel_IT_implies_ex_myrel: 
assumes R: "neper R" 
and 0: "tr R jj"  "rel_IT R jj jj" 
shows "\<exists>ii. myrel R ii ii \<and> rel_IT R jj ii" 
using R 0 proof(induct rule: tr_induct)
  case (1 y)
  have y1: "Fset1 y \<subseteq> {a. R a a}"
  using F.set_transfer(1)[unfolded rel_fun_def, rule_format, OF 1(1)]
  unfolding rel_set_def using R neper_classes_eq by fastforce

  from 1(2) 
  obtain f where f: 
  "\<forall>j\<in>Fset2 y. tr R j \<and> rel_IT R j j \<longrightarrow> myrel R (f j) (f j) \<and> rel_IT R j (f j)" by metis
  define x where x: "x = Fmap id f y"
  show ?case proof(rule exI[of _ "str_init (SOME a. R a a) x"], 
   unfold str_init_any[of "SOME a. R a a"], safe)
    show mr: "myrel R (str_init undefined x) (str_init undefined x)"
    proof(rule myrel.intros)
      show "Fset2 x \<subseteq> car_init undefined" unfolding x F.set_map using f apply auto
      by (metis (no_types, lifting) "1.hyps"(2) Collect_mono_iff R alg_Fset 
        is_car_init myrel.simps neper_rel_IT neper_rel_set_iff rel_set_rel_IT_tr)
      thus "Fset2 x \<subseteq> car_init undefined" .
      show "Frel R (myrel R) x x" unfolding x F.rel_map apply simp apply(rule F.rel_refl_strong)
        subgoal using y1 by auto
        subgoal apply(rule f[rule_format, THEN conjunct1])  
          subgoal using "1.hyps"(2) by auto
          subgoal by (metis (no_types, lifting) "1.hyps"(2) Collect_mono_iff R 
            neper_rel_IT neper_rel_set_iff rel_set_rel_IT_tr) . . 
    qed 
  
    have fr: "Frel R (rel_IT R) y x"
    unfolding x F.rel_map apply(rule F.rel_refl_strong)
    subgoal using y1 by auto
    subgoal apply(rule f[rule_format, THEN conjunct2])
      subgoal using "1.hyps"(2) by blast
      subgoal by (smt (verit, best) "1.hyps"(2) CollectD CollectI R neper_classes_eq 
        neper_rel_IT rel_setD2 rel_set_rel_IT_tr) . .
    show "rel_IT R (str_init undefined y) (str_init undefined x)"
    using str_init_param2[OF R fr] . 
  qed
next
  case (2 ii jj)
  thus ?case by (metis R neper_def neper_rel_IT per_def)
qed 


(* *)

definition t where "t = (\<lambda>x. x \<in> car_init undefined)"

lemma Collect_t: "Collect t = car_init undefined"
unfolding t_def by auto

thm IF.type_definition_IF[unfolded Collect_t[symmetric]]


(* *)

term "Rep_IF :: 'a IF \<Rightarrow> 'a IT"

thm str_init_def


lemma bij_upto_hh: 
assumes R: "neper R" 
shows 
"bij_upto 
   (restr (myrel R) (\<lambda>x. x \<in> car_init undefined)) 
   (restr (rel_IT R) (tr R))
   id"
unfolding id_def apply(rule bij_uptoI)
  subgoal using neper_restr_rel_IT_tr[OF R] .
  subgoal unfolding restr_def  
  using myrel_implies_rel_IT myrel_implies_tr[OF R] by auto
  subgoal unfolding restr_def using rel_IT_implies_myrel[OF R] by auto
  subgoal for jj unfolding restr_def 
  using neper_rel_IT[OF R] tr_rel_IT_implies_ex_myrel[OF R, of jj] apply clarsimp
    subgoal for ii apply(rule exI[of _ ii]) 
    using myrel_implies_car_init myrel_implies_rel_IT myrel_implies_tr[OF R]
    by fastforce . .
 
(* *)

thm IFrel_inv_imagep_myrel

lemmas bij_uptoRep_IF = bij_upto_transportFromRaw
 [OF IF.type_definition_IF[unfolded Collect_t[symmetric]] 
     IFrel_inv_imagep_myrel, unfolded t_def, OF _ bij_upto_hh]
      
wide_typedef IF rel: "\<lambda>R _ _ _ _. IFrel R" rep: "\<lambda>R _ _ _ _. Rep_IF" 
cond: "\<lambda>R z_map z_bd z_set1 z_set2. z_map = Fmap \<and> z_bd = bd_F \<and> z_set1 = Fset1 \<and> z_set2 = Fset2" 
  subgoal for R unfolding rrel_eq by (auto simp: rel_fun_def)
  subgoal using IF.rel_eq .
  subgoal for R z_set2 z_set1 z_bd z_map unfolding rrel_eq apply simp
  unfolding ccar_init_rlt_def[symmetric]
  unfolding min_aalg_rlt_def[symmetric]
  unfolding rel_IIT_def[symmetric] rel_IT_def[symmetric] unfolding Eps_rlt_True
  using bij_uptoRep_IF[of R] unfolding closure_def tr_def by auto 
  subgoal .. 
  subgoal by simp .
  


(*********)

(*<*)
end
(*>*)

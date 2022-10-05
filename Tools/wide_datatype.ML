signature WIDE_DATATYPE = sig
val generate_wide: BNF_FP_Def_Sugar.fp_sugar list -> Proof.context -> Proof.context
val wide_plugin: string
end

structure Wide_Datatype : WIDE_DATATYPE = struct

open Relativization
open BNF_Util
open BNF_Def
open BNF_Comp
open BNF_FP_Def_Sugar

val rrel_altN = "_alt"

fun dest_leq (Const (\<^const_name>\<open>less_eq\<close>, _) $ t1 $ t2) = (t1, t2)
  | dest_leq t = raise TERM ("dest_leq", [t]);

fun generate_wide (fp_sugars : fp_sugar list) lthy =
  let
    val Ts = map (#T) fp_sugars;

    val ns = map (fn fp_sugar => #T fp_sugar |> dest_Type |> snd |> length) fp_sugars;
    val lives = map (fn fp_sugar => #fp_bnf fp_sugar |> live_of_bnf) fp_sugars;
    val livenesss = @{map 2} (fn n => fn fp_sugar =>
      liveness_of_fp_bnf n (#fp_bnf fp_sugar)) ns fp_sugars;

    val tfrees = Term.add_tfreesT (hd Ts) [] |> rev |> map TFree;
    val (alphaTs, names_lthy) = lthy
      |> fold Variable.declare_typ tfrees
      |> mk_TFrees' (map Type.sort_of_atyp tfrees);
    val RTs = @{map 2} mk_pred2T alphaTs alphaTs;
    val (Rs, names_lthy) = mk_Frees "R" RTs names_lthy;
    val ITs = map (typ_subst_atomic (tfrees ~~ alphaTs)) Ts;
    val IRTs = @{map 2} mk_pred2T ITs ITs;

    val absT_infos = map #absT_info fp_sugars;
    val ctors = (map (mk_ctor tfrees) o #ctors o #fp_res) (hd fp_sugars);
    val ctor_repTs = ctors
      |> map (domain_type o snd o dest_Const)
      |> @{map 2} (fn src => mk_repT (#absT src) (#repT src)) absT_infos;
    val ctor_repATs = map (typ_subst_atomic ((tfrees ~~ alphaTs))) ctor_repTs;
    val ctors = ctors
      |> @{map 3} (fn T => fn src => fn ctor => absfree ("x", T)
          (ctor $ (mk_abs (domain_type (fastype_of ctor)) (#abs src) $ Bound 0))) ctor_repATs absT_infos;
    val ctorAs = map (subst_atomic_types (tfrees ~~ alphaTs)) ctors;

    val type_Reps = map Logic.mk_type ctor_repATs;
    val shyps = distinct (op =) (maps (mk_shyps_term lthy) type_Reps);
    val deps = mk_deps lthy (Logic.list_implies (shyps,
      Logic.mk_conjunction_list (@{map 2} (curry mk_Trueprop_eq) type_Reps type_Reps)));
    val depTs = map fastype_of deps;

    val rel_Ts = @{map 2} (fn T => fn U => RTs ---> depTs ---> T --> U --> @{typ bool}) ITs ITs;
    val Irel_names = map ((fn s => "rrel_" ^ s) o base_name_of_typ o #T) fp_sugars;
    val (Irels, names_lthy) = @{fold_map 2} (yield_singleton o mk_Frees) Irel_names rel_Ts names_lthy;

    val (((((Xs, Ys), xs), ys), zs), names_lthy) = names_lthy
      |> mk_Frees "X" IRTs
      ||>> mk_Frees "Y" IRTs
      ||>> mk_Frees "x" ctor_repATs
      ||>> mk_Frees "y" ctor_repATs
      ||>> mk_Frees "z" depTs;

    val alphaTRs = alphaTs ~~ Rs;
    val dzs = deps ~~ zs;

    fun lookup Xs lthy T = 
      (AList.lookup (op =) (ITs ~~ Xs) T
      |> the_default (fn () => error ("RIN: encountered a non-wide type " ^ Syntax.string_of_typ lthy T))) ();
    fun lookup_Irel lthy = rpair lthy o lookup (map (fn Irel => K (list_comb (Irel, Rs @ zs))) Irels) lthy;
    fun lookup_Xs lthy = rpair lthy o lookup (map K Xs) lthy;
    fun lookup_Ys lthy = rpair lthy o lookup (map K Ys) lthy;
    val (rel_Xs, lthy) = fold_map (RIN_gen lookup_Xs alphaTRs dzs) ctor_repATs lthy;
    val (rel_Ys, lthy) = fold_map (RIN_gen lookup_Ys alphaTRs dzs) ctor_repATs lthy;
    val (rel_Irels, lthy) = fold_map (RIN_gen lookup_Irel alphaTRs dzs) ctor_repATs lthy;

    fun filter_prems prems t =
      let
        val Ts = Term.add_frees t []
      in
        (filter (fn prem => subset (op =) (Term.add_frees prem [], Ts)) prems, t)
      end;

    val mono_prems = @{map 2} (HOLogic.mk_Trueprop oo mk_leq) Xs Ys;
    val monos = @{map 2} (Logic.list_implies o filter_prems mono_prems o HOLogic.mk_Trueprop oo mk_leq) rel_Xs rel_Ys
      |> map (Skip_Proof.make_thm (Proof_Context.theory_of lthy))
      |> Proof_Context.export names_lthy lthy
      |> filter_out (fn thm => thm |> Thm.concl_of |> HOLogic.dest_Trueprop |> dest_leq |> op aconv handle TERM _ => false);

    val Irel_intros = @{map 6}
        (fn Irel => fn rel_Irel => fn ctorA => fn ctorB => fn x => fn y =>
          Logic.mk_implies (HOLogic.mk_Trueprop (rel_Irel $ x $ y),
            HOLogic.mk_Trueprop (list_comb (Irel, Rs @ zs) $ (betapply (ctorA, x)) $ (betapply (ctorB, y)))))
      Irels rel_Irels ctorAs ctorAs xs ys;

(* val _ = Irel_intros |> map (Syntax.string_of_term lthy #> writeln) *)

    val fp = #fp (hd fp_sugars)

    val inductive_flags = {quiet_mode = true, verbose = false, alt_name = Binding.empty,
      coind = (fp = Greatest_FP), no_elim = false, no_ind = false,
      skip_mono = false};

    val Irel_bs = map (Binding.name o fst o dest_Free) Irels;
    val Irel_decls = @{map 2} (rpair NoSyn oo pair) Irel_bs (map fastype_of Irels);

    val (Irels_raw, (lthy, lthy_old)) = lthy
      |> Local_Theory.begin_nested |> snd
      |> Inductive.add_inductive inductive_flags Irel_decls (map dest_Free (Rs @ zs))
        (map (pair Binding.empty_atts) Irel_intros) monos
      ||> `Local_Theory.end_nested;

    val phi = Proof_Context.export_morphism lthy_old lthy;
    val Irel_gens = Irels_raw |> Inductive.transform_result phi |> #preds;
    val Irel_fixeds = @{map 2} (fn gen => fn rel => Const (gen |> dest_Const |> fst, fastype_of rel)) Irel_gens Irels;

    val names = map_filter (try (fst o dest_Type)) Ts;

    val (conds, lthy) = fold_map (CND alphaTRs dzs) type_Reps lthy |>> flat;
    val cond = if null conds then NONE
      else SOME (Library.foldr1 HOLogic.mk_conj conds |> fold_rev Term.lambda (Rs @ zs)
        |> Morphism.term phi);


    val lthy = @{fold 2} (fn name => fn rel =>
      (case Wide_Database.wide_of lthy name of
        NONE => Wide_Typedef.wide_typedef ((((name, rel), NONE), cond), NONE)
          (replicate (if cond = NONE then 4 else 5) (fn {context = ctxt, prems = _} => Skip_Proof.cheat_tac ctxt 1))
      | SOME _ => I))
      names Irel_gens lthy;

    fun filter_Rs liveness = map_filter I (@{map 2} (fn live => fn R => if live then SOME R else NONE) liveness Rs);
    val Irel_eqs = @{map 2} (fn liveness => fn Irel => curry Term.list_comb Irel
      (@{map 2} (fn live => fn R =>
         if live then R else HOLogic.eq_const (R |> fastype_of |> dest_pred2T |> fst)) liveness Rs @
      deps) |> fold_rev Term.lambda (filter_Rs liveness)) livenesss Irel_fixeds;

    val bnf_rels = map (rel_of_bnf o #fp_bnf) fp_sugars;
    val Irel_alts = @{map 2} (curry mk_Trueprop_eq) Irel_eqs
        (@{map 3} (fn live => fn IT =>
          try (mk_rel live alphaTs alphaTs) #> the_default (HOLogic.eq_const IT)) lives ITs bnf_rels)
      |> map (Skip_Proof.make_thm (Proof_Context.theory_of lthy))
      |> Proof_Context.export names_lthy lthy;

    val notes =
      @{map 2} (fn b => fn Irel_alt => (b, rrel_altN, [Irel_alt], @{attributes [rrel_alt]})) Irel_bs Irel_alts
      |> map (fn (b, thmN, thms, atts) => ((b |> Binding.suffix_name thmN, []), [(thms, atts)]));
  in
    lthy
    |> Local_Theory.notes notes |> snd
  end;

val wide_plugin = Plugin_Name.declare_setup \<^binding>\<open>wide\<close>;

end
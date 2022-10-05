signature WIDE_TYPEDEF = sig
  val wide_typedef:
    (((string * term) * term option) * term option) * thm option ->
    ({context: Proof.context, prems: thm list} -> tactic) list -> Proof.context -> Proof.context
  val wide_typedef_cmd: (((string * string) * string option) * string option) * (Facts.ref * Token.src list) option -> Proof.context -> Proof.state
  val wide_copy: Typedef.info -> Proof.context -> Proof.context
end

structure Wide_Typedef : WIDE_TYPEDEF = struct

open Relativization
open Wide_Database
open BNF_Util

fun strip3 thm = (case Term.strip_comb (HOLogic.dest_Trueprop (Thm.prop_of thm)) of
    (_, [x1, x2, x3]) => (x1, x2, x3)
  | _ => error "strip3: wrong number of arguments");

fun mk_restr R P =
  let
    val RT = fastype_of R;
    val PT = fastype_of P;
  in
    Const (@{const_name restr}, RT --> PT --> RT) $ R $ P
  end;

fun mk_bij_upto P Q f =
  let
    val PT = fastype_of P;
    val QT = fastype_of Q;
    val fT = fastype_of f;
  in
    Const (@{const_name bij_upto}, PT --> QT --> fT --> HOLogic.boolT) $ P $ Q $ f
  end;

fun mk_rep T P =
  let
    val PT = fastype_of P;
  in
    Const (@{const_name rep}, PT --> T --> domain_type PT) $ P
  end;

fun mk_INV f =
  let
    val (T, U) = dest_funT (fastype_of f);
  in
    Const (@{const_name INV}, (T --> U) --> U --> T) $ f
  end;

fun dest_Collect (Const (\<^const_name>\<open>Collect\<close>, _) $ P) = P
  | dest_Collect t = raise TERM ("dest_Collect", [t]);

val rel_neperN = "rrel_neper"
val rel_eqN = "rrel_eq"
val rep_bij_uptoN = "rep_bij_upto"
val rep_eqN = "rep_eq"
val cond_eqN = "cond_eq"

fun mk_goals rel_neper rel_eq typedef_rlt rep_eq cond_eq =
  [rel_neper, rel_eq, typedef_rlt, rep_eq] @ the_list cond_eq;

fun dest_goals ([rel_neper] :: [rel_eq] :: [typedef_rlt] :: [rep_eq] :: cond_eq) =
  ({rel_per=rel_neper, rel_eq=rel_eq, bij_upto=typedef_rlt, rep_eq = rep_eq,
   cond_eq = (case cond_eq of [] => NONE | thm :: _ => SOME (hd thm))} : axioms)
  | dest_goals _ = error "Should not happen";

fun wide rin_cont thm relwit repwit_opt cond_opt lthy =
  let
    val (rep, abs, tset) = strip3 thm;
    val repabsT = dest_funT (fastype_of abs);
    val repT = fst repabsT;
    val absT = snd repabsT;
    val absT_name = fst (dest_Type absT);
    val tvs = absT |> dest_Type |> snd;

    val _ = case wide_of lthy absT_name of
        SOME _ => error ("Andrei does not want to override wide entry for type " ^ absT_name)
      | NONE => ();

    fun dest_relT (Type (@{type_name fun}, [T, Type (@{type_name fun}, [_, @{typ bool}])])) = T
      | dest_relT (Type (@{type_name fun}, [_, U])) = dest_relT U
      | dest_relT _ = error "Bad relator type";
    val sorts = relwit |> fastype_of |> dest_relT |> dest_Type |> snd |> map Type.sort_of_atyp;
    val (alphaTs, names_lthy) = lthy |> mk_TFrees' sorts;

    val subst = map (fst o dest_TVar) tvs ~~ alphaTs;
    val RTs = @{map 2} mk_pred2T alphaTs alphaTs

    val rep = subst_TVars subst rep;
    val abs = subst_TVars subst abs;
    val rep_name = rep |> dest_Const |> fst;
    val abs_name = abs |> dest_Const |> fst;
    val repT = typ_subst_TVars subst repT;
    val absT = typ_subst_TVars subst absT;

    val ((x, Rs), names_lthy) = names_lthy
      |> yield_singleton (mk_Frees "x") repT
      ||>> mk_Frees "R" RTs;

    val tset = subst_TVars subst tset;
    val t = case try dest_Collect tset of
        SOME t => t
      | NONE => Term.absfree (dest_Free x) (HOLogic.mk_mem (x, subst_TVars subst tset));

    val lthy = lthy
      |> preregister_quasidef rep_name {c = rep, rhs = Original (mk_rep absT t)}
      |> register_quasidef abs_name {c = abs, rhs = Original (mk_INV rep)};

    val shyps = mk_shyps_term lthy tset;
    val deps = mk_deps lthy (Logic.list_implies (shyps, mk_Trueprop_eq (rep, rep)));
    val depTs = map fastype_of deps;

    val repwitT = RTs ---> depTs ---> absT --> repT;

    val ((zs, f), _) = names_lthy
      |> mk_Frees "z" depTs
      ||>> yield_singleton (mk_Frees "f") repwitT;

    val relwit = singleton (Variable.polymorphic lthy) relwit;
    val relwitT = (RTs ---> depTs ---> mk_pred2T absT absT);
    val relwit = Envir.subst_term_types
      (Sign.typ_match (Proof_Context.theory_of lthy) (fastype_of relwit, relwitT) Vartab.empty
        handle Type.TYPE_MATCH => error ("could not match the type of the given relator " ^
          Syntax.string_of_typ lthy (fastype_of relwit) ^ " with the expected type "
                     ^ Syntax.string_of_typ lthy relwitT ^ " in wide"))
      relwit;

    val lhs = Term.list_comb (relwit, Rs @ zs);

    val alphaTRs = alphaTs ~~ Rs;
    val dzs = deps ~~ zs;

    fun mk_parametrics zs lthy = fold_map (fn z => fn lthy =>
      let val (rin, lthy) = RIN alphaTRs dzs (fastype_of z) lthy
      in (HOLogic.mk_Trueprop (rin $ z $ z), lthy) end) zs lthy;
    val (z_parametrics, lthy) = mk_parametrics zs lthy;

    val nepers = map (HOLogic.mk_Trueprop o mk_neper) Rs;
    val rel_neper = fold_rev Logic.all (Rs @ zs)
      (Logic.list_implies (nepers @ z_parametrics, HOLogic.mk_Trueprop (mk_neper lhs)));

    val eqs = map HOLogic.eq_const alphaTs;
    val eq_deps = eqs @ deps;

    val rel_eq = mk_Trueprop_eq (Term.list_comb (relwit, eq_deps), HOLogic.eq_const absT);
    val (repTrin, lthy) = RIN_gen (rin_cont alphaTRs dzs) alphaTRs dzs repT lthy;
    val (trlt, lthy) = RLT_gen (rin_cont alphaTRs dzs) alphaTRs dzs t lthy;
    val rhs = mk_restr repTrin trlt;

    val repwit =
      (case repwit_opt of
        NONE => f
      | SOME t => t
         |> singleton (Variable.polymorphic lthy)
         |> (fn t => Envir.subst_term_types
            (Sign.typ_match (Proof_Context.theory_of lthy) (fastype_of t, repwitT) Vartab.empty) t
              handle Type.TYPE_MATCH => error ("could not match the type of the provided rep " ^
                Syntax.string_of_typ lthy (fastype_of relwit) ^ " with the expected type "
                           ^ Syntax.string_of_typ lthy relwitT ^ " in wide")));

    val (repwit, rep_def, lthy) =
      (case repwit of
        Const _ => (repwit, refl, lthy)
      | Free _ => (repwit, refl, lthy)
      | _ =>
        let
          val rep_bind = Binding.qualified_name rep_name |> Binding.suffix_name "_rlt";
          val rep_def_bind = (Thm.def_binding rep_bind, []);
          val ((rep_free, (_, rep_def_free)), (lthy, lthy_old)) =
            lthy
            |> (snd o Local_Theory.begin_nested)
            |> Local_Theory.define ((rep_bind, NoSyn), (rep_def_bind, repwit))
            ||> `Local_Theory.end_nested;

          val phi = Proof_Context.export_morphism lthy_old lthy;
          val rep = Const (fst (Term.dest_Const (Morphism.term phi rep_free)), fastype_of repwit);
          val rep_def = Morphism.thm phi rep_def_free;
        in
          (rep, rep_def, lthy)
        end);
    val maybe_ex = (case repwit_opt of NONE => list_exists_free [f] | _ => I)
    val rep_eq = HOLogic.mk_Trueprop (maybe_ex (HOLogic.mk_eq (Term.list_comb (repwit, eq_deps), rep)));
    val bij_upto = maybe_ex (mk_bij_upto lhs rhs (Term.list_comb (repwit, Rs @ zs)));
    val (shyps_rlt, lthy) = fold_map (RLT alphaTRs dzs) shyps lthy

    val condT = RTs ---> depTs ---> @{typ bool};
    val cond = cond_opt |> Option.map (fn t => t
     |> singleton (Variable.polymorphic lthy)
     |> (fn t => Envir.subst_term_types
        (Sign.typ_match (Proof_Context.theory_of lthy) (fastype_of t, condT) Vartab.empty) t
          handle Type.TYPE_MATCH => error ("could not match the type of the provided condition " ^
            Syntax.string_of_typ lthy (fastype_of relwit) ^ " with the expected type "
                       ^ Syntax.string_of_typ lthy relwitT ^ " in wide")));
    val (cond, cond_def, lthy) =
      (case cond of
        NONE => (cond, refl, lthy)
      | SOME (Const _) => (cond, refl, lthy)
      | SOME (Free _) => (cond, refl, lthy)
      | SOME cond =>
        let
          val cond_bind = Binding.qualified_name absT_name |> Binding.suffix_name "_cond";
          val cond_def_bind = (Thm.def_binding cond_bind, []);
          val ((cond_free, (_, cond_def_free)), (lthy, lthy_old)) =
            lthy
            |> (snd o Local_Theory.begin_nested)
            |> Local_Theory.define ((cond_bind, NoSyn), (cond_def_bind, cond))
            ||> `Local_Theory.end_nested;

          val phi = Proof_Context.export_morphism lthy_old lthy;
          val cond = Const (fst (Term.dest_Const (Morphism.term phi cond_free)), fastype_of cond);
          val cond_def = Morphism.thm phi cond_def_free;
        in
          (SOME cond, cond_def, lthy)
        end);

    val conds = the_list (Option.map (fn t => HOLogic.mk_Trueprop (Term.list_comb (t, Rs @ zs))) cond)
    val typedef_rlt = fold_rev Logic.all (Rs @ zs)
      (Logic.list_implies (nepers @ z_parametrics @ shyps_rlt @ conds, HOLogic.mk_Trueprop bij_upto));

    val cond_eq = Option.map (fn t => HOLogic.mk_Trueprop (Term.list_comb (t, eq_deps))) cond;

    val goals = mk_goals rel_neper rel_eq typedef_rlt rep_eq cond_eq;

    fun after_qed thms lthy =
      let

        val axioms = dest_goals thms;

        val lthy = lthy
          |> register_wide absT_name {T=absT, axioms=axioms, facts={}, rel=relwit,
            deps=deps, cond=cond};

        val rep_rhs = (case repwit_opt of
            NONE => Original (mk_rep absT t)
          | SOME _ => Relativized {alphaTs = alphaTs, ds = deps, cT = repwitT, crlt = repwit})

        val lthy = lthy
          |> register_quasidef rep_name {c = rep, rhs = rep_rhs};

        val notes =
          ([(rel_neperN, [#rel_per axioms], @{attributes [neper]}),
           (rel_eqN, [#rel_eq axioms], if null (no_refl [#rel_eq axioms]) then [] else @{attributes [rrel_eq]}),
           (rep_bij_uptoN, [#bij_upto axioms], []),
           (rep_eqN, [#rep_eq axioms], @{attributes [rep_eq]})] @
          (case #cond_eq axioms of SOME thm => [(cond_eqN, [thm], @{attributes [cond_eq]})] | _ => []))
          |> map (fn (thmN, thms, atts) =>
            ((Binding.qualify true (Binding.qualified_name absT_name |> Binding.name_of) (Binding.name thmN), []),
             [(thms, atts)]));

      in
       lthy
       |> Local_Theory.notes notes |> snd
      end;
  in
    (goals, after_qed, no_refl [rep_def, cond_def], lthy)
  end;

(** main commands **)

local

fun prepare_common prepare_name prepare_term prepare_thm rin_cont
    ((((raw_absT_name, raw_relwit), raw_repwit_opt), raw_cond_opt), xthm_opt) lthy =
  let
    val absT_name = prepare_name lthy raw_absT_name;

    fun bad_input input =
      Pretty.chunks [Pretty.para ("Expected theorem of the form:"),
      Pretty.item [Syntax.pretty_term lthy @{term "type_definition Rep Abs A"}],
      Pretty.para ("Got"), Thm.pretty_thm lthy input]
      |> Pretty.string_of
      |> error;

    val typedef_thm =
      (case Option.map (prepare_thm lthy) xthm_opt of
        SOME thm =>(if can (fn thm => thm RS @{thm type_definition.Rep}) thm
          then thm
          else bad_input thm)
      | NONE => Typedef.get_info lthy absT_name |> hd |> snd |> #type_definition);
    val relwit = prepare_term lthy raw_relwit;
    val repwit_opt = Option.map (prepare_term lthy) raw_repwit_opt;
    val cond_opt = Option.map (prepare_term lthy) raw_cond_opt;
  in
    wide rin_cont typedef_thm relwit repwit_opt cond_opt lthy
  end;

fun prepare_wide_typedef prepare_name prepare_term prepare_thm rin_cont =
  (fn (goals, after_qed, defs, lthy) =>
    lthy
    |> Proof.theorem NONE after_qed (map (single o rpair []) goals)
    |> Proof.refine_singleton
      (Method.Basic (fn ctxt => SIMPLE_METHOD (BNF_Tactics.unfold_thms_tac ctxt defs)))
    |> Proof.refine_singleton (Method.primitive_text (K I))) oo
  prepare_common prepare_name prepare_term prepare_thm rin_cont;

fun prepare_solve prepare_name prepare_typ prepare_thm rin_cont tacs =
  (fn (goals, after_qed, defs, lthy) =>
    lthy
    |> after_qed (map2 (fn goal => fn tac => [Goal.prove_sorry lthy [] [] goal
      (fn context as {context = ctxt, prems = _} =>
         BNF_Tactics.unfold_thms_tac ctxt defs THEN tac context)])
      goals tacs)) oo
  prepare_common prepare_name prepare_typ prepare_thm rin_cont;

in 

fun wide_typedef_cmd args =
    prepare_wide_typedef
      (fst o dest_Type oo Proof_Context.read_type_name {proper = true, strict = false})
      Syntax.read_term (fn ctxt => singleton (Attrib.eval_thms ctxt)) rin_cont args
and wide_typedef args tacs = prepare_solve (K I) (K I) (K I) rin_cont tacs args
and rin_cont alphaTRs dzs ctxt (T as Type (C, Ts)) =
  (if can (fn C => (Typedef.get_info ctxt C |> hd |> snd |> #type_definition) RS @{thm type_copy_bij}) C
  then wide_copy (Typedef.get_info ctxt C |> hd) ctxt
   |> (fn ctxt =>
     let
       val wide = the (wide_of ctxt C);
       val deps = mk_deps_of_wide Ts wide;
       val (rins, ctxt) = fold_map (RIN_gen (rin_cont alphaTRs dzs) alphaTRs dzs) Ts ctxt;
       val (rlts, ctxt) = fold_map (RLT_gen (rin_cont alphaTRs dzs) alphaTRs dzs) deps ctxt;
     in
       (list_comb (mk_rel_of_wide Ts wide, rins @ rlts), ctxt)
     end)
  else error ("RIN: encountered a non-wide type " ^ Syntax.string_of_typ ctxt T))
  | rin_cont _ _ _ _ = error "RIN: should not happen"
and wide_copy (typedef : Typedef.info) lthy =
  let
    val AbsT = typedef |> fst |> #abs_type;
    val Ts = AbsT |> dest_Type |> snd;
    val (alphaTs, names_lthy) = lthy
      |> mk_TFrees' (map Type.sort_of_atyp Ts);
    val RTs = @{map 2} mk_pred2T alphaTs alphaTs;
    val (Rs, names_lthy) = mk_Frees "R" RTs names_lthy;

    val AbsT = AbsT |> typ_subst_atomic (Ts ~~ alphaTs);
    val RepT = typedef |> fst |> #rep_type |> typ_subst_atomic (Ts ~~ alphaTs);

    val Rep_name = typedef |> fst |> #Rep_name;

    val Rep = Const (Rep_name, AbsT --> RepT);
    val name = AbsT |> dest_Type |> fst;
    val type_definition = typedef |> snd |> #type_definition;

    val type_Rep = Logic.mk_type RepT;
    val shyps = mk_shyps_term lthy type_Rep;
    val deps = mk_deps lthy (Logic.list_implies (shyps, mk_Trueprop_eq (type_Rep, type_Rep)));
    val depTs = map fastype_of deps;
    val (zs, _) = names_lthy |> mk_Frees "z" depTs;

    val alphaTRs = alphaTs ~~ Rs;
    val dzs = deps ~~ zs;
    val (rin, lthy) = RIN_gen (rin_cont alphaTRs dzs) alphaTRs dzs RepT lthy;
    val rel_spec = BNF_Util.mk_vimage2p Rep Rep $ rin |> fold_rev Term.lambda (Rs @ zs);

    val rel_bind = Binding.qualified_name name |> Binding.prefix_name "rrel_";
    val rel_def_bind = (Thm.def_binding rel_bind, []);

    val ((rel_free, (_, rel_def_free)), (lthy, lthy_old)) =
      lthy
      |> (snd o Local_Theory.begin_nested)
      |> Local_Theory.define ((rel_bind, NoSyn), (rel_def_bind, rel_spec))
      ||> `Local_Theory.end_nested;

    val phi = Proof_Context.export_morphism lthy_old lthy;
    val rel = Const (fst (Term.dest_Const (Morphism.term phi rel_free)), RTs ---> depTs ---> mk_pred2T AbsT AbsT);
    val rel_def = Morphism.thm phi rel_def_free;

    val (conds, lthy) = CND alphaTRs dzs type_Rep lthy;
    val cond = if null conds then NONE
      else SOME (Library.foldr1 HOLogic.mk_conj conds |> fold_rev Term.lambda (Rs @ zs));

    fun retrieve s ctxt = Facts.retrieve (Context.Proof ctxt) (Proof_Context.facts_of ctxt)
      (s, Position.none) |> #thms;
    val neper = retrieve "neper";
    val rrel_eq = retrieve "rrel_eq";
    val cond_eq = retrieve "cond_eq";
    val bij_upto = retrieve "bij_upto";
    fun neper_tac {context = ctxt, prems = _} = (* print_tac ctxt "neper" THEN *)
      BNF_Tactics.unfold_thms_tac ctxt [rel_def] THEN
      HEADGOAL (REPEAT_DETERM o (resolve_tac ctxt
      ((type_definition RS @{thm neper_vimage2p_bij[OF type_copy_bij]}) :: neper ctxt) ORELSE'
       assume_tac ctxt));
    fun rrel_eq_tac {context = ctxt, prems = _} = (* print_tac ctxt "rrel_eq" THEN *)
      BNF_Tactics.unfold_thms_tac ctxt [rel_def] THEN
      HEADGOAL (resolve_tac ctxt [type_definition RS @{thm vimage2p_bij_eq[OF type_copy_bij]}]) THEN
      HEADGOAL (simp_tac (ss_only_distinct (rrel_eq ctxt) ctxt));
    fun bij_upto_tac {context = ctxt, prems = _} = (* print_tac ctxt "bij_upto" THEN *)
      BNF_Tactics.unfold_thms_tac ctxt [rel_def] THEN
      HEADGOAL (asm_simp_tac (ss_only_distinct
        ((type_definition RS @{thm bij_upto_bij[OF type_copy_bij]}) ::
          bij_upto ctxt @ neper ctxt) ctxt))
  in
    lthy
    |> wide_typedef ((((name, rel), SOME (Rep |> fold_rev Term.lambda (Rs @ zs))), cond), SOME type_definition)
       ([neper_tac, rrel_eq_tac, bij_upto_tac,
        fn {context = ctxt, prems = _} => HEADGOAL (resolve_tac ctxt @{thms refl})]
       @ the_list (Option.map (fn _ => fn {context = ctxt, prems = _} =>
         HEADGOAL (simp_tac (ss_only_distinct (rrel_eq ctxt @ cond_eq ctxt) ctxt))) cond))
  end;

end;

(** outer syntax **)

fun parse_aterm s =  (Parse.reserved s -- \<^keyword>\<open>:\<close>) |-- Parse.term;
val parse_xthm = Scan.option (Parse.reserved "via" |-- Parse.thm);

(* exposed commands *)

val _ =
  Outer_Syntax.local_theory_to_proof @{command_keyword wide_typedef}
    "register a defined type as wide"
    ((Parse.type_const -- parse_aterm "rel" -- Scan.option (parse_aterm "rep") --
       Scan.option (parse_aterm "cond") -- parse_xthm) >> wide_typedef_cmd);

end
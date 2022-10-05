signature RELATIVIZATION = sig
  type relativized = {
    alphaTs : typ list,
    ds : term list,
    cT : typ,
    crlt : term
  }

  datatype rhs = Original of term | Relativized of relativized

  type quasidef = {
    c : term,
    rhs : rhs
  }

  val mk_neper: term -> term
  val mk_deps: local_theory -> term -> term list
  val mk_shyps: local_theory -> thm -> term list
  val mk_shyps_term: local_theory -> term -> term list
  val ss_only_distinct: thm list -> Proof.context -> Proof.context
  val definition_of: local_theory -> string * typ -> ((term * term) * string) option

  val RIN_gen: (local_theory -> typ -> term * local_theory) -> (typ * term) list -> (term * term) list -> typ -> local_theory ->  term * local_theory
  val RIN: (typ * term) list -> (term * term) list -> typ -> local_theory -> term * local_theory
  val RLT_gen: (local_theory -> typ -> term * local_theory) -> (typ * term) list -> (term * term) list -> term -> local_theory -> term * local_theory
  val RLT: (typ * term) list -> (term * term) list -> term -> local_theory -> term * local_theory
  val CND: (typ * term) list -> (term * term) list -> term -> local_theory -> term list * local_theory
  val RLTHM: binding -> thm -> local_theory -> thm * local_theory

  val retrieve_or_define: string option -> (local_theory -> typ -> term * local_theory) -> Proof.context -> term -> term -> string -> relativized * Proof.context
  val register_relativized: Symtab.key -> relativized -> local_theory -> local_theory
  val morph_quasidef: morphism -> quasidef -> quasidef
  val quasidef_of: local_theory -> Symtab.key -> quasidef option
  val preregister_quasidef: Symtab.key -> quasidef -> local_theory -> local_theory
  val register_quasidef: Symtab.key -> quasidef -> local_theory -> local_theory
end

structure Relativization : RELATIVIZATION = struct

open BNF_Util
open Wide_Database

type relativized = {
  alphaTs : typ list,
  ds : term list,
  cT : typ,
  crlt : term
}

datatype rhs = Original of term | Relativized of relativized

fun map_rhs f _ (Original t) = Original (f t)
  | map_rhs _ g (Relativized rlt) = Relativized (g rlt)

type quasidef = {
  c : term,
  rhs : rhs
}

fun map_relativized f g ({alphaTs, ds, cT, crlt} : relativized) =
  {alphaTs = map f alphaTs, ds = map g ds, cT = f cT, crlt = g crlt} : relativized;

fun map_quasidef f g h ({c : term, rhs : rhs} : quasidef) =
  {c = f c, rhs = map_rhs g h rhs} : quasidef;

fun morph_relativized phi =
  let
    val Tphi = Morphism.typ phi;
    val tphi = Morphism.term phi;
  in
    map_relativized Tphi tphi
  end;

fun morph_quasidef phi =
  let
    val tphi = Morphism.term phi;
  in
    map_quasidef tphi tphi (morph_relativized phi)
  end;

val transfer_relativized = morph_relativized o Morphism.transfer_morphism;

val transfer_quasidef = morph_quasidef o Morphism.transfer_morphism;

structure Data = Generic_Data
(
  type T = relativized Symtab.table * quasidef Symtab.table;
  val empty = (Symtab.empty, Symtab.empty);
  fun merge ((r, q), (r', q')) = (Symtab.merge (K true) (r, r'), Symtab.merge (K true) (q, q'))
);

fun relativized_of_generic context =
  Option.map (transfer_relativized (Context.theory_of context)) o Symtab.lookup (Data.get context |> fst);

fun quasidef_of_generic context =
  Option.map (transfer_quasidef (Context.theory_of context)) o Symtab.lookup (Data.get context |> snd);

val relativized_of = relativized_of_generic o Context.Proof;
val relativized_of_global = relativized_of_generic o Context.Theory;
val quasidef_of = quasidef_of_generic o Context.Proof;
val quasidef_of_global = quasidef_of_generic o Context.Theory;

fun register_relativized key relc =
  Local_Theory.declaration {syntax = false, pervasive = true}
    (fn phi => Data.map (apfst (Symtab.update (key, morph_relativized phi relc))));

fun preregister_quasidef key qdef lthy =
  lthy
  |> Local_Theory.declaration {syntax = false, pervasive = true}
    (fn phi => Data.map (apsnd (Symtab.update (key, morph_quasidef phi qdef))));

fun register_quasidef key qdef lthy =
  lthy
  |> Local_Theory.declaration {syntax = false, pervasive = true}
    (fn phi => Data.map (apsnd (Symtab.update (key, morph_quasidef phi qdef))))
  |> (case #rhs qdef of 
      Original t => Local_Theory.note ((#c qdef |> dest_Const |> fst  |> space_explode "." |> rev |> hd |> suffix "_qdef" |> Binding.name, @{attributes [quasidef]}),
        [mk_Trueprop_eq (#c qdef, t) |> Skip_Proof.make_thm (Proof_Context.theory_of lthy)])
        #> snd
    | Relativized _ => I);

fun mk_neper R =
  let
    val T = fastype_of R;
  in
    Const (@{const_name neper}, T --> HOLogic.boolT) $ R
  end;

val add_tcon_names = (fold_types o fold_subtypes) (fn Type (name, _) => insert (op =) name | _ => I);

fun specialize_definition_type thy x def0 =
  let
    val def = ATP_Util.specialize_type thy x def0;
    val (lhs, rhs) = Logic.dest_equals def;
  in
    if exists_Const (curry (op =) x) lhs then rhs else raise Fail "cannot specialize"
  end;

fun itself_abs_def ctxt thm =
  let
    fun go ctxt thm =
      (case try (Thm.prop_of #> Logic.dest_equals #> fst #> dest_comb #> fst) thm of
        NONE => thm
      | SOME t => perhaps (try (fn thm => go ctxt
          (thm RS infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt t)] @{thm itself_abs_def}))) thm)
  in
    Variable.trade (fn ctxt => fn thms => [go ctxt (the_single thms)]) ctxt [thm]
    |> the_single
  end;

fun typ_unify_disjointly thy (T, T') =
  if T = T' then
    Vartab.empty
  else
    let
      val tvars = Term.add_tvar_namesT T [];
      val tvars' = Term.add_tvar_namesT T' [];
      val maxidx' = maxidx_of_typ T';
      val T = T |> exists (member (op =) tvars') tvars ? Logic.incr_tvar (maxidx' + 1);
      val maxidx = Integer.max (maxidx_of_typ T) maxidx';
      val (tyenv, _) = Sign.typ_unify thy (T, T') (Vartab.empty, maxidx);
    in
      tyenv
    end;

fun definition_of_gen C_opt ctxt (x as (C, _)) =
  let
    val thy = Proof_Context.theory_of ctxt;
  in
    Defs.specifications_of (Theory.defs_of thy) (Defs.Const, C)
    |> map_filter #def
    |> map_filter (try (`(snd o `(specialize_definition_type thy x) o Thm.prop_of o
         itself_abs_def ctxt o Local_Defs.abs_def_rule ctxt o Thm.axiom thy)))
    |> try hd
    |> Option.map (apfst Logic.dest_equals)
    |> Option.map (apfst (fn (c, t) =>
      let
        val rho = typ_unify_disjointly thy (Sign.the_const_constraint thy 
          (case C_opt of NONE => C | SOME C => C), fastype_of c)
      in
        (Envir.subst_term_types rho c, Envir.subst_term_types rho t)
      end))
  end;

val definition_of = definition_of_gen NONE;

val ordinary_built_ins = [@{const_name "Pure.imp"},
  @{const_name "HOL.Trueprop"}, @{const_name "HOL.implies"},
  @{const_name "Zero_Rep"}, @{const_name "Suc_Rep"}];

val special_built_ins = [@{const_name "HOL.eq"}, @{const_name "undefined"},
  @{const_name "Eps"}, @{const_name "The"},  @{const_name "Pure.eq"}, @{const_name "Pure.all"}];

val built_ins = ordinary_built_ins @ special_built_ins;

fun ss_only_distinct thms = ss_only (distinct Thm.eq_thm_prop (no_refl thms));

fun mk_deps ctxt t =
  let
    val thy = Proof_Context.theory_of ctxt;
    val consts = t |> (fn t => Term.add_const_names t []);
    val tcons = t |> (fn t => add_tcon_names t []);
    val items = map (pair Defs.Const) consts @ map (pair Defs.Type) tcons;
    
    val consts_ctxt = Proof_Context.consts_of ctxt;
    fun mk_instance kt _ (Defs.Const, name) subst =
          kt name (Consts.instance consts_ctxt (name, subst))
      | mk_instance _ kT (Defs.Type, name) Ts =
          kT name Ts;

    fun subst_entry rho (item, Ts) = (item, map (Envir.subst_type rho) Ts);
    fun maybe_subst_deps T U deps depss =
      map (subst_entry (Sign.typ_match thy (T, U) Vartab.empty)) deps :: depss
        handle Type.TYPE_MATCH => depss;

    fun check_subterm deps C T = fold_aterms (fn ci => fn depss =>
      (case ci of
        Const (D, U) => if C = D then maybe_subst_deps T U deps depss else depss
      | _ => depss)) t [];
    fun check_subtype deps C Ts = (fold_types o fold_subtypes) (fn Ti => fn depss =>
      (case Ti of
        Type (D, _) => if C = D then maybe_subst_deps (Type (C, Ts)) Ti deps depss else depss
      | _ => depss)) t [];

    fun fail_types _ _ = raise Fail "type dependencies (declared only types) not allowed"

    val deps = maps (fn item =>
        Defs.get_deps (Theory.defs_of thy) item
        |> maps (fn (subst, deps) => mk_instance (check_subterm deps) (check_subtype deps) item subst)
        |> maps (map (fn (item, subst) => mk_instance pair fail_types item subst))
        |> filter (fn t => definition_of ctxt t = NONE)
        |> map Const)
      items;

    val const_insts = t |> (fn t => Term.add_consts t []);
  in
    distinct (op aconv) (deps @
    map Const (filter (fn t => definition_of ctxt t = NONE andalso quasidef_of ctxt (fst t) = NONE
      andalso List.all (fn c => c <> fst t) built_ins) const_insts))
  end;

fun Eps_rlt_const T = Const (\<^const_name>\<open>Eps_rlt\<close>, (T --> T --> HOLogic.boolT) --> (T --> HOLogic.boolT) --> T);
fun The_rlt_const T = Const (\<^const_name>\<open>The_rlt\<close>, (T --> T --> HOLogic.boolT) --> (T --> HOLogic.boolT) --> T);

fun infer_instantiate_term ctxt args t =
  infer_instantiate ctxt args (Drule.mk_term (Thm.cterm_of ctxt t))
  |> Drule.dest_term |> Thm.term_of;

fun term_for_tvars_and_deps ctxt t =
  let
    val tvars = t |> (fn t => Term.add_tvars t []);
    val (alphaTs, ctxt) = mk_TFrees' (map (fn (_, S) => if null S then\<^sort>\<open>type\<close> else S) tvars) ctxt;
    val RTs = @{map 2} mk_pred2T alphaTs alphaTs;
    val (Rs, ctxt) = mk_Frees "R" RTs ctxt;
    val t = Term.subst_TVars (map fst tvars ~~ alphaTs) t;

    val raw_vars = t |> (fn t => Term.add_vars t []);
    val var_names = map (fst o fst) raw_vars;
    val varTs = map (typ_subst_atomic (map TVar tvars ~~ alphaTs) o snd) raw_vars;
    val (vars, ctxt) = @{fold_map 2} (fn x => yield_singleton (mk_Frees x)) var_names varTs ctxt;
    val t = infer_instantiate_term ctxt (@{map 2} (fn (ix, _) => fn t =>
      (ix, Thm.cterm_of ctxt t)) raw_vars vars) t;
    val deps = mk_deps ctxt t;
    val depTs = map fastype_of deps;

    val (zs, ctxt) = mk_Frees "z" depTs ctxt;
  in
    (tvars, alphaTs, Rs, vars, deps, zs, t, ctxt)
  end;

fun retrieve lthy name cT fail =
  (case relativized_of lthy name of
    SOME relc =>
     let
       val thy = Proof_Context.theory_of lthy;
     in
       let
         val rename = Sign.typ_match thy (#cT relc, cT) Vartab.empty;
       in
         (map_relativized (Envir.subst_type rename) (Envir.subst_term_types rename) relc, lthy)
       end
     end
  | NONE => fail lthy);

val rlt_eqN = "_eq";
val rlt_paramN = "_param";

fun andrei s =
  let
    val n = String.size s;
  in
    if n >= 8 andalso String.substring (s, n - 8, 8) = "_def_raw"
    then String.substring (s, 0, n - 8)
    else 
    if n >= 4 andalso String.substring (s, n - 4, 4) = "_def"
    then String.substring (s, 0, n - 4)
    else s
  end;

fun RIN_gen mk alphaTRs dzs =
  let
    fun rin (TVar _) _ = error "RIN: schematic types not allowed"
      | rin (alphaT as TFree _) ctxt =
          (case AList.lookup (op =) alphaTRs alphaT of
            SOME R => (R, ctxt)
          | _ => error "RIN: unexpected type variable")
      | rin (T as Type (C, Ts)) ctxt =
          if C = @{type_name ind} orelse C = @{type_name bool} orelse C = @{type_name prop}
          then (HOLogic.eq_const T, ctxt)
          else if C = @{type_name fun} then
            let
              val (T, ctxt) = rin (hd Ts) ctxt;
              val (U, ctxt) = rin (hd (tl Ts)) ctxt;
            in (mk_rel_fun T U, ctxt) end
          else (case wide_of ctxt C of
              SOME w => 
              let
                val rho = Sign.typ_match (Proof_Context.theory_of ctxt) (#T w, T) Vartab.empty;
                val deps = map (Envir.subst_term_types rho) (#deps w);
                val (rins, ctxt) = fold_map rin Ts ctxt;
                val (rlts, ctxt) = fold_map (RLT_gen mk alphaTRs dzs) deps ctxt;
              in (list_comb (mk_rel_of_wide Ts w, rins @ rlts), ctxt) end
            | _ => mk ctxt T);
  in
    rin
  end
and apply_crlt rin_cont lthy alphaTRs dzs ({alphaTs, ds, crlt, ...} : relativized) =
  let
    val (rins, lthy) = fold_map (RIN_gen rin_cont alphaTRs dzs) alphaTs lthy;
    val (rltds, lthy) = fold_map (RLT_gen rin_cont alphaTRs dzs) ds lthy;
  in
    (Term.list_comb (Term.list_comb (crlt, rins), rltds), lthy)
  end
and retrieve_or_define C_opt rin_cont lthy c t defname =
  let
    fun add_relativized lthy c t =
      let
        val name = andrei defname ^ "_rlt";
        val b = Binding.qualified_name name;
        val (tvars, alphaTs, Rs, _, deps, zs, _, names_lthy) = term_for_tvars_and_deps lthy c;
        val c_alpha = Term.subst_TVars (map fst tvars ~~ alphaTs) c;
        val t = Term.subst_TVars (map fst tvars ~~ alphaTs) t;
        val talphaTs = map TFree (Term.add_tfrees t []) |> rev;
        val alphaTRs = alphaTs ~~ Rs;
        val alphaTtvars = alphaTs ~~ map TVar tvars;
        val (rlt, lthy) = RLT_gen_opt C_opt rin_cont alphaTRs (deps ~~ zs) t lthy;
        val permuted_Rs = map (the o AList.lookup (op =) alphaTRs) talphaTs;
        val permuted_tvars = map (the o AList.lookup (op =) alphaTtvars) talphaTs;
        val crlt_rhs = fold_rev Term.lambda (permuted_Rs @ zs) rlt;
        val ((raw_crlt, (_, raw_crlt_def)), (lthy, lthy_old)) = lthy
          |> (snd o Local_Theory.begin_nested)
          |> Local_Theory.define ((b, NoSyn), ((Thm.def_binding b, []), crlt_rhs))
          ||> `Local_Theory.end_nested;

        val phi = Proof_Context.export_morphism lthy_old lthy;
        val crlt_name = fst (dest_Const (Morphism.term phi raw_crlt));
        val crlt_def = Morphism.thm phi raw_crlt_def;

        fun retrieve s ctxt = Facts.retrieve (Context.Proof ctxt) (Proof_Context.facts_of ctxt)
          (s, Position.none) |> #thms;
        val rrel_eq = retrieve "rrel_eq";
        val rlt_eq = retrieve "rlt_eq";
        val rep_eq = retrieve "rep_eq";
        val cond_eq = retrieve "cond_eq";
        val quasidef = retrieve "quasidef";
        fun eqs ctxt = rrel_eq ctxt @ rlt_eq ctxt @ rep_eq ctxt @ cond_eq ctxt;
        val crlt = Const (crlt_name, fastype_of crlt_rhs);
        fun c_def ctxt = hd (the_list (try (Thm.axiom (Proof_Context.theory_of lthy)) defname) @
          filter (can (fn thm =>
            trans OF [infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt c_alpha)] refl, thm]))
          (quasidef ctxt))
          |> Local_Defs.abs_def_rule ctxt
          |> itself_abs_def ctxt;
        val eq_args = map (HOLogic.eq_const o fst o dest_pred2T o fastype_of) permuted_Rs;
        val crlt_eq = Goal.prove_sorry lthy [] [] (mk_Trueprop_eq
          (Term.list_comb (crlt, eq_args @ deps), c_alpha))
          (fn {context = ctxt, prems = _} =>
             HEADGOAL (simp_tac (ss_only_distinct (crlt_def :: eqs ctxt @ quasidef ctxt) ctxt) THEN'
               (TRY o simp_tac (ss_only_distinct (c_def ctxt :: quasidef ctxt) ctxt))));

        val crlt_gen = Const (crlt_name, typ_subst_atomic (alphaTs ~~ map TVar tvars) (fastype_of crlt_rhs));
        val relc = {alphaTs = permuted_tvars,
          ds = map (subst_atomic_types (alphaTs ~~ map TVar tvars)) deps,
          cT = fastype_of c,
          crlt = crlt_gen};

        val rlt_params = (if perhaps (try (fn _ => is_parametric rin_cont alphaTRs c_alpha lthy)) false then
            let
              val rlt_param = mk_Trueprop_eq (Term.list_comb (crlt, permuted_Rs @ deps), c_alpha)
                |> curry Logic.list_implies (map (HOLogic.mk_Trueprop o mk_neper) permuted_Rs)
                |> Skip_Proof.make_thm (Proof_Context.theory_of lthy)
                |> singleton (Proof_Context.export names_lthy lthy);
            in
              [(rlt_paramN, [rlt_param], @{attributes [rlt_param]})]
            end
          else []);

        val notes =
          ([(rlt_eqN, [crlt_eq], @{attributes [rlt_eq]})] @ rlt_params)
          |> map (fn (thmN, thms, atts) => ((b |> Binding.suffix_name thmN, []), [(thms, atts)]));
      in
        (relc, lthy
        |> register_relativized defname relc
        |> Local_Theory.notes notes |> snd)
      end;
  in
    retrieve lthy defname (fastype_of c) (fn lthy => add_relativized lthy c t)
  end
and is_parametric rin_cont alphaTRs t ctxt =
  let
    val T = fastype_of t;
    val (rin, ctxt) = RIN_gen rin_cont alphaTRs [] T ctxt;
    val param = HOLogic.mk_Trueprop (rin $ t $ t);
    fun retrieve s ctxt = Facts.retrieve (Context.Proof ctxt) (Proof_Context.facts_of ctxt)
      (s, Position.none) |> #thms;
    val rrel_eq = retrieve "rrel_eq"
    val rrel_alt = retrieve "rrel_alt"
    val transfer_raw = retrieve "transfer_raw"
    val thms = refl :: map (unfold_thms ctxt @{thms Rel_def}) (transfer_raw ctxt)
      |> filter_out (can (Thm.prop_of #> Logic.dest_implies));
  in
    can (Goal.prove ctxt (map (fst o dest_Free o snd) alphaTRs) [] param)
      (fn {context=ctxt, prems=_} =>
        BNF_Tactics.unfold_thms_tac ctxt (rrel_eq ctxt) THEN
        BNF_Tactics.unfold_thms_tac ctxt (rrel_alt ctxt) THEN
        HEADGOAL (resolve_tac ctxt thms))
  end
and RLT_gen rin_cont = RLT_gen_opt NONE rin_cont
and RLT_gen_opt C_opt rin_cont alphaTRs dzs =
  let
    fun rlt (Var _) _ = error "RLT: schematic variables not allowed"
      | rlt (Free (x, S)) lthy = (Free (x, S), lthy)
      | rlt (Bound i) lthy = (Bound i, lthy)
      | rlt (t as Const (C, T)) lthy =
          (if List.exists (fn D => C = D) ordinary_built_ins then (t, lthy)
          else if C = @{const_name "HOL.eq"} then
            RIN_gen rin_cont alphaTRs dzs (dest_pred2T T |> fst) lthy
          else if C = @{const_name "Pure.eq"} then
            let
              val AT = dest_pred2T T |> fst;
              val (rin, lthy) = RIN_gen rin_cont alphaTRs dzs AT lthy;
            in (Abs ("x", AT, Abs ("y", AT,
              HOLogic.mk_Trueprop (rin $ Bound 1 $ Bound 0))), lthy) end
          else if C = @{const_name "Pure.all"} then
            let
              val AT = T |> domain_type |> domain_type;
              val (rin, lthy) = RIN_gen rin_cont alphaTRs dzs AT lthy;
            in (Abs ("P", domain_type T, Logic.all_const AT $
              Abs ("x", AT, Logic.mk_implies (HOLogic.mk_Trueprop (rin $ Bound 0 $ Bound 0),
                Bound 1 $ Bound 0))), lthy) end
          else if C = @{const_name "undefined"} then
            rlt (HOLogic.choice_const T $ absdummy T @{term True}) lthy
          else if C = @{const_name "Eps"} orelse C = @{const_name "The"} then
            let
              val T = fastype_of t |> range_type;
              val (rin, lthy) = RIN_gen rin_cont alphaTRs dzs T lthy;
              val const = if C = @{const_name "Eps"} then Eps_rlt_const else The_rlt_const;
            in
              (const (fastype_of t |> range_type) $ rin, lthy)
            end
          else case AList.lookup (op aconv) dzs t of
            SOME z => (z, lthy)
          | NONE =>
            (case quasidef_of lthy C of
              SOME {c, rhs} => 
              let
(* val _ = @{print} ("before quasidef_of type match:", c, fastype_of c, T) *)
                val rho = Sign.typ_match (Proof_Context.theory_of lthy) (fastype_of c, T) Vartab.empty
                  handle Type.TYPE_MATCH => error ("could not match " ^ Syntax.string_of_typ lthy (fastype_of c) ^ " with "
                     ^ Syntax.string_of_typ lthy T ^ " in rlt (for a quasidef)");
(* val _ = @{print} ("after quasidef_of type match:", rho) *)
                val (relc, lthy) = (case rhs of
                    Original t => retrieve_or_define C_opt rin_cont lthy c t C
                  | Relativized t => (t, lthy));
              in
                apply_crlt rin_cont lthy alphaTRs dzs
                  (map_relativized (Envir.subst_type rho) (Envir.subst_term_types rho) relc)
              end
            | NONE => (case definition_of_gen C_opt lthy (C, T) of
                SOME ((c, rhs), defname) =>
                  let
(* val _ = @{print warning} ("before definition_of type match:", c, fastype_of c, T) *)
                    val rho = Sign.typ_match (Proof_Context.theory_of lthy) (fastype_of c, T) Vartab.empty
                  handle Type.TYPE_MATCH => error ("could not match " ^ Syntax.string_of_typ lthy (fastype_of c) ^ " with "
                     ^ Syntax.string_of_typ lthy T ^ " in rlt (for a definition)");
(* val _ = @{print warning} ("after definition_of type match:", rho) *)
(* val _ = @{print} (c, rhs, defname); *)
                    val C_opt = if Axclass.unoverload_const (Proof_Context.theory_of lthy) (C, T) = C
                      then NONE else SOME C;
                    val (relc, lthy) = retrieve_or_define C_opt rin_cont lthy c rhs defname;
                  in
                    apply_crlt rin_cont lthy alphaTRs dzs
                      (map_relativized (Envir.subst_type rho) (Envir.subst_term_types rho) relc)
                  end
              | NONE => (AList.lookup (op aconv) dzs t |> the
                  handle Option.Option => error ("RLT: unexpected crlt " ^ C ^ " \
\instance " ^ Syntax.string_of_typ lthy T ^ " neither declared nor defined."), lthy))))
      | rlt (Abs (x, T, t)) lthy = let val (t, lthy) = rlt t lthy in (Abs (x, T, t), lthy) end
      | rlt (t $ u) lthy =
          let
            val (t, lthy) = rlt t lthy;
            val (u, lthy) = rlt u lthy;
          in (t $ u, lthy) end;
  in
    rlt
  end;

val RIN = RIN_gen (fn ctxt => fn T =>
  error ("RIN: encountered a non-wide type " ^ Syntax.string_of_typ ctxt T))

val RLT_gen = RLT_gen_opt NONE;
val RLT = RLT_gen (fn ctxt => fn T =>
  error ("RLT: encountered a non-wide type " ^ Syntax.string_of_typ ctxt T));

fun mk_shyps lthy thm =
  let
    val deps = mk_deps lthy (thm |> Thm.prop_of);
    val thy = Proof_Context.theory_of lthy;
    val shyps = thm |> Thm.shyps_of |> flat
      |> filter_out (fn s => [s] = \<^sort>\<open>type\<close>)
      |> map_filter (Class.rules thy #> fst)
      |> map (`(snd o strip_comb o HOLogic.dest_Trueprop) o Thm.prop_of)
      |> maps (fn (cs, hyp) =>
          let
            val rhos = maps (fn c => maps (fn d =>
              the_list (try (Sign.typ_match thy (fastype_of c, fastype_of d)) Vartab.empty)) deps) cs
          in
            distinct (op aconv) (map (fn rho => Envir.subst_term_types rho hyp) rhos)
          end);
  in
    shyps
  end;
fun mk_shyps_term lthy t =
  mk_shyps lthy (infer_instantiate' lthy [SOME (Thm.cterm_of lthy t)] refl);

fun mk_type_cond alphaTRs dzs (T as Type (name, Ts)) ctxt =
    (case Option.join (Option.map get_cond (wide_of ctxt name)) of
      NONE => ([], ctxt)
    | SOME ((U, cs), cond) =>
      let
(* val _ = @{print warning} (T,U, (cs, cond)) *)
        val rho = Sign.typ_match (Proof_Context.theory_of ctxt) (U, T) Vartab.empty
          handle Type.TYPE_MATCH => error ("could not match " ^ Syntax.string_of_typ ctxt U ^ " with "
             ^ Syntax.string_of_typ ctxt T ^ " in mk_type_cond");
        val (rins, ctxt) = fold_map (RIN alphaTRs dzs) Ts ctxt;
        val (rlts, ctxt) = fold_map (RLT alphaTRs dzs o Envir.subst_term_types rho) cs ctxt;
      in
        ([Term.list_comb (Envir.subst_term_types rho cond, rins @ rlts)], ctxt)
      end)
  | mk_type_cond _ _ _ ctxt = ([], ctxt);

fun CND alphaTRs dzs t ctxt =
  let
    val Ts = (fold_types o fold_subtypes) (fn T as Type (_, _) => insert (op =) T | _ => I) t [];
  in
    fold_map (mk_type_cond alphaTRs dzs) Ts ctxt |>> flat
  end;

fun RLTHM b thm lthy =
  let
    val goal = Logic.list_implies (mk_shyps lthy thm, thm |> Thm.prop_of);
    val (_, alphaTs, Rs, vars, ds, zs, goal, names_lthy) = term_for_tvars_and_deps lthy goal;
    val nepers = map (HOLogic.mk_Trueprop o mk_neper) Rs;
    val alphaTRs = alphaTs ~~ Rs;
    val dzs = ds ~~ zs;

    fun mk_parametrics zs lthy = fold_map (fn z => fn lthy =>
      let val (rin, lthy) = RIN alphaTRs dzs (fastype_of z) lthy
      in (HOLogic.mk_Trueprop (rin $ z $ z), lthy) end) zs lthy;
    val (z_parametrics, lthy) = mk_parametrics zs lthy;
    val (x_parametrics, lthy) = mk_parametrics vars lthy;
    val (concl, lthy) = RLT alphaTRs dzs goal lthy;
    val (conds, lthy) = CND alphaTRs dzs goal lthy |>> map HOLogic.mk_Trueprop;

    val (relthm, lthy) = Logic.list_implies (nepers @ z_parametrics @ x_parametrics @ conds, concl)
      |> Skip_Proof.make_thm (Proof_Context.theory_of lthy)
      |> singleton (Proof_Context.export names_lthy lthy)
      |> (fn thm => Local_Theory.note ((b, []), [thm]) lthy)
      |>> the_single o snd;
  in
    (relthm, lthy)
  end;

end
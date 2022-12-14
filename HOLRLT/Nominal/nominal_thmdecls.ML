(*  Title:      HOL/Nominal/nominal_thmdecls.ML
    Author:     Julien Narboux, TU Muenchen
    Author:     Christian Urban, TU Muenchen

Infrastructure for the lemma collection "eqvts".

By attaching [eqvt] or [eqvt_force] to a lemma, it will get stored in
a data-slot in the context. Possible modifiers are [... add] and
[... del] for adding and deleting, respectively, the lemma from the
data-slot.
*)

signature NOMINAL_THMDECLS =
sig
  val nominal_eqvt_debug: bool Config.T
  val eqvt_add: attribute
  val eqvt_del: attribute
  val eqvt_force_add: attribute
  val eqvt_force_del: attribute
  val setup: theory -> theory
  val get_eqvt_thms: Proof.context -> thm list
end;

structure NominalThmDecls: NOMINAL_THMDECLS =
struct

structure Data = Generic_Data
(
  type T = thm list
  val empty = []
  val merge = Thm.merge_thms
)

(* Exception for when a theorem does not conform with form of an equivariance lemma. *)
(* There are two forms: one is an implication (for relations) and the other is an    *)
(* equality (for functions). In the implication-case, say P ==> Q, Q must be equal   *)
(* to P except that every free variable of Q, say x, is replaced by pi o x. In the   *)
(* equality case, say lhs = rhs, the lhs must be of the form pi o t and the rhs must *)
(* be equal to t except that every free variable, say x, is replaced by pi o x. In   *)
(* the implicational case it is also checked that the variables and permutation fit  *)
(* together, i.e. are of the right "pt_class", so that a stronger version of the     *)
(* equality-lemma can be derived. *)
exception EQVT_FORM of string

val nominal_eqvt_debug = Attrib.setup_config_bool \<^binding>\<open>nominal_eqvt_debug\<close> (K false);

fun tactic ctxt (msg, tac) =
  if Config.get ctxt nominal_eqvt_debug
  then tac THEN' (K (print_tac ctxt ("after " ^ msg)))
  else tac

fun prove_eqvt_tac ctxt orig_thm pi pi' =
  let
    val thy = Proof_Context.theory_of ctxt
    val T = fastype_of pi'
    val mypifree = Thm.cterm_of ctxt (Const (\<^const_name>\<open>rev\<close>, T --> T) $ pi')
    val perm_pi_simp = Global_Theory.get_thms thy "perm_pi_simp"
  in
    EVERY1 [tactic ctxt ("iffI applied", resolve_tac ctxt @{thms iffI}),
            tactic ctxt ("remove pi with perm_boolE", dresolve_tac ctxt @{thms perm_boolE}),
            tactic ctxt ("solve with orig_thm", eresolve_tac ctxt [orig_thm]),
            tactic ctxt ("applies orig_thm instantiated with rev pi",
               dresolve_tac ctxt [infer_instantiate ctxt [(#1 (dest_Var pi), mypifree)] orig_thm]),
            tactic ctxt ("getting rid of the pi on the right", resolve_tac ctxt @{thms perm_boolI}),
            tactic ctxt ("getting rid of all remaining perms",
                       full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps perm_pi_simp))]
  end;

fun get_derived_thm ctxt hyp concl orig_thm pi typi =
  let
    val pi' = Var (pi, typi);
    val lhs = Const (\<^const_name>\<open>perm\<close>, typi --> HOLogic.boolT --> HOLogic.boolT) $ pi' $ hyp;
    val ([goal_term, pi''], ctxt') = Variable.import_terms false
      [HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, concl)), pi'] ctxt
    val _ = writeln (Syntax.string_of_term ctxt' goal_term);
  in
    Goal.prove ctxt' [] [] goal_term
      (fn _ => prove_eqvt_tac ctxt' orig_thm pi' pi'') |>
    singleton (Proof_Context.export ctxt' ctxt)
  end

(* replaces in t every variable, say x, with pi o x *)
fun apply_pi trm (pi, typi) =
let
  fun replace n ty =
  let 
    val c  = Const (\<^const_name>\<open>perm\<close>, typi --> ty --> ty) 
    val v1 = Var (pi, typi)
    val v2 = Var (n, ty)
  in
    c $ v1 $ v2 
  end
in
  map_aterms (fn Var (n, ty) => replace n ty | t => t) trm
end

(* returns *the* pi which is in front of all variables, provided there *)
(* exists such a pi; otherwise raises EQVT_FORM                        *)
fun get_pi t thy =
  let fun get_pi_aux s =
        (case s of
          (Const (\<^const_name>\<open>perm\<close> ,typrm) $
             (Var (pi,typi as Type(\<^type_name>\<open>list\<close>, [Type (\<^type_name>\<open>Product_Type.prod\<close>, [Type (tyatm,[]),_])]))) $
               (Var (n,ty))) =>
             let
                (* FIXME: this should be an operation the library *)
                val class_name = (Long_Name.map_base_name (fn s => "pt_"^s) tyatm)
             in
                if (Sign.of_sort thy (ty,[class_name]))
                then [(pi,typi)]
                else raise
                EQVT_FORM ("Could not find any permutation or an argument is not an instance of "^class_name)
             end
        | Abs (_,_,t1) => get_pi_aux t1
        | (t1 $ t2) => get_pi_aux t1 @ get_pi_aux t2
        | _ => [])
  in
    (* collect first all pi's in front of variables in t and then use distinct *)
    (* to ensure that all pi's must have been the same, i.e. distinct returns  *)
    (* a singleton-list  *)
    (case (distinct (op =) (get_pi_aux t)) of
      [(pi,typi)] => (pi, typi)
    | _ => raise EQVT_FORM "All permutation should be the same")
  end;

(* Either adds a theorem (orig_thm) to or deletes one from the equivariance *)
(* lemma list depending on flag. To be added the lemma has to satisfy a     *)
(* certain form. *)

fun eqvt_add_del_aux flag orig_thm context = 
  let
    val thy = Context.theory_of context
    val thms_to_be_added =
      (case Thm.prop_of orig_thm of
        (* case: eqvt-lemma is of the implicational form *)
        (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ (Const (\<^const_name>\<open>Trueprop\<close>,_) $ hyp) $ (Const (\<^const_name>\<open>Trueprop\<close>,_) $ concl)) =>
          let
            val (pi,typi) = get_pi concl thy
          in
             if (apply_pi hyp (pi,typi) = concl)
             then
               (warning ("equivariance lemma of the relational form");
                [orig_thm,
                 get_derived_thm (Context.proof_of context) hyp concl orig_thm pi typi])
             else raise EQVT_FORM "Type Implication"
          end
       (* case: eqvt-lemma is of the equational form *)
      | (Const (\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $
            (Const (\<^const_name>\<open>perm\<close>,typrm) $ Var (pi,typi) $ lhs) $ rhs)) =>
           (if (apply_pi lhs (pi,typi)) = rhs
               then [orig_thm]
               else raise EQVT_FORM "Type Equality")
      | _ => raise EQVT_FORM "Type unknown")
  in
      fold (fn thm => Data.map (flag thm)) thms_to_be_added context
  end
  handle EQVT_FORM s =>
      error (Thm.string_of_thm (Context.proof_of context) orig_thm ^ 
               " does not comply with the form of an equivariance lemma (" ^ s ^").")


val eqvt_add = Thm.declaration_attribute (eqvt_add_del_aux (Thm.add_thm));
val eqvt_del = Thm.declaration_attribute (eqvt_add_del_aux (Thm.del_thm));

val eqvt_force_add  = Thm.declaration_attribute (Data.map o Thm.add_thm);
val eqvt_force_del  = Thm.declaration_attribute (Data.map o Thm.del_thm);

val get_eqvt_thms = Context.Proof #> Data.get;

val setup =
  Attrib.setup \<^binding>\<open>eqvt\<close> (Attrib.add_del eqvt_add eqvt_del) 
   "equivariance theorem declaration" #>
  Attrib.setup \<^binding>\<open>eqvt_force\<close> (Attrib.add_del eqvt_force_add eqvt_force_del)
    "equivariance theorem declaration (without checking the form of the lemma)" #>
  Global_Theory.add_thms_dynamic (\<^binding>\<open>eqvts\<close>, Data.get);


end;

(*  Title:      HOL/Tools/SMT/smt_builtin.ML
    Author:     Sascha Boehme, TU Muenchen

Tables of types and terms directly supported by SMT solvers.
*)

signature SMT_BUILTIN =
sig
  (*for experiments*)
  val filter_builtins: (typ -> bool) -> Proof.context -> Proof.context

  (*built-in types*)
  val add_builtin_typ: SMT_Util.class ->
    typ * (typ -> (string * typ list) option) * (typ -> int -> string option) -> Context.generic ->
    Context.generic
  val add_builtin_typ_ext: typ * (Proof.context -> typ -> bool) -> Context.generic ->
    Context.generic
  val dest_builtin_typ: Proof.context -> typ -> (string * typ list) option
  val is_builtin_typ_ext: Proof.context -> typ -> bool

  (*built-in numbers*)
  val dest_builtin_num: Proof.context -> term -> (string * typ) option
  val is_builtin_num: Proof.context -> term -> bool
  val is_builtin_num_ext: Proof.context -> term -> bool

  (*built-in functions*)
  type 'a bfun = Proof.context -> typ -> term list -> 'a
  type bfunr = string * int * term list * (term list -> term)
  val add_builtin_fun: SMT_Util.class -> (string * typ) * bfunr option bfun -> Context.generic ->
    Context.generic
  val add_builtin_fun': SMT_Util.class -> term * string -> Context.generic -> Context.generic
  val add_builtin_fun_ext: (string * typ) * term list bfun -> Context.generic -> Context.generic
  val add_builtin_fun_ext': string * typ -> Context.generic -> Context.generic
  val add_builtin_fun_ext'': string -> Context.generic -> Context.generic
  val dest_builtin_fun: Proof.context -> string * typ -> term list -> bfunr option
  val dest_builtin_eq: Proof.context -> term -> term -> bfunr option
  val dest_builtin_pred: Proof.context -> string * typ -> term list -> bfunr option
  val dest_builtin_conn: Proof.context -> string * typ -> term list -> bfunr option
  val dest_builtin: Proof.context -> string * typ -> term list -> bfunr option
  val dest_builtin_ext: Proof.context -> string * typ -> term list -> term list option
  val is_builtin_fun: Proof.context -> string * typ -> term list -> bool
  val is_builtin_fun_ext: Proof.context -> string * typ -> term list -> bool
end;

structure SMT_Builtin: SMT_BUILTIN =
struct


(* built-in tables *)

datatype ('a, 'b) kind = Ext of 'a | Int of 'b

type ('a, 'b) ttab = ((typ * ('a, 'b) kind) Ord_List.T) SMT_Util.dict

fun typ_ord ((T, _), (U, _)) =
  let
    fun tord (TVar _, Type _) = GREATER
      | tord (Type _, TVar _) = LESS
      | tord (Type (n, Ts), Type (m, Us)) =
          if n = m then list_ord tord (Ts, Us)
          else Term_Ord.typ_ord (T, U)
      | tord TU = Term_Ord.typ_ord TU
  in tord (T, U) end

fun insert_ttab cs T f =
  SMT_Util.dict_map_default (cs, [])
    (Ord_List.insert typ_ord (perhaps (try Logic.varifyT_global) T, f))

fun merge_ttab ttabp = SMT_Util.dict_merge (Ord_List.merge typ_ord) ttabp

fun lookup_ttab ctxt ttab T =
  let fun match (U, _) = Sign.typ_instance (Proof_Context.theory_of ctxt) (T, U)
  in
    get_first (find_first match) (SMT_Util.dict_lookup ttab (SMT_Config.solver_class_of ctxt))
  end

type ('a, 'b) btab = ('a, 'b) ttab Symtab.table

fun insert_btab cs n T f =
  Symtab.map_default (n, []) (insert_ttab cs T f)

fun merge_btab btabp = Symtab.join (K merge_ttab) btabp

fun lookup_btab ctxt btab (n, T) =
  (case Symtab.lookup btab n of
    NONE => NONE
  | SOME ttab => lookup_ttab ctxt ttab T)

type 'a bfun = Proof.context -> typ -> term list -> 'a

type bfunr = string * int * term list * (term list -> term)

structure Builtins = Generic_Data
(
  type T =
    (Proof.context -> typ -> bool,
     (typ -> (string * typ list) option) * (typ -> int -> string option)) ttab *
    (term list bfun, bfunr option bfun) btab
  val empty = ([], Symtab.empty)
  fun merge ((t1, b1), (t2, b2)) = (merge_ttab (t1, t2), merge_btab (b1, b2))
)

fun filter_ttab keep_T = map (apsnd (filter (keep_T o fst)))

fun filter_builtins keep_T =
  Context.proof_map (Builtins.map (fn (ttab, btab) =>
    (filter_ttab keep_T ttab, Symtab.map (K (filter_ttab keep_T)) btab)))


(* built-in types *)

fun add_builtin_typ cs (T, f, g) =
  Builtins.map (apfst (insert_ttab cs T (Int (f, g))))

fun add_builtin_typ_ext (T, f) = Builtins.map (apfst (insert_ttab SMT_Util.basicC T (Ext f)))

fun lookup_builtin_typ ctxt =
  lookup_ttab ctxt (fst (Builtins.get (Context.Proof ctxt)))

fun dest_builtin_typ ctxt T =
  (case lookup_builtin_typ ctxt T of
    SOME (_, Int (f, _)) => f T
  | _ => NONE)

fun is_builtin_typ_ext ctxt T =
  (case lookup_builtin_typ ctxt T of
    SOME (_, Int (f, _)) => is_some (f T)
  | SOME (_, Ext f) => f ctxt T
  | NONE => false)


(* built-in numbers *)

fun dest_builtin_num ctxt t =
  (case try HOLogic.dest_number t of
    NONE => NONE
  | SOME (T, i) =>
      if i < 0 then NONE else
        (case lookup_builtin_typ ctxt T of
          SOME (_, Int (_, g)) => g T i |> Option.map (rpair T)
        | _ => NONE))

val is_builtin_num = is_some oo dest_builtin_num

fun is_builtin_num_ext ctxt t =
  (case try HOLogic.dest_number t of
    NONE => false
  | SOME (T, _) => is_builtin_typ_ext ctxt T)


(* built-in functions *)

fun add_builtin_fun cs ((n, T), f) =
  Builtins.map (apsnd (insert_btab cs n T (Int f)))

fun add_builtin_fun' cs (t, n) =
  let
    val c as (m, T) = Term.dest_Const t
    fun app U ts = Term.list_comb (Const (m, U), ts)
    fun bfun _ U ts = SOME (n, length (Term.binder_types T), ts, app U)
  in add_builtin_fun cs (c, bfun) end

fun add_builtin_fun_ext ((n, T), f) =
  Builtins.map (apsnd (insert_btab SMT_Util.basicC n T (Ext f)))

fun add_builtin_fun_ext' c = add_builtin_fun_ext (c, fn _ => fn _ => I)

fun add_builtin_fun_ext'' n context =
  let val thy = Context.theory_of context
  in add_builtin_fun_ext' (n, Sign.the_const_type thy n) context end

fun lookup_builtin_fun ctxt =
  lookup_btab ctxt (snd (Builtins.get (Context.Proof ctxt)))

fun dest_builtin_fun ctxt (c as (_, T)) ts =
  (case lookup_builtin_fun ctxt c of
    SOME (_, Int f) => f ctxt T ts
  | _ => NONE)

fun dest_builtin_eq ctxt t u =
  let
    val aT = Term.aT \<^sort>\<open>type\<close>
    val c = (\<^const_name>\<open>HOL.eq\<close>, aT --> aT --> \<^typ>\<open>bool\<close>)
    fun mk ts = Term.list_comb (HOLogic.eq_const (Term.fastype_of (hd ts)), ts)
  in
    dest_builtin_fun ctxt c []
    |> Option.map (fn (n, i, _, _) => (n, i, [t, u], mk))
  end

fun special_builtin_fun pred ctxt (c as (_, T)) ts =
  if pred (Term.body_type T, Term.binder_types T) then
    dest_builtin_fun ctxt c ts
  else NONE

fun dest_builtin_pred ctxt = special_builtin_fun (equal \<^typ>\<open>bool\<close> o fst) ctxt

fun dest_builtin_conn ctxt =
  special_builtin_fun (forall (equal \<^typ>\<open>bool\<close>) o (op ::)) ctxt

fun dest_builtin ctxt c ts =
  let val t = Term.list_comb (Const c, ts)
  in
    (case dest_builtin_num ctxt t of
      SOME (n, _) => SOME (n, 0, [], K t)
    | NONE => dest_builtin_fun ctxt c ts)
  end

fun dest_builtin_fun_ext ctxt (c as (_, T)) ts =
  (case lookup_builtin_fun ctxt c of
    SOME (_, Int f) => f ctxt T ts |> Option.map (fn (_, _, us, _) => us)
  | SOME (_, Ext f) => SOME (f ctxt T ts)
  | NONE => NONE)

fun dest_builtin_ext ctxt c ts =
  if is_builtin_num_ext ctxt (Term.list_comb (Const c, ts)) then SOME []
  else dest_builtin_fun_ext ctxt c ts

fun is_builtin_fun ctxt c ts = is_some (dest_builtin_fun ctxt c ts)

fun is_builtin_fun_ext ctxt c ts = is_some (dest_builtin_fun_ext ctxt c ts)

end;

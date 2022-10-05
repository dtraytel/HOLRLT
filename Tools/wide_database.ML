signature WIDE_DATABASE = sig

type axioms = {
  rel_per : thm,
  rel_eq : thm,
  bij_upto : thm,
  rep_eq : thm,
  cond_eq : thm option
}
type facts = {}
type wide = {T: typ, axioms: axioms, facts: facts, rel: term, deps: term list, cond: term option}
val wide_of: Proof.context -> Symtab.key -> wide option
val wide_of_generic: Context.generic -> Symtab.key -> wide option
val wide_of_global: theory -> Symtab.key -> wide option
val register_wide: Symtab.key -> wide -> local_theory -> local_theory
val mk_rel_of_wide: typ list -> wide -> term
val mk_deps_of_wide: typ list -> wide -> term list
val get_cond: wide -> ((typ * term list) * term) option

end

structure Wide_Database : WIDE_DATABASE = struct

type axioms = {
  rel_per : thm,
  rel_eq : thm,
  bij_upto : thm,
  rep_eq : thm,
  cond_eq : thm option
}

type facts = {}

type wide = {
  T : typ,
  rel : term,
  axioms : axioms,
  facts : facts,
  deps : term list,
  cond: term option
}

fun map_axioms f {rel_per, rel_eq, bij_upto, rep_eq, cond_eq} =
  {rel_per = f rel_per,
    rel_eq = f rel_eq,
    bij_upto = f bij_upto,
    rep_eq = f rep_eq,
    cond_eq = Option.map f cond_eq};

val morph_axioms = map_axioms o Morphism.thm;

fun map_facts _ {} = {};

val morph_facts = map_facts o Morphism.thm;

fun map_wide f1 f2 f3 f4 f5 f6 ({T, rel, axioms, facts, deps, cond} : wide) =
  ({T = f1 T, 
    rel = f2 rel,
    axioms = f3 axioms,
    facts = f4 facts,
    deps = f5 deps,
    cond = f6 cond}) : wide;

fun morph_wide phi =
  let
    val Tphi = Morphism.typ phi;
    val tphi = Morphism.term phi;
  in
    map_wide Tphi tphi (morph_axioms phi) (morph_facts phi) (map tphi) (Option.map tphi)
  end;

val transfer_wide = morph_wide o Morphism.transfer_morphism;

structure Data = Generic_Data
(
  type T = wide Symtab.table;
  val empty = Symtab.empty;
  val merge = Symtab.merge (K true);
);


fun wide_of_generic context =
  Option.map (transfer_wide (Context.theory_of context)) o Symtab.lookup (Data.get context);

val wide_of = wide_of_generic o Context.Proof;
val wide_of_global = wide_of_generic o Context.Theory;

fun register_wide key wide =
  Local_Theory.declaration {syntax = false, pervasive = true}
    (fn phi => Data.map (Symtab.update_new (key, morph_wide phi wide)));

fun mk_rel_of_wide Ts (wide : wide) =
  let
    val As = #T wide |> dest_Type |> snd;
  in
    Term.subst_atomic_types (As ~~ Ts) (#rel wide)
  end;

fun mk_deps_of_wide Ts (wide : wide) =
  let
    val As = #T wide |> dest_Type |> snd;
  in
    map (Term.subst_atomic_types (As ~~ Ts)) (#deps wide)
  end;

fun get_cond (wide : wide) = Option.map (pair (#T wide, #deps wide)) (#cond wide);

end
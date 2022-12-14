(*  Title:      HOL/Tools/SMT/z3_replay_rules.ML
    Author:     Sascha Boehme, TU Muenchen

Custom rules for Z3 proof replay.
*)

signature Z3_REPLAY_RULES =
sig
  val apply: Proof.context -> cterm -> thm option
end;

structure Z3_Replay_Rules: Z3_REPLAY_RULES =
struct

structure Data = Generic_Data
(
  type T = thm Net.net
  val empty = Net.empty
  val merge = Net.merge Thm.eq_thm
)

fun maybe_instantiate ct thm =
  try Thm.first_order_match (Thm.cprop_of thm, ct)
  |> Option.map (fn inst => Thm.instantiate inst thm)

fun apply ctxt ct =
  let
    val net = Data.get (Context.Proof ctxt)
    val xthms = Net.match_term net (Thm.term_of ct)

    fun select ct = map_filter (maybe_instantiate ct) xthms
    fun select' ct =
      let val thm = Thm.trivial ct
      in map_filter (try (fn rule => rule COMP thm)) xthms end

  in try hd (case select ct of [] => select' ct | xthms' => xthms') end

val prep = `Thm.prop_of

fun ins thm net = Net.insert_term Thm.eq_thm (prep thm) net handle Net.INSERT => net
fun del thm net = Net.delete_term Thm.eq_thm (prep thm) net handle Net.DELETE => net

val add = Thm.declaration_attribute (Data.map o ins)
val del = Thm.declaration_attribute (Data.map o del)

val name = Binding.name "z3_rule"

val description = "declaration of Z3 proof rules"

val _ = Theory.setup (Attrib.setup name (Attrib.add_del add del) description #>
  Global_Theory.add_thms_dynamic (name, Net.content o Data.get))

end;

(*  Title:      HOL/ex/MonoidGroup.thy
    Author:     Markus Wenzel
*)

section \<open>Monoids and Groups as predicates over record schemes\<close>

theory MonoidGroup imports MainRLT begin

record 'a monoid_sig =
  times :: "'a => 'a => 'a"
  one :: 'a

record 'a group_sig = "'a monoid_sig" +
  inv :: "'a => 'a"

definition
  monoid :: "(| times :: 'a => 'a => 'a, one :: 'a, ... :: 'b |) => bool" where
  "monoid M = (\<forall>x y z.
    times M (times M x y) z = times M x (times M y z) \<and>
    times M (one M) x = x \<and> times M x (one M) = x)"

definition
  group :: "(| times :: 'a => 'a => 'a, one :: 'a, inv :: 'a => 'a, ... :: 'b |) => bool" where
  "group G = (monoid G \<and> (\<forall>x. times G (inv G x) x = one G))"

definition
  reverse :: "(| times :: 'a => 'a => 'a, one :: 'a, ... :: 'b |) =>
    (| times :: 'a => 'a => 'a, one :: 'a, ... :: 'b |)" where
  "reverse M = M (| times := \<lambda>x y. times M y x |)"

end

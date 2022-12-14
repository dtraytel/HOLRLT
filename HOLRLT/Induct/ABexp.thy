(*  Title:      HOL/Induct/ABexp.thy
    Author:     Stefan Berghofer, TU Muenchen
*)

section \<open>Arithmetic and boolean expressions\<close>

theory ABexp
imports MainRLT
begin

datatype 'a aexp =
    IF "'a bexp"  "'a aexp"  "'a aexp"
  | Sum "'a aexp"  "'a aexp"
  | Diff "'a aexp"  "'a aexp"
  | Var 'a
  | Num nat
and 'a bexp =
    Less "'a aexp"  "'a aexp"
  | And "'a bexp"  "'a bexp"
  | Neg "'a bexp"


text \<open>\medskip Evaluation of arithmetic and boolean expressions\<close>

primrec evala :: "('a \<Rightarrow> nat) \<Rightarrow> 'a aexp \<Rightarrow> nat"
  and evalb :: "('a \<Rightarrow> nat) \<Rightarrow> 'a bexp \<Rightarrow> bool"
where
  "evala env (IF b a1 a2) = (if evalb env b then evala env a1 else evala env a2)"
| "evala env (Sum a1 a2) = evala env a1 + evala env a2"
| "evala env (Diff a1 a2) = evala env a1 - evala env a2"
| "evala env (Var v) = env v"
| "evala env (Num n) = n"

| "evalb env (Less a1 a2) = (evala env a1 < evala env a2)"
| "evalb env (And b1 b2) = (evalb env b1 \<and> evalb env b2)"
| "evalb env (Neg b) = (\<not> evalb env b)"


text \<open>\medskip Substitution on arithmetic and boolean expressions\<close>

primrec substa :: "('a \<Rightarrow> 'b aexp) \<Rightarrow> 'a aexp \<Rightarrow> 'b aexp"
  and substb :: "('a \<Rightarrow> 'b aexp) \<Rightarrow> 'a bexp \<Rightarrow> 'b bexp"
where
  "substa f (IF b a1 a2) = IF (substb f b) (substa f a1) (substa f a2)"
| "substa f (Sum a1 a2) = Sum (substa f a1) (substa f a2)"
| "substa f (Diff a1 a2) = Diff (substa f a1) (substa f a2)"
| "substa f (Var v) = f v"
| "substa f (Num n) = Num n"

| "substb f (Less a1 a2) = Less (substa f a1) (substa f a2)"
| "substb f (And b1 b2) = And (substb f b1) (substb f b2)"
| "substb f (Neg b) = Neg (substb f b)"

lemma subst1_aexp:
  "evala env (substa (Var (v := a')) a) = evala (env (v := evala env a')) a"
and subst1_bexp:
  "evalb env (substb (Var (v := a')) b) = evalb (env (v := evala env a')) b"
    \<comment> \<open>one variable\<close>
  by (induct a and b) simp_all

lemma subst_all_aexp:
  "evala env (substa s a) = evala (\<lambda>x. evala env (s x)) a"
and subst_all_bexp:
  "evalb env (substb s b) = evalb (\<lambda>x. evala env (s x)) b"
  by (induct a and b) auto

end

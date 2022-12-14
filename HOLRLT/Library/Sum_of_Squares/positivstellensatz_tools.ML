(*  Title:      HOL/Library/Sum_of_Squares/positivstellensatz_tools.ML
    Author:     Philipp Meyer, TU Muenchen

Functions for generating a certificate from a positivstellensatz and vice
versa.
*)

signature POSITIVSTELLENSATZ_TOOLS =
sig
  val print_cert: RealArith.pss_tree -> string
  val read_cert: Proof.context -> string -> RealArith.pss_tree
end

structure Positivstellensatz_Tools : POSITIVSTELLENSATZ_TOOLS =
struct

(** print certificate **)

local

(* map polynomials to strings *)

fun string_of_varpow x k =
  let
    val term = Thm.term_of x
    val name =
      (case term of
        Free (n, _) => n
      | _ => error "Term in monomial not free variable")
  in
    if k = 1 then name else name ^ "^" ^ string_of_int k
  end

fun string_of_monomial m =
  if FuncUtil.Ctermfunc.is_empty m then "1"
  else
    let
      val m' = FuncUtil.dest_monomial m
      val vps = fold_rev (fn (x,k) => cons (string_of_varpow x k)) m' []
    in foldr1 (fn (s, t) => s ^ "*" ^ t) vps end

fun string_of_cmonomial (m,c) =
  if FuncUtil.Ctermfunc.is_empty m then Rat.string_of_rat c
  else if c = @1 then string_of_monomial m
  else Rat.string_of_rat c ^ "*" ^ string_of_monomial m

fun string_of_poly p =
  if FuncUtil.Monomialfunc.is_empty p then "0"
  else
    let
      val cms = map string_of_cmonomial
        (sort (prod_ord FuncUtil.monomial_order (K EQUAL)) (FuncUtil.Monomialfunc.dest p))
    in foldr1 (fn (t1, t2) => t1 ^ " + " ^ t2) cms end


(* print cert *)

fun pss_to_cert (RealArith.Axiom_eq i) = "A=" ^ string_of_int i
  | pss_to_cert (RealArith.Axiom_le i) = "A<=" ^ string_of_int i
  | pss_to_cert (RealArith.Axiom_lt i) = "A<" ^ string_of_int i
  | pss_to_cert (RealArith.Rational_eq r) = "R=" ^ Rat.string_of_rat r
  | pss_to_cert (RealArith.Rational_le r) = "R<=" ^ Rat.string_of_rat r
  | pss_to_cert (RealArith.Rational_lt r) = "R<" ^ Rat.string_of_rat r
  | pss_to_cert (RealArith.Square p) = "[" ^ string_of_poly p ^ "]^2"
  | pss_to_cert (RealArith.Eqmul (p, pss)) =
      "([" ^ string_of_poly p ^ "] * " ^ pss_to_cert pss ^ ")"
  | pss_to_cert (RealArith.Sum (pss1, pss2)) =
      "(" ^ pss_to_cert pss1 ^ " + " ^ pss_to_cert pss2 ^ ")"
  | pss_to_cert (RealArith.Product (pss1, pss2)) =
      "(" ^ pss_to_cert pss1 ^ " * " ^ pss_to_cert pss2 ^ ")"

in

fun print_cert RealArith.Trivial = "()"
  | print_cert (RealArith.Cert pss) = "(" ^ pss_to_cert pss ^ ")"
  | print_cert (RealArith.Branch (t1, t2)) =
      "(" ^ print_cert t1 ^ " & " ^ print_cert t2 ^ ")"

end



(** read certificate **)

local

(* basic parsers *)

val str = Scan.this_string

val number =
  Scan.repeat1 (Scan.one Symbol.is_ascii_digit >> (fn s => ord s - ord "0"))
    >> foldl1 (fn (n, d) => n * 10 + d)

val nat = number
val int = Scan.optional (str "~" >> K ~1) 1 -- nat >> op *
val rat = int --| str "/" -- int >> Rat.make
val rat_int = rat || int >> Rat.of_int


(* polynomial parsers *)

fun repeat_sep s f = f ::: Scan.repeat (str s |-- f)

val parse_id = Scan.one Symbol.is_letter ::: Scan.many Symbol.is_letdig >> implode

fun parse_varpow ctxt = parse_id -- Scan.optional (str "^" |-- nat) 1 >>
  (fn (x, k) => (Thm.cterm_of ctxt (Free (x, \<^Type>\<open>real\<close>)), k))

fun parse_monomial ctxt = repeat_sep "*" (parse_varpow ctxt) >>
  (fn xs => fold FuncUtil.Ctermfunc.update xs FuncUtil.Ctermfunc.empty)

fun parse_cmonomial ctxt =
  rat_int --| str "*" -- (parse_monomial ctxt) >> swap ||
  (parse_monomial ctxt) >> (fn m => (m, @1)) ||
  rat_int >> (fn r => (FuncUtil.Ctermfunc.empty, r))

fun parse_poly ctxt = repeat_sep "+" (parse_cmonomial ctxt) >>
  (fn xs => fold FuncUtil.Monomialfunc.update xs FuncUtil.Monomialfunc.empty)


(* positivstellensatz parsers *)

val parse_axiom =
  (str "A=" |-- int >> RealArith.Axiom_eq) ||
  (str "A<=" |-- int >> RealArith.Axiom_le) ||
  (str "A<" |-- int >> RealArith.Axiom_lt)

val parse_rational =
  (str "R=" |-- rat_int >> RealArith.Rational_eq) ||
  (str "R<=" |-- rat_int >> RealArith.Rational_le) ||
  (str "R<" |-- rat_int >> RealArith.Rational_lt)

fun parse_cert ctxt input =
  let
    val pc = parse_cert ctxt
    val pp = parse_poly ctxt
  in
    (parse_axiom ||
     parse_rational ||
     str "[" |-- pp --| str "]^2" >> RealArith.Square ||
     str "([" |-- pp --| str "]*" -- pc --| str ")" >> RealArith.Eqmul ||
     str "(" |-- pc --| str "*" -- pc --| str ")" >> RealArith.Product ||
     str "(" |-- pc --| str "+" -- pc --| str ")" >> RealArith.Sum) input
  end

fun parse_cert_tree ctxt input =
  let
    val pc = parse_cert ctxt
    val pt = parse_cert_tree ctxt
  in
    (str "()" >> K RealArith.Trivial ||
     str "(" |-- pc --| str ")" >> RealArith.Cert ||
     str "(" |-- pt --| str "&" -- pt --| str ")" >> RealArith.Branch) input
  end

in

fun read_cert ctxt input_str =
  Symbol.scanner "Bad certificate" (parse_cert_tree ctxt)
    (filter_out Symbol.is_blank (Symbol.explode input_str))

end

end


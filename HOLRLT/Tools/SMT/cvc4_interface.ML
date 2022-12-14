(*  Title:      HOL/Tools/SMT/cvc4_interface.ML
    Author:     Jasmin Blanchette, TU Muenchen

Interface to CVC4 based on an extended version of SMT-LIB.
*)

signature CVC4_INTERFACE =
sig
  val smtlib_cvc4C: SMT_Util.class
  val hosmtlib_cvc4C: SMT_Util.class
end;

structure CVC4_Interface: CVC4_INTERFACE =
struct

val cvc4C = ["cvc4"]
val smtlib_cvc4C = SMTLIB_Interface.smtlibC @ cvc4C
val hosmtlib_cvc4C = SMTLIB_Interface.hosmtlibC @ cvc4C


(* interface *)

local
  fun translate_config order ctxt =
    {order = order,
     logic = K (K "(set-logic ALL_SUPPORTED)\n"),
     fp_kinds = [BNF_Util.Least_FP, BNF_Util.Greatest_FP],
     serialize = #serialize (SMTLIB_Interface.translate_config order ctxt)}
in

val _ = Theory.setup (Context.theory_map
  (SMT_Translate.add_config (smtlib_cvc4C, translate_config SMT_Util.First_Order) #>
   SMT_Translate.add_config (hosmtlib_cvc4C, translate_config SMT_Util.Higher_Order)))

end

end;

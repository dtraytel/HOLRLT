(*  Title:      HOL/Tools/ATP/atp_systems.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

Setup for supported ATPs.
*)

signature SLEDGEHAMMER_ATP_SYSTEMS =
sig
  type term_order = ATP_Problem.term_order
  type atp_format = ATP_Problem.atp_format
  type atp_formula_role = ATP_Problem.atp_formula_role
  type atp_failure = ATP_Proof.atp_failure

  type slice_spec = (int * string) * atp_format * string * string * bool
  type atp_config =
    {exec : string list * string list,
     arguments : Proof.context -> bool -> string -> Time.time -> Path.T ->
       term_order * (unit -> (string * int) list) * (unit -> (string * real) list) -> string list,
     proof_delims : (string * string) list,
     known_failures : (atp_failure * string) list,
     prem_role : atp_formula_role,
     best_slices : Proof.context -> (real * (slice_spec * string)) list,
     best_max_mono_iters : int,
     best_max_new_mono_instances : int}

  val default_max_mono_iters : int
  val default_max_new_mono_instances : int
  val force_sos : bool Config.T
  val term_order : string Config.T
  val e_smartN : string
  val e_autoN : string
  val e_fun_weightN : string
  val e_sym_offset_weightN : string
  val e_selection_heuristic : string Config.T
  val e_default_fun_weight : real Config.T
  val e_fun_weight_base : real Config.T
  val e_fun_weight_span : real Config.T
  val e_default_sym_offs_weight : real Config.T
  val e_sym_offs_weight_base : real Config.T
  val e_sym_offs_weight_span : real Config.T
  val spass_H1SOS : string
  val spass_H2 : string
  val spass_H2LR0LT0 : string
  val spass_H2NuVS0 : string
  val spass_H2NuVS0Red2 : string
  val spass_H2SOS : string
  val isabelle_scala_function: string list * string list
  val remote_atp : string -> string -> string list -> (string * string) list ->
    (atp_failure * string) list -> atp_formula_role -> (Proof.context -> slice_spec * string) ->
    string * (unit -> atp_config)
  val add_atp : string * (unit -> atp_config) -> theory -> theory
  val get_atp : theory -> string -> (unit -> atp_config)
  val supported_atps : theory -> string list
  val is_atp_installed : theory -> string -> bool
  val refresh_systems_on_tptp : unit -> unit
  val effective_term_order : Proof.context -> string -> term_order
end;

structure Sledgehammer_ATP_Systems : SLEDGEHAMMER_ATP_SYSTEMS =
struct

open ATP_Problem
open ATP_Proof
open ATP_Problem_Generate


(* ATP configuration *)

val default_max_mono_iters = 3 (* FUDGE *)
val default_max_new_mono_instances = 100 (* FUDGE *)

type slice_spec = (int * string) * atp_format * string * string * bool

type atp_config =
  {exec : string list * string list,
   arguments : Proof.context -> bool -> string -> Time.time -> Path.T ->
     term_order * (unit -> (string * int) list) * (unit -> (string * real) list) -> string list,
   proof_delims : (string * string) list,
   known_failures : (atp_failure * string) list,
   prem_role : atp_formula_role,
   best_slices : Proof.context -> (real * (slice_spec * string)) list,
   best_max_mono_iters : int,
   best_max_new_mono_instances : int}

(* "best_slices" must be found empirically, taking a holistic approach since the
   ATPs are run in parallel. Each slice has the format

     (time_frac, ((max_facts, fact_filter), format, type_enc,
                  lam_trans, uncurried_aliases), extra)

   where

     time_frac = faction of the time available given to the slice (which should
       add up to 1.0)

     extra = extra information to the prover (e.g., SOS or no SOS).

   The last slice should be the most "normal" one, because it will get all the
   time available if the other slices fail early and also because it is used if
   slicing is disabled (e.g., by the minimizer). *)

val mepoN = "mepo"
val mashN = "mash"
val meshN = "mesh"

val tstp_proof_delims =
  [("% SZS output start CNFRefutation", "% SZS output end CNFRefutation"),
   ("% SZS output start Refutation", "% SZS output end Refutation"),
   ("% SZS output start Proof", "% SZS output end Proof")]

fun known_szs_failures wrap =
  [(Unprovable, wrap "CounterSatisfiable"),
   (Unprovable, wrap "Satisfiable"),
   (GaveUp, wrap "GaveUp"),
   (GaveUp, wrap "Unknown"),
   (GaveUp, wrap "Incomplete"),
   (ProofMissing, wrap "Theorem"),
   (ProofMissing, wrap "Unsatisfiable"),
   (TimedOut, wrap "Timeout"),
   (Inappropriate, wrap "Inappropriate"),
   (OutOfResources, wrap "ResourceOut"),
   (OutOfResources, wrap "MemoryOut"),
   (Interrupted, wrap "Forced"),
   (Interrupted, wrap "User")]

val known_szs_status_failures = known_szs_failures (prefix "SZS status ")
val known_says_failures = known_szs_failures (prefix " says ")

structure Data = Theory_Data
(
  type T = ((unit -> atp_config) * stamp) Symtab.table
  val empty = Symtab.empty
  fun merge data : T =
    Symtab.merge (eq_snd (op =)) data
    handle Symtab.DUP name => error ("Duplicate ATP: " ^ quote name)
)

fun to_secs min time = Int.max (min, (Time.toMilliseconds time + 999) div 1000)

fun normalize_weights xs =
  let val total_weight = real (fold (curry op + o fst) xs 0) in
    map (apfst (fn weight => real weight / total_weight)) xs
  end

val sosN = "sos"
val no_sosN = "no_sos"

val force_sos = Attrib.setup_config_bool \<^binding>\<open>atp_force_sos\<close> (K false)

val smartN = "smart"
(* val kboN = "kbo" *)
val lpoN = "lpo"
val xweightsN = "_weights"
val xprecN = "_prec"
val xsimpN = "_simp" (* SPASS-specific *)

(* Possible values for "atp_term_order":
   "smart", "(kbo|lpo)(_weights)?(_prec|_simp)?" *)
val term_order =
  Attrib.setup_config_string \<^binding>\<open>atp_term_order\<close> (K smartN)


(* agsyHOL *)

val agsyhol_config : atp_config =
  {exec = (["AGSYHOL_HOME"], ["agsyHOL"]),
   arguments = fn _ => fn _ => fn _ => fn timeout => fn problem => fn _ =>
     ["--proof --time-out " ^ string_of_int (to_secs 1 timeout) ^ " " ^ File.bash_path problem],
   proof_delims = tstp_proof_delims,
   known_failures = known_szs_status_failures,
   prem_role = Hypothesis,
   best_slices =
     (* FUDGE *)
     K [(1.0, (((60, ""), THF (Without_FOOL, Monomorphic, THF_Without_Choice), "mono_native_higher", keep_lamsN, false), ""))],
   best_max_mono_iters = default_max_mono_iters - 1 (* FUDGE *),
   best_max_new_mono_instances = default_max_new_mono_instances}

val agsyhol = (agsyholN, fn () => agsyhol_config)


(* Alt-Ergo *)

val alt_ergo_config : atp_config =
  {exec = (["WHY3_HOME"], ["why3"]),
   arguments = fn _ => fn _ => fn _ => fn timeout => fn problem => fn _ =>
     ["--format tptp --prover 'Alt-Ergo,0.95.2,' --timelimit " ^ string_of_int (to_secs 1 timeout) ^
      " " ^ File.bash_path problem],
   proof_delims = [],
   known_failures =
     [(ProofMissing, ": Valid"),
      (TimedOut, ": Timeout"),
      (GaveUp, ": Unknown")],
   prem_role = Hypothesis,
   best_slices = fn _ =>
     (* FUDGE *)
     [(1.0, (((100, ""), TFF (Without_FOOL, Polymorphic), "poly_native", liftingN, false), ""))],
   best_max_mono_iters = default_max_mono_iters,
   best_max_new_mono_instances = default_max_new_mono_instances}

val alt_ergo = (alt_ergoN, fn () => alt_ergo_config)


(* E *)

val e_smartN = "smart"
val e_autoN = "auto"
val e_fun_weightN = "fun_weight"
val e_sym_offset_weightN = "sym_offset_weight"

val e_selection_heuristic =
  Attrib.setup_config_string \<^binding>\<open>atp_e_selection_heuristic\<close> (K e_smartN)
(* FUDGE *)
val e_default_fun_weight =
  Attrib.setup_config_real \<^binding>\<open>atp_e_default_fun_weight\<close> (K 20.0)
val e_fun_weight_base =
  Attrib.setup_config_real \<^binding>\<open>atp_e_fun_weight_base\<close> (K 0.0)
val e_fun_weight_span =
  Attrib.setup_config_real \<^binding>\<open>atp_e_fun_weight_span\<close> (K 40.0)
val e_default_sym_offs_weight =
  Attrib.setup_config_real \<^binding>\<open>atp_e_default_sym_offs_weight\<close> (K 1.0)
val e_sym_offs_weight_base =
  Attrib.setup_config_real \<^binding>\<open>atp_e_sym_offs_weight_base\<close> (K ~20.0)
val e_sym_offs_weight_span =
  Attrib.setup_config_real \<^binding>\<open>atp_e_sym_offs_weight_span\<close> (K 60.0)

fun e_selection_heuristic_case heuristic fw sow =
  if heuristic = e_fun_weightN then fw
  else if heuristic = e_sym_offset_weightN then sow
  else raise Fail ("unexpected " ^ quote heuristic)

fun scaled_e_selection_weight ctxt heuristic w =
  w * Config.get ctxt (e_selection_heuristic_case heuristic
                           e_fun_weight_span e_sym_offs_weight_span)
  + Config.get ctxt (e_selection_heuristic_case heuristic
                         e_fun_weight_base e_sym_offs_weight_base)
  |> Real.ceil |> signed_string_of_int

fun e_selection_weight_arguments ctxt heuristic sel_weights =
  if heuristic = e_fun_weightN orelse heuristic = e_sym_offset_weightN then
    (* supplied by Stephan Schulz *)
    "--split-clauses=4 --split-reuse-defs --simul-paramod --forward-context-sr \
    \--destructive-er-aggressive --destructive-er --presat-simplify \
    \--prefer-initial-clauses -winvfreqrank -c1 -Ginvfreqconjmax -F1 \
    \--delete-bad-limit=150000000 -WSelectMaxLComplexAvoidPosPred -H'(4*" ^
    e_selection_heuristic_case heuristic "FunWeight" "SymOffsetWeight" ^
    "(SimulateSOS," ^
    (e_selection_heuristic_case heuristic
         e_default_fun_weight e_default_sym_offs_weight
     |> Config.get ctxt |> Real.ceil |> signed_string_of_int) ^
    ",20,1.5,1.5,1" ^
    (sel_weights ()
     |> map (fn (s, w) => "," ^ s ^ ":" ^
                          scaled_e_selection_weight ctxt heuristic w)
     |> implode) ^
    "),3*ConjectureGeneralSymbolWeight(PreferNonGoals,200,100,200,50,50,1,100,\
    \1.5,1.5,1),1*Clauseweight(PreferProcessed,1,1,1),1*\
    \FIFOWeight(PreferProcessed))' "
  else
    "-xAuto "

val e_ord_weights = map (fn (s, w) => s ^ ":" ^ string_of_int w) #> space_implode ","
fun e_ord_precedence [_] = ""
  | e_ord_precedence info = info |> map fst |> space_implode "<"

fun e_term_order_info_arguments false false _ = ""
  | e_term_order_info_arguments gen_weights gen_prec ord_info =
    let val ord_info = ord_info () in
      (if gen_weights then "--order-weights='" ^ e_ord_weights ord_info ^ "' " else "") ^
      (if gen_prec then "--precedence='" ^ e_ord_precedence ord_info ^ "' " else "")
    end

val e_config : atp_config =
  {exec = (["E_HOME"], ["eprover-ho", "eprover"]),
   arguments = fn ctxt => fn _ => fn heuristic => fn timeout => fn problem =>
     fn ({is_lpo, gen_weights, gen_prec, ...}, ord_info, sel_weights) =>
       ["--auto-schedule --tstp-in --tstp-out --silent " ^
        e_selection_weight_arguments ctxt heuristic sel_weights ^
        e_term_order_info_arguments gen_weights gen_prec ord_info ^
        "--term-ordering=" ^ (if is_lpo then "LPO4" else "KBO6") ^ " " ^
        "--cpu-limit=" ^ string_of_int (to_secs 2 timeout) ^
        " --proof-object=1 " ^
        File.bash_path problem],
   proof_delims =
     [("# SZS output start CNFRefutation", "# SZS output end CNFRefutation")] @
     tstp_proof_delims,
   known_failures =
     [(TimedOut, "Failure: Resource limit exceeded (time)"),
      (TimedOut, "time limit exceeded")] @
     known_szs_status_failures,
   prem_role = Conjecture,
   best_slices = fn ctxt =>
     let
       val heuristic = Config.get ctxt e_selection_heuristic
       val (format, enc, main_lam_trans) =
         if string_ord (getenv "E_VERSION", "2.7") <> LESS then
           (THF (With_FOOL, Monomorphic, THF_Without_Choice), "mono_native_higher_fool", keep_lamsN)
         else if string_ord (getenv "E_VERSION", "2.6") <> LESS then
           (THF (Without_FOOL, Monomorphic, THF_Without_Choice), "mono_native_higher", keep_lamsN)
         else
           (THF (Without_FOOL, Monomorphic, THF_Lambda_Free), "mono_native_higher", combsN)
     in
       (* FUDGE *)
       if heuristic = e_smartN then
         [(0.15, (((128, meshN), format, enc, main_lam_trans, false), e_fun_weightN)),
          (0.15, (((128, mashN), format, enc, main_lam_trans, false), e_sym_offset_weightN)),
          (0.15, (((91, mepoN), format, enc, main_lam_trans, false), e_autoN)),
          (0.15, (((1000, meshN), format, "poly_guards??", main_lam_trans, false), e_sym_offset_weightN)),
          (0.15, (((256, mepoN), format, enc, liftingN, false), e_fun_weightN)),
          (0.25, (((64, mashN), format, enc, combsN, false), e_fun_weightN))]
       else
         [(1.0, (((500, ""), format, enc, combsN, false), heuristic))]
     end,
   best_max_mono_iters = default_max_mono_iters,
   best_max_new_mono_instances = default_max_new_mono_instances}

val e = (eN, fn () => e_config)


(* iProver *)

val iprover_config : atp_config =
  {exec = (["IPROVER_HOME"], ["iproveropt", "iprover"]),
   arguments = fn _ => fn _ => fn _ => fn timeout => fn problem => fn _ =>
     ["--clausifier \"$VAMPIRE_HOME\"/vampire " ^
      "--clausifier_options \"--mode clausify\" " ^
      "--time_out_real " ^ string_of_real (Time.toReal timeout) ^ " " ^ File.bash_path problem],
   proof_delims = tstp_proof_delims,
   known_failures =
     [(ProofIncomplete, "% SZS output start CNFRefutation")] @
     known_szs_status_failures,
   prem_role = Hypothesis,
   best_slices =
     (* FUDGE *)
     K [(1.0, (((150, ""), FOF, "mono_guards??", liftingN, false), ""))],
   best_max_mono_iters = default_max_mono_iters,
   best_max_new_mono_instances = default_max_new_mono_instances}

val iprover = (iproverN, fn () => iprover_config)


(* LEO-II *)

val leo2_config : atp_config =
  {exec = (["LEO2_HOME"], ["leo.opt", "leo"]),
   arguments = fn _ => fn full_proofs => fn _ => fn timeout => fn problem => fn _ =>
     ["--foatp e --atp e=\"$E_HOME\"/eprover \
      \--atp epclextract=\"$E_HOME\"/epclextract \
      \--proofoutput 1 --timeout " ^ string_of_int (to_secs 1 timeout) ^ " " ^
      (if full_proofs then "--notReplLeibnizEQ --notReplAndrewsEQ --notUseExtCnfCmbd " else "") ^
      File.bash_path problem],
   proof_delims = tstp_proof_delims,
   known_failures =
     [(TimedOut, "CPU time limit exceeded, terminating"),
      (GaveUp, "No.of.Axioms")] @
     known_szs_status_failures,
   prem_role = Hypothesis,
   best_slices =
     (* FUDGE *)
     K [(1.0, (((40, ""), THF (Without_FOOL, Monomorphic, THF_Without_Choice), "mono_native_higher", keep_lamsN, false), ""))],
   best_max_mono_iters = default_max_mono_iters - 1 (* FUDGE *),
   best_max_new_mono_instances = default_max_new_mono_instances}

val leo2 = (leo2N, fn () => leo2_config)


(* Leo-III *)

(* Include choice? Disabled now since it's disabled for Satallax as well. *)
val leo3_config : atp_config =
  {exec = (["LEO3_HOME"], ["leo3"]),
   arguments = fn _ => fn full_proofs => fn _ => fn timeout => fn problem => fn _ =>
     [File.bash_path problem ^ " " ^ "--atp cvc=\"$CVC4_SOLVER\" --atp e=\"$E_HOME\"/eprover \
      \-p -t " ^ string_of_int (to_secs 1 timeout) ^ " " ^
      (if full_proofs then "--nleq --naeq " else "")],
   proof_delims = tstp_proof_delims,
   known_failures = known_szs_status_failures,
   prem_role = Hypothesis,
   best_slices =
     (* FUDGE *)
     K [(1.0, (((150, ""), THF (Without_FOOL, Polymorphic, THF_Without_Choice), "mono_native_higher", keep_lamsN, false), ""))],
   best_max_mono_iters = default_max_mono_iters - 1 (* FUDGE *),
   best_max_new_mono_instances = default_max_new_mono_instances}

val leo3 = (leo3N, fn () => leo3_config)


(* Satallax *)

(* Choice is disabled until there is proper reconstruction for it. *)
val satallax_config : atp_config =
  {exec = (["SATALLAX_HOME"], ["satallax.opt", "satallax"]),
   arguments = fn _ => fn _ => fn _ => fn timeout => fn problem => fn _ =>
     [(case getenv "E_HOME" of
        "" => ""
      | home => "-E " ^ home ^ "/eprover ") ^
      "-p tstp -t " ^ string_of_int (to_secs 1 timeout) ^ " " ^ File.bash_path problem],
   proof_delims =
     [("% SZS output start Proof", "% SZS output end Proof")],
   known_failures = known_szs_status_failures,
   prem_role = Hypothesis,
   best_slices =
     (* FUDGE *)
     K [(1.0, (((150, ""), THF (Without_FOOL, Monomorphic, THF_Without_Choice), "mono_native_higher", keep_lamsN, false), ""))],
   best_max_mono_iters = default_max_mono_iters - 1 (* FUDGE *),
   best_max_new_mono_instances = default_max_new_mono_instances}

val satallax = (satallaxN, fn () => satallax_config)


(* SPASS *)

val spass_H1SOS = "-Heuristic=1 -SOS"
val spass_H2 = "-Heuristic=2"
val spass_H2LR0LT0 = "-Heuristic=2 -LR=0 -LT=0"
val spass_H2NuVS0 = "-Heuristic=2 -RNuV=1 -Sorts=0"
val spass_H2NuVS0Red2 = "-Heuristic=2 -RNuV=1 -Sorts=0 -RFRew=2 -RBRew=2 -RTaut=2"
val spass_H2SOS = "-Heuristic=2 -SOS"

val spass_config : atp_config =
  let
    val format = DFG Monomorphic
  in
    {exec = (["SPASS_HOME"], ["SPASS"]),
     arguments = fn _ => fn full_proofs => fn extra_options => fn timeout => fn problem => fn _ =>
       ["-Isabelle=1 " ^ (if full_proofs then "-CNFRenaming=0 -Splits=0 " else "") ^
        "-TimeLimit=" ^ string_of_int (to_secs 1 timeout) ^ " " ^ File.bash_path problem
        |> extra_options <> "" ? prefix (extra_options ^ " ")],
     proof_delims = [("Here is a proof", "Formulae used in the proof")],
     known_failures =
       [(GaveUp, "SPASS beiseite: Completion found"),
        (TimedOut, "SPASS beiseite: Ran out of time"),
        (OutOfResources, "SPASS beiseite: Maximal number of loops exceeded"),
        (MalformedInput, "Undefined symbol"),
        (MalformedInput, "Free Variable"),
        (Unprovable, "No formulae and clauses found in input file"),
        (InternalError, "Please report this error")],
     prem_role = Conjecture,
     best_slices = fn _ =>
       (* FUDGE *)
       [(0.1667, (((150, meshN), format, "mono_native", combsN, true), "")),
        (0.1667, (((500, meshN), format, "mono_native", liftingN, true), spass_H2SOS)),
        (0.1666, (((50, meshN), format,  "mono_native", liftingN, true), spass_H2LR0LT0)),
        (0.1000, (((250, meshN), format, "mono_native", combsN, true), spass_H2NuVS0)),
        (0.1000, (((1000, mepoN), format, "mono_native", liftingN, true), spass_H1SOS)),
        (0.1000, (((150, meshN), format, "poly_guards??", liftingN, false), spass_H2NuVS0Red2)),
        (0.1000, (((300, meshN), format, "mono_native", combsN, true), spass_H2SOS)),
        (0.1000, (((100, meshN), format, "mono_native", combs_and_liftingN, true), spass_H2))],
     best_max_mono_iters = default_max_mono_iters,
     best_max_new_mono_instances = default_max_new_mono_instances}
  end

val spass = (spassN, fn () => spass_config)


(* Vampire *)

val vampire_basic_options =
  "--proof tptp --output_axiom_names on" ^
  (if ML_System.platform_is_windows
   then ""  (*time slicing is not support in the Windows version of Vampire*)
   else " --mode casc")

val vampire_full_proof_options =
  " --proof_extra free --forced_options avatar=off:equality_proxy=off:general_splitting=off:inequality_splitting=0:naming=0"

val vampire_config : atp_config =
  let
    val format = TFF (With_FOOL, Polymorphic)
  in
    {exec = (["VAMPIRE_HOME"], ["vampire"]),
     arguments = fn _ => fn full_proofs => fn sos => fn timeout => fn problem => fn _ =>
       [vampire_basic_options ^ (if full_proofs then " " ^ vampire_full_proof_options else "") ^
         " -t " ^ string_of_int (to_secs 1 timeout) ^ " --input_file " ^ File.bash_path problem
         |> sos = sosN ? prefix "--sos on "],
     proof_delims =
       [("=========== Refutation ==========",
         "======= End of refutation =======")] @
       tstp_proof_delims,
     known_failures =
       [(GaveUp, "UNPROVABLE"),
        (GaveUp, "CANNOT PROVE"),
        (Unprovable, "Satisfiability detected"),
        (Unprovable, "Termination reason: Satisfiable"),
        (Interrupted, "Aborted by signal SIGINT")] @
       known_szs_status_failures,
     prem_role = Hypothesis,
     best_slices = fn ctxt =>
       (* FUDGE *)
       [(0.333, (((500, meshN), format, "mono_native_fool", combs_or_liftingN, false), sosN)),
        (0.333, (((150, meshN), format, "poly_native_fool", combs_or_liftingN, false), sosN)),
        (0.334, (((50, meshN), format, "mono_native_fool", combs_or_liftingN, false), no_sosN))]
       |> Config.get ctxt force_sos ? (hd #> apfst (K 1.0) #> single),
     best_max_mono_iters = default_max_mono_iters,
     best_max_new_mono_instances = 2 * default_max_new_mono_instances (* FUDGE *)}
  end

val vampire = (vampireN, fn () => vampire_config)


(* Z3 with TPTP syntax (half experimental, half legacy) *)

val z3_tptp_config : atp_config =
  let
    val format = TFF (Without_FOOL, Monomorphic)
  in
    {exec = (["Z3_TPTP_HOME"], ["z3_tptp"]),
     arguments = fn _ => fn _ => fn _ => fn timeout => fn problem => fn _ =>
       ["-proof -t:" ^ string_of_int (to_secs 1 timeout) ^ " -file:" ^ File.bash_path problem],
     proof_delims = [("SZS status Theorem", "")],
     known_failures = known_szs_status_failures,
     prem_role = Hypothesis,
     best_slices =
       (* FUDGE *)
       K [(0.5, (((250, meshN), format, "mono_native", combsN, false), "")),
          (0.25, (((125, mepoN), format, "mono_native", combsN, false), "")),
          (0.125, (((62, mashN), format, "mono_native", combsN, false), "")),
          (0.125, (((31, meshN), format, "mono_native", combsN, false), ""))],
     best_max_mono_iters = default_max_mono_iters,
     best_max_new_mono_instances = 2 * default_max_new_mono_instances (* FUDGE *)}
  end

val z3_tptp = (z3_tptpN, fn () => z3_tptp_config)


(* Zipperposition *)

val zipperposition_config : atp_config =
  let
    val format = THF (Without_FOOL, Polymorphic, THF_Without_Choice)
    val enc = ((512, "meshN"), format, "mono_native_higher", keep_lamsN, false)
  in
    {exec = (["ZIPPERPOSITION_HOME"], ["zipperposition"]),
     arguments = fn _ => fn _ => fn extra_options => fn timeout => fn problem => fn _ =>
       ["--input tptp", "--output tptp", "--timeout " ^ Time.toString timeout, extra_options,
        File.bash_path problem],
     proof_delims = tstp_proof_delims,
     known_failures =
       [(TimedOut, "SZS status ResourceOut")] @   (* odd way of timing out *)
       known_szs_status_failures,
     prem_role = Hypothesis,
     best_slices = fn _ =>
       [(1, (enc, "--mode=ho-pragmatic --tptp-def-as-rewrite --rewrite-before-cnf=true --max-inferences=1 --ho-unif-max-depth=1 --ho-max-elims=0 --ho-max-app-projections=0 --ho-max-rigid-imitations=1 --ho-max-identifications=0 --boolean-reasoning=bool-hoist --bool-hoist-simpl=true --bool-select=LI --recognize-injectivity=true --ext-rules=ext-family --ext-rules-max-depth=1 --ho-choice-inst=true --ho-prim-enum=none --ho-elim-leibniz=0 --interpret-bool-funs=true --try-e=\"$E_HOME/eprover\" --tmp-dir=\"$ISABELLE_TMP_PREFIX\" --ho-unif-level=pragmatic-framework --select=bb+e-selection2 --post-cnf-lambda-lifting=true -q \"4|prefer-sos|pnrefined(2,1,1,1,2,2,2)\" -q \"6|prefer-processed|conjecture-relative-struct(1.5,3.5,2,3)\" -q \"1|const|fifo\" -q \"4|prefer-ground|orient-lmax(2,1,2,1,1)\" -q \"4|defer-sos|conjecture-relative-struct(1,5,2,3)\" --avatar=off --recognize-injectivity=true --ho-neg-ext=true --e-timeout=2 --ho-pattern-decider=true --ho-fixpoint-decider=true --e-max-derived=50 --ignore-orphans=true --e-auto=true --presaturate=true --e-call-point=0.1")),
        (1, (enc, "--mode=ho-pragmatic --tptp-def-as-rewrite --rewrite-before-cnf=true --mode=ho-competitive --boolean-reasoning=simpl-only --ext-rules=ext-family --ext-rules-max-depth=1 --ho-prim-enum=none --avatar=off --recognize-injectivity=true --ho-elim-leibniz=1 --ho-unif-level=pragmatic-framework --no-max-vars --max-inferences=2 --ho-unif-max-depth=1 -q \"6|prefer-sos|pnrefined(1,1,1,2,2,2,0.5)\" -q \"6|const|conjecture-relative-var(1.02,l,f)\" -q \"1|prefer-processed|fifo\" -q \"1|prefer-non-goals|conjecture-relative-var(1,l,f)\" -q \"4|prefer-easy-ho|conjecture-relative-var(1.01,s,f)\" --select=e-selection16 --ho-choice-inst=true --try-e=\"$E_HOME/eprover\" --tmp-dir=\"$ISABELLE_TMP_PREFIX\" --e-timeout=3 --e-auto=true --sine=50 --sine-tolerance=1.0 --sine-depth-max=3 --sine-depth-min=1 --sine-trim-implications=true --ho-unif-level=pragmatic-framework --e-encode-lambdas=lift --scan-clause-ac=false --kbo-weight-fun=lambda-def-invfreqrank --e-call-point=0.1")),
        (1, (enc, "-nc --tptp-def-as-rewrite --rewrite-before-cnf=true --mode=ho-competitive --boolean-reasoning=simpl-only --ext-rules=off --ho-prim-enum=full --ho-prim-max=1 --avatar=off --recognize-injectivity=true --ho-elim-leibniz=4 --ho-unif-level=full-framework --no-max-vars -q \"2|prefer-goals|conjecture-relative-e(0.5,1,100,100,100,100,1.5,1.5,1)\" -q \"4|const|conjecture-relative-e(0.1,1,100,100,100,100,1.5,1.5,1.5)\" -q \"1|prefer-processed|fifo\" -q \"1|prefer-non-goals|conjecture-relative-e(0.5,1,100,100,100,100,1.5,1.5,1.5)\" -q \"4|prefer-sos|pnrefined(1,1,1,1,2,1.5,2)\" --select=ho-selection5 --ho-choice-inst=true --try-e=\"$E_HOME/eprover\" --tmp-dir=\"$ISABELLE_TMP_PREFIX\" --e-timeout=5 --e-call-point=0.25 --e-auto=true --sine=50 --sine-tolerance=2 --sine-depth-max=4 --sine-depth-min=1 --e-max-derived=96 --e-encode-lambdas=lift --scan-clause-ac=false --kbo-weight-fun=arity0 --prec-gen-fun=invfreq_conj")),
        (1, (enc, "--mode=ho-pragmatic -nc --tptp-def-as-rewrite --rewrite-before-cnf=true --mode=ho-competitive --boolean-reasoning=simpl-only --ext-rules=ext-family --ext-rules-max-depth=1 --ho-prim-enum=none --avatar=off --recognize-injectivity=true --ho-elim-leibniz=1 --ho-unif-level=pragmatic-framework --no-max-vars --max-inferences=4 --ho-max-app-projections=1 --ho-max-elims=0 --ho-max-rigid-imitations=2 --ho-max-identifications=0 --ho-unif-max-depth=3 -q \"6|prefer-sos|pnrefined(1,1,1,2,2,2,0.5)\" -q \"6|const|conjecture-relative-var(1.02,l,f)\" -q \"1|prefer-processed|fifo\" -q \"1|prefer-non-goals|conjecture-relative-var(1,l,f)\" -q \"4|prefer-easy-ho|conjecture-relative-var(1.01,s,f)\" --select=e-selection7 --ho-choice-inst=true --try-e=\"$E_HOME/eprover\" --tmp-dir=\"$ISABELLE_TMP_PREFIX\" --e-timeout=7 --sine=50 --sine-tolerance=1 --sine-depth-max=2 --sine-depth-min=1 --e-max-derived=64 --sine-ignore-k-most-common-syms=2 --sine-trim-implications=true --e-encode-lambdas=lift --scan-clause-ac=false --lambdasup=0 --kbo-weight-fun=lambda-def-invfreqrank --demod-in-var-args=true --bool-demod=true --lambda-demod=true --e-call-point=0.1")),
        (1, (enc, "--mode=ho-comb-complete --boolean-reasoning=simpl-only --ext-rules=off --kbo-weight-fun=lambda-def-sqarity --ho-prim-enum=none --tptp-def-as-rewrite -q \"4|prefer-sos|orient-lmax(2,1,2,1,1)\" -q \"4|defer-sos|conjecture-relative-var(1,s,f)\" -q \"3|const|default\" -q \"1|prefer-processed|fifo\" --ho-elim-leibniz=1 --select=NoSelection --solve-formulas=true --lazy-cnf=true --lazy-cnf-kind=simp --lazy-cnf-renaming-threshold=8 --sine=60 --sine-tolerance=2 --sine-depth-max=5 --sine-depth-min=1 --try-e=\"$E_HOME/eprover\" --tmp-dir=\"$ISABELLE_TMP_PREFIX\" --e-timeout=3 --e-auto=true --e-max-derived=50 --e-encode-lambdas=ignore --scan-clause-ac=false --presaturate=true --comb-b-penalty=3 --comb-c-penalty=3 --comb-k-penalty=1 --comb-s-penalty=5 --subvarsup=false --e-call-point=0.15")),
        (1, (enc, "--mode=ho-pragmatic --boolean-reasoning=simpl-only --ho-unif-max-depth=0 --ho-prim-enum=none -q \"2|prefer-ho-steps|conjecture-relative-e(0.1,0.5,100,100,100,100,1.5,1.5,1.5)\" -q \"1|prefer-sos|pnrefined(1,1,1,2,2,2,0.5)\" -q \"2|prefer-ground|default\" -q \"2|prefer-empty-trail|conjecture-relative-e(0.1,0.5,100,100,100,100,1.5,1.5,1.5)\" -q \"1|prefer-processed|fifo\" --select=bb+e-selection7 --ho-pattern-decider=false --ho-fixpoint-decider=true --ho-solid-decider=false --sine=150 --sine-tolerance=2 --sine-depth-max=3 --sine-depth-min=1 --prec-gen-fun=invfreqhack --lazy-cnf=true --lazy-cnf-kind=simp --lazy-cnf-renaming-threshold=2 --fluid-log-hoist=false --tptp-def-as-rewrite --rewrite-before-cnf=true --ho-prim-enum=eq --ho-prim-enum-add-var=true --ho-prim-max=1 --ho-prim-enum-early-bird=true -o tptp --avatar=eager --split-only-ground=true"))]
       |> normalize_weights,
     best_max_mono_iters = default_max_mono_iters,
     best_max_new_mono_instances = default_max_new_mono_instances}
  end

val zipperposition = (zipperpositionN, fn () => zipperposition_config)


(* Remote ATP invocation via SystemOnTPTP *)

val no_remote_systems = {url = "", systems = [] : string list}
val remote_systems = Synchronized.var "atp_remote_systems" no_remote_systems

fun get_remote_systems () =
  Timeout.apply (seconds 10.0) SystemOnTPTP.list_systems ()
    handle ERROR msg => (warning msg; no_remote_systems)
      | Timeout.TIMEOUT _ => no_remote_systems

fun find_remote_system name [] systems =
    find_first (String.isPrefix (name ^ "---")) systems
  | find_remote_system name (version :: versions) systems =
    case find_first (String.isPrefix (name ^ "---" ^ version)) systems of
      NONE => find_remote_system name versions systems
    | res => res

fun get_remote_system name versions =
  Synchronized.change_result remote_systems (fn remote =>
    (if #url remote <> SystemOnTPTP.get_url () orelse null (#systems remote)
      then get_remote_systems () else remote) |> ` #systems)
  |> `(find_remote_system name versions)

fun the_remote_system name versions =
  (case get_remote_system name versions of
    (SOME sys, _) => sys
  | (NONE, []) => error "SystemOnTPTP is currently not available"
  | (NONE, syss) =>
    (case syss |> filter_out (String.isPrefix "%") |> filter_out (curry (op =) "") of
      [] => error "SystemOnTPTP is currently not available"
    | [msg] => error ("SystemOnTPTP is currently not available: " ^ msg)
    | syss =>
      error ("System " ^ quote name ^ " is not available at SystemOnTPTP.\n(Available systems: " ^
        commas_quote syss ^ ".)")))

val max_remote_secs = 1000   (* give Geoff Sutcliffe's servers a break *)

val isabelle_scala_function = (["SCALA_HOME"], ["bin/scala"])

fun remote_config system_name system_versions proof_delims known_failures prem_role best_slice =
  {exec = isabelle_scala_function,
   arguments = fn _ => fn _ => fn command => fn timeout => fn problem => fn _ =>
     [the_remote_system system_name system_versions,
      Isabelle_System.absolute_path problem,
      command, string_of_int (Int.min (max_remote_secs, to_secs 1 timeout) * 1000)],
   proof_delims = union (op =) tstp_proof_delims proof_delims,
   known_failures = known_failures @ known_says_failures,
   prem_role = prem_role,
   best_slices = fn ctxt => [(1.0, best_slice ctxt)],
   best_max_mono_iters = default_max_mono_iters,
   best_max_new_mono_instances = default_max_new_mono_instances} : atp_config

fun remotify_config system_name system_versions best_slice
    ({proof_delims, known_failures, prem_role, ...} : atp_config) =
  remote_config system_name system_versions proof_delims known_failures prem_role best_slice

fun remote_atp name system_name system_versions proof_delims known_failures prem_role best_slice =
  (remote_prefix ^ name, fn () =>
     remote_config system_name system_versions proof_delims known_failures prem_role best_slice)
fun remotify_atp (name, config) system_name system_versions best_slice =
  (remote_prefix ^ name, remotify_config system_name system_versions best_slice o config)

fun gen_remote_waldmeister name type_enc =
  remote_atp name "Waldmeister" ["710"] tstp_proof_delims
    ([(OutOfResources, "Too many function symbols"),
      (Inappropriate, "****  Unexpected end of file."),
      (Crashed, "Unrecoverable Segmentation Fault")]
     @ known_szs_status_failures)
    Hypothesis
    (K (((50, ""), CNF_UEQ, type_enc, combsN, false), "") (* FUDGE *))

val remote_agsyhol =
  remotify_atp agsyhol "agsyHOL" ["1.0", "1"]
    (K (((60, ""), THF (Without_FOOL, Monomorphic, THF_Without_Choice), "mono_native_higher", keep_lamsN, false), "") (* FUDGE *))
val remote_alt_ergo =
  remotify_atp alt_ergo "Alt-Ergo" ["0.95.2"]
    (K (((250, ""), TFF (Without_FOOL, Polymorphic), "poly_native", keep_lamsN, false), "") (* FUDGE *))
val remote_e =
  remotify_atp e "E" ["2.0", "1.9.1", "1.8"]
    (K (((750, ""), TFF (Without_FOOL, Monomorphic), "mono_native", combsN, false), "") (* FUDGE *))
val remote_iprover =
  remotify_atp iprover "iProver" ["0.99"]
    (K (((150, ""), FOF, "mono_guards??", liftingN, false), "") (* FUDGE *))
val remote_leo2 =
  remotify_atp leo2 "LEO-II" ["1.5.0", "1.4", "1.3", "1.2", "1"]
    (K (((40, ""), THF (Without_FOOL, Monomorphic, THF_Without_Choice), "mono_native_higher", liftingN, false), "") (* FUDGE *))
val remote_leo3 =
  remotify_atp leo3 "Leo-III" ["1.1"]
    (K (((150, ""), THF (Without_FOOL, Polymorphic, THF_Without_Choice), "poly_native_higher", keep_lamsN, false), "") (* FUDGE *))
val remote_waldmeister = gen_remote_waldmeister waldmeisterN "raw_mono_tags??"
val remote_zipperposition =
  remotify_atp zipperposition "Zipperpin" ["2.1", "2.0"]
    (K (((512, ""), THF (Without_FOOL, Monomorphic, THF_Without_Choice), "mono_native_higher", keep_lamsN, false), "") (* FUDGE *))


(* Dummy prover *)

fun dummy_config prem_role format type_enc uncurried_aliases : atp_config =
  {exec = (["ISABELLE_ATP"], ["scripts/dummy_atp"]),
   arguments = K (K (K (K (K (K []))))),
   proof_delims = [],
   known_failures = known_szs_status_failures,
   prem_role = prem_role,
   best_slices =
     K [(1.0, (((200, ""), format, type_enc,
                if is_format_higher_order format then keep_lamsN
                else combsN, uncurried_aliases), ""))],
   best_max_mono_iters = default_max_mono_iters,
   best_max_new_mono_instances = default_max_new_mono_instances}


val dummy_fof_format = FOF
val dummy_fof_config = dummy_config Hypothesis dummy_fof_format "mono_guards??" false
val dummy_fof = (dummy_fofN, fn () => dummy_fof_config)

val dummy_tfx_format = TFF (With_FOOL, Polymorphic)
val dummy_tfx_config = dummy_config Hypothesis dummy_tfx_format "mono_native_fool" false
val dummy_tfx = (dummy_tfxN, fn () => dummy_tfx_config)

val dummy_thf_format = THF (With_FOOL, Polymorphic, THF_With_Choice)
val dummy_thf_config = dummy_config Hypothesis dummy_thf_format "mono_native_higher_fool" false
val dummy_thf = (dummy_thfN, fn () => dummy_thf_config)


(* Setup *)

fun add_atp (name, config) thy =
  Data.map (Symtab.update_new (name, (config, stamp ()))) thy
  handle Symtab.DUP name => error ("Duplicate ATP: " ^ quote name)

fun get_atp thy name =
  fst (the (Symtab.lookup (Data.get thy) name))
  handle Option.Option => error ("Unknown ATP: " ^ name)

val supported_atps = Symtab.keys o Data.get

fun is_atp_installed thy name =
  let val {exec, ...} = get_atp thy name () in
    exists (fn var => getenv var <> "") (fst exec)
  end

fun refresh_systems_on_tptp () =
  Synchronized.change remote_systems (fn _ => get_remote_systems ())

fun effective_term_order ctxt atp =
  let val ord = Config.get ctxt term_order in
    if ord = smartN then
      {is_lpo = false, gen_weights = (atp = spassN), gen_prec = (atp = spassN),
       gen_simp = false}
    else
      let val is_lpo = String.isSubstring lpoN ord in
        {is_lpo = is_lpo, gen_weights = not is_lpo andalso String.isSubstring xweightsN ord,
         gen_prec = String.isSubstring xprecN ord, gen_simp = String.isSubstring xsimpN ord}
      end
  end

val atps =
  [agsyhol, alt_ergo, e, iprover, leo2, leo3, satallax, spass, vampire, z3_tptp, zipperposition,
   remote_agsyhol, remote_alt_ergo, remote_e, remote_iprover, remote_leo2, remote_leo3,
   remote_waldmeister, remote_zipperposition, dummy_fof, dummy_tfx, dummy_thf]

val _ = Theory.setup (fold add_atp atps)

end;

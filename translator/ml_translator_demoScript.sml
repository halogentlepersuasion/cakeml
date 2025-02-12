(*
  A small example of using the HOL to CakeML translator.
*)
open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory combinTheory pairTheory;
open semanticPrimitivesTheory
open ml_translatorLib ml_translatorTheory;

val _ = new_theory "ml_translator_demo";

(* --- qsort translation --- *)

val res = translate sortingTheory.PART_DEF;
val res = translate sortingTheory.PARTITION_DEF;
val qsort = REWRITE_RULE [GSYM APPEND_ASSOC,APPEND] sortingTheory.QSORT_DEF;
val res = translate qsort;


(* --- all of the important lemmas about qsort --- *)

(* the value of the qsort closure (qsort_v) behaves like qsort *)
Theorem qsort_v_thm[allow_rebind] = res;

val Decls_thm =
  get_ml_prog_state ()
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def,ml_progTheory.ML_code_env_def];

(* the qsort program successfully evaluates to an env, called auto_env3 *)
Theorem evaluate_prog_thm =
  Decls_thm |> REWRITE_RULE [ml_progTheory.Decls_def]

(* looking up "qsort" in this env finds the qsort value (qsort_v) *)
Theorem lookup_qsort =
  EVAL ``nsLookup  ^(concl Decls_thm |> rator |> rand).v (Short "qsort")``

(* --- a more concrete example, not much use --- *)

Triviality Eval_Var_lemma:
  (lookup_var name env = SOME x) /\ P x ==> Eval env (Var (Short name)) P
Proof
  fs[Eval_Var]
QED

Theorem ML_QSORT_CORRECT:
   !env tys a ord R l xs refs.
      nsLookup env.v (Short "qsort") = SOME qsort_v /\
      LIST_TYPE a l xs /\ (lookup_var "xs" env = SOME xs) /\
      (a --> a --> BOOL) ord R /\ (lookup_var "R" env = SOME R) /\
      transitive ord /\ total ord
      ==>
      ?l' xs' refs' ck1 ck2.
        evaluate (empty_state with <| clock := ck1; refs := refs |>) env
          [App Opapp [App Opapp [Var (Short "qsort");
             Var (Short "R")]; Var (Short "xs")]] =
          (empty_state with <| clock := ck2; refs := refs ++ refs' |>,Rval [xs']) /\
        (LIST_TYPE a l' xs') /\ PERM l l' /\ SORTED ord l'
Proof
  rw [] \\ imp_res_tac Eval_Var_lemma
  \\ imp_res_tac (DISCH_ALL (hol2deep ``QSORT R xs``))
  \\ fs [Eval_def,ml_progTheory.eval_rel_def]
  \\ metis_tac [sortingTheory.QSORT_PERM,sortingTheory.QSORT_SORTED]
QED


val _ = export_theory();

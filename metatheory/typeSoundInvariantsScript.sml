(*Generated by Lem from typeSoundInvariants.lem.*)
open HolKernel Parse boolLib bossLib;
open lem_pervasivesTheory libTheory astTheory semanticPrimitivesTheory smallStepTheory typeSystemTheory;

val _ = numLib.prefer_num();



val _ = new_theory "typeSoundInvariants"

(*open import Pervasives*)
(*open import Lib*)
(*open import Ast*)
(*open import SemanticPrimitives*)
(*open import SmallStep*)
(*open import TypeSystem*)

(* Store typing *)
val _ = type_abbrev( "tenvS" , ``: (num, t) env``);

(* A value has a type *)
(* The number is how many deBruijn type variables are bound in the context. *)
(*val type_v : nat -> tenvM -> tenvC -> tenvS -> v -> t -> bool*)

(* A value environment has a corresponding type environment.  Since all of the
 * entries in the environment are values, and values have no free variables,
 * each entry in the environment can be typed in the empty environment (if at
 * all) *)
(*val type_env : tenvM -> tenvC -> tenvS -> envE -> tenvE -> bool*)

(* The type of the store *)
(*val type_s : tenvM -> tenvC -> tenvS -> store -> bool*)

(* An evaluation context has the second type when its hole is filled with a
 * value of the first type. *)
(* The number is how many deBruijn type variables are bound in the context.
 * This is only used for constructor contexts, because the value restriction 
 * ensures that no other contexts can be created under a let binding. *)
(*val type_ctxt : nat -> tenvM -> tenvC -> tenvS -> tenvE -> ctxt_frame -> t -> t -> bool*)
(*val type_ctxts : nat -> tenvM -> tenvC -> tenvS -> list ctxt -> t -> t -> bool*)
(*val type_state : nat -> tenvM -> tenvC -> tenvS -> state -> t -> bool*)
(*val context_invariant : nat -> list ctxt -> nat -> bool*)

(* Type programs without imposing signatures.  This is needed for the type
 * soundness proof *)
(*val type_top_ignore_sig : tenvM -> tenvC -> tenvE -> top -> tenvM -> tenvC -> env varN (nat * t) -> bool*)


val _ = Hol_reln ` (! menv cenv tenv d cenv' tenv'.
(type_d NONE menv cenv tenv d cenv' tenv')
==>
type_top_ignore_sig menv cenv tenv (Tdec d) emp cenv' tenv')

/\ (! menv cenv tenv mn spec ds cenv' tenv'.
 (~ (MEM mn (MAP FST menv)) /\
type_ds (SOME mn) menv cenv tenv ds cenv' tenv')
==>
type_top_ignore_sig menv cenv tenv (Tmod mn spec ds) [(mn,tenv')] cenv' emp)`;


val _ = Hol_reln ` (! tvs menv cenv senv b.
T
==>
type_v tvs menv cenv senv (Litv (Bool b)) Tbool)

/\ (! tvs menv cenv senv n.
T
==>
type_v tvs menv cenv senv (Litv (IntLit n)) Tint)

/\ (! tvs menv cenv senv s.
T
==>
type_v tvs menv cenv senv (Litv (StrLit s)) Tstring)

/\ (! tvs menv cenv senv.
T
==>
type_v tvs menv cenv senv (Litv Unit) Tunit)

/\ (! tvs menv cenv senv cn vs tvs' tn ts' ts.
(EVERY (check_freevars tvs []) ts' /\
((LENGTH tvs' = LENGTH ts') /\
(type_vs tvs menv cenv senv vs (MAP (type_subst (ZIP (tvs', ts'))) ts) /\
(lookup cn cenv = SOME (tvs', ts, tn)))))
==>
type_v tvs menv cenv senv (Conv (SOME cn) vs) (Tapp ts' (tid_exn_to_tc tn)))

/\ (! tvs menv cenv senv vs ts.
(type_vs tvs menv cenv senv vs ts)
==>
type_v tvs menv cenv senv (Conv NONE vs) (Tapp ts TC_tup))

/\ (! tvs menv cenv senv env tenv n e t1 t2.
(type_env menv cenv senv env tenv /\
(check_freevars tvs [] t1 /\
type_e menv cenv (bind_tenv n( 0) t1 (bind_tvar tvs tenv)) e t2))
==>
type_v tvs menv cenv senv (Closure env n e) (Tfn t1 t2))

/\ (! tvs menv cenv senv env funs n t tenv tenv'.
(type_env menv cenv senv env tenv /\
(type_funs menv cenv (bind_var_list( 0) tenv' (bind_tvar tvs tenv)) funs tenv' /\
(lookup n tenv' = SOME t)))
==>
type_v tvs menv cenv senv (Recclosure env funs n) t)

/\ (! tvs menv cenv senv n t.
(check_freevars( 0) [] t /\
(lookup n senv = SOME t))
==>
type_v tvs menv cenv senv (Loc n) (Tref t))

/\ (! tvs menv cenv senv.
T
==>
type_vs tvs menv cenv senv [] [])

/\ (! tvs menv cenv senv v vs t ts.
(type_v tvs menv cenv senv v t /\
type_vs tvs menv cenv senv vs ts)
==>
type_vs tvs menv cenv senv (v::vs) (t::ts))

/\ (! menv cenv senv.
T
==>
type_env menv cenv senv emp Empty)

/\ (! menv cenv senv n v env t tenv tvs.
(type_v tvs menv cenv senv v t /\
type_env menv cenv senv env tenv)
==>
type_env menv cenv senv (bind n v env) (bind_tenv n tvs t tenv))`;

 val consistent_mod_env_defn = Hol_defn "consistent_mod_env" `
 
(consistent_mod_env tenvS tenvC [] [] = T)
/\
(consistent_mod_env tenvS tenvC ((mn,env)::menv) ((mn',tenv)::tenvM) =  
((mn = mn') /\  
(~ (MEM mn (MAP FST tenvM)) /\  
(type_env tenvM tenvC tenvS env (bind_var_list2 tenv Empty) /\
  consistent_mod_env tenvS tenvC menv tenvM))))
/\
(consistent_mod_env tenvS tenvC _ _ = F)`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn consistent_mod_env_defn;

val _ = Define `
 (type_s menv cenv senv s =  
(! l. 
    ((? t. lookup l senv = SOME t) <=> (? v. store_lookup l s = SOME v)) /\    
(! t v. ((lookup l senv = SOME t) /\ (store_lookup l s = SOME v)) ==> type_v( 0) menv cenv senv v t)))`;


val _ = Hol_reln ` (! n.
T
==>
context_invariant n [] n)

/\ (! dec_tvs c env.
(context_invariant dec_tvs c( 0))
==>
context_invariant dec_tvs ((Craise () ,env) :: c) 0)

/\ (! dec_tvs c pes env.
(context_invariant dec_tvs c( 0))
==>
context_invariant dec_tvs ((Chandle ()  pes,env) :: c) 0)

/\ (! dec_tvs c op e env.
(context_invariant dec_tvs c( 0))
==>
context_invariant dec_tvs ((Capp1 op ()  e,env) :: c) 0)

/\ (! dec_tvs c op v env.
(context_invariant dec_tvs c( 0))
==>
context_invariant dec_tvs ((Capp2 op v () ,env) :: c) 0)

/\ (! dec_tvs c l e env.
(context_invariant dec_tvs c( 0))
==>
context_invariant dec_tvs ((Clog l ()  e,env) :: c) 0)

/\ (! dec_tvs c e1 e2 env.
(context_invariant dec_tvs c( 0))
==>
context_invariant dec_tvs ((Cif ()  e1 e2,env) :: c) 0)

/\ (! dec_tvs c pes env err_v.
(context_invariant dec_tvs c( 0))
==>
context_invariant dec_tvs ((Cmat ()  pes err_v,env) :: c) 0)

/\ (! dec_tvs c tvs x e env.
(context_invariant dec_tvs c( 0))
==>
context_invariant dec_tvs ((Clet x ()  e,env) :: c) tvs)

/\ (! dec_tvs c cn vs es tvs env.
(context_invariant dec_tvs c tvs /\
( ~ (tvs =( 0)) ==> EVERY is_value es))
==>
context_invariant dec_tvs ((Ccon cn vs ()  es,env) :: c) tvs)

/\ (! dec_tvs c op env.
(context_invariant dec_tvs c( 0))
==>
context_invariant dec_tvs ((Cuapp op () ,env) :: c) 0)`;

val _ = Hol_reln ` (! tvs menv cenv senv tenv t.
(check_freevars tvs [] t)
 ==>
type_ctxt tvs menv cenv senv tenv (Craise () ) Texn t)

/\ (! tvs menv cenv senv tenv pes t.
(! ((p,e) :: LIST_TO_SET pes). ? tenv'.
   ALL_DISTINCT (pat_bindings p []) /\   
(type_p (num_tvs tenv) cenv p Texn tenv' /\
   type_e menv cenv (bind_var_list( 0) tenv' tenv) e t))
==>
type_ctxt tvs menv cenv senv tenv (Chandle ()  pes) t t)

/\ (! tvs menv cenv senv tenv uop t1 t2.
(check_freevars tvs [] t1 /\
(check_freevars tvs [] t2 /\
type_uop uop t1 t2))
==>
type_ctxt tvs menv cenv senv tenv (Cuapp uop () ) t1 t2)

/\ (! tvs menv cenv senv tenv e op t1 t2 t3.
(check_freevars tvs [] t1 /\
(check_freevars tvs [] t3 /\
(type_e menv cenv tenv e t2 /\
type_op op t1 t2 t3)))
==>
type_ctxt tvs menv cenv senv tenv (Capp1 op ()  e) t1 t3)

/\ (! tvs menv cenv senv tenv op v t1 t2 t3.
(check_freevars tvs [] t2 /\
(check_freevars tvs [] t3 /\
(type_v( 0) menv cenv senv v t1 /\
type_op op t1 t2 t3)))
==>
type_ctxt tvs menv cenv senv tenv (Capp2 op v () ) t2 t3)

/\ (! tvs menv cenv senv tenv op e.
(type_e menv cenv tenv e Tbool)
==>
type_ctxt tvs menv cenv senv tenv (Clog op ()  e) Tbool Tbool)

/\ (! tvs menv cenv senv tenv e1 e2 t.
(type_e menv cenv tenv e1 t /\
type_e menv cenv tenv e2 t)
==>
type_ctxt tvs menv cenv senv tenv (Cif ()  e1 e2) Tbool t)

/\ (! tvs menv cenv senv tenv t1 t2 pes err_v.
(((pes = []) ==> (check_freevars tvs [] t1 /\ check_freevars( 0) [] t2)) /\
((! ((p,e) :: LIST_TO_SET pes) . ? tenv'.
   ALL_DISTINCT (pat_bindings p []) /\   
(type_p tvs cenv p t1 tenv' /\
   type_e menv cenv (bind_var_list( 0) tenv' tenv) e t2)) /\
type_v( 0) menv cenv senv err_v Texn))
==>
type_ctxt tvs menv cenv senv tenv (Cmat ()  pes err_v) t1 t2)

/\ (! tvs menv cenv senv tenv e t1 t2 n.
(check_freevars tvs [] t1 /\
type_e menv cenv (bind_tenv n tvs t1 tenv) e t2)
==>
type_ctxt tvs menv cenv senv tenv (Clet n ()  e) t1 t2)

/\ (! tvs menv cenv senv tenv cn vs es ts1 ts2 t tn ts' tvs'.
(EVERY (check_freevars tvs []) ts' /\
((LENGTH tvs' = LENGTH ts') /\
(type_vs tvs menv cenv senv (REVERSE vs)
        (MAP (type_subst (ZIP (tvs', ts'))) ts1) /\
(type_es menv cenv (bind_tvar tvs tenv) es (MAP (type_subst (ZIP (tvs', ts'))) ts2) /\
(lookup cn cenv = SOME (tvs', ((ts1++[t])++ts2), tn))))))
==>
type_ctxt tvs menv cenv senv tenv (Ccon (SOME cn) vs ()  es) (type_subst (ZIP (tvs', ts')) t)
          (Tapp ts' (tid_exn_to_tc tn)))

/\ (! tvs menv cenv senv tenv vs es t ts1 ts2.
(check_freevars tvs [] t /\
(type_vs tvs menv cenv senv (REVERSE vs) ts1 /\
type_es menv cenv (bind_tvar tvs tenv) es ts2))
==>
type_ctxt tvs menv cenv senv tenv (Ccon NONE vs ()  es) t (Tapp ((ts1++[t])++ts2) TC_tup))`;

val _ = Define `
 (poly_context cs =  
 ((case cs of
      (Ccon cn vs ()  es,env) :: cs => EVERY is_value es
    | (Clet x ()  e,env) :: cs => T
    | [] => T
    | _ => F
  )))`;


val _ = Define `
 (is_ccon c =  
 ((case c of
      Ccon cn vs ()  es => T
    | _ => F
  )))`;


val _ = Hol_reln ` (! tvs tenvM tenvC senv t.
(check_freevars tvs [] t)
==>
type_ctxts tvs tenvM tenvC senv [] t t)

/\ (! tvs tenvM tenvC senv c env cs tenv t1 t2 t3.
(type_env tenvM tenvC senv env tenv /\
(type_ctxt tvs tenvM tenvC senv tenv c t1 t2 /\
type_ctxts (if is_ccon c /\ poly_context cs then tvs else  0) tenvM tenvC senv cs t2 t3))
==>
type_ctxts tvs tenvM tenvC senv ((c,env)::cs) t1 t3)`;

val _ = Hol_reln ` (! dec_tvs tenvM tenvC senv envM envC s env e c t1 t2 tenv tvs.
(context_invariant dec_tvs c tvs /\
(type_ctxts tvs tenvM tenvC senv c t1 t2 /\
(type_env tenvM tenvC senv env tenv /\
(type_s tenvM tenvC senv s /\
(type_e tenvM tenvC (bind_tvar tvs tenv) e t1 /\
(( ~ (tvs =( 0))) ==> is_value e))))))
==>
type_state dec_tvs tenvM tenvC senv (envM,envC, s, env, Exp e, c) t2)

/\ (! dec_tvs tenvM tenvC senv envM envC s env v c t1 t2 tenv tvs.
(context_invariant dec_tvs c tvs /\
(type_ctxts tvs tenvM tenvC senv c t1 t2 /\
(type_env tenvM tenvC senv env tenv /\
(type_s tenvM tenvC senv s /\
type_v tvs tenvM tenvC senv v t1))))
==>
type_state dec_tvs tenvM tenvC senv (envM, envC, s, env, Val v, c) t2)`;
val _ = export_theory()


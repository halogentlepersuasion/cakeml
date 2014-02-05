(*Generated by Lem from typeSystem.lem.*)
open HolKernel Parse boolLib bossLib;
open lem_pervasives_extraTheory libTheory astTheory semanticPrimitivesTheory;

val _ = numLib.prefer_num();



val _ = new_theory "typeSystem"

(*open import Pervasives_extra*)
(*open import Lib*)
(*open import Ast*)

(* Only to get check_dup_ctors *)
(*open import SemanticPrimitives*) 

(* Type substitution *)

(* Increment the deBruijn indices in a type by n levels, skipping all levels
 * less than skip. *)
(*val deBruijn_inc : nat -> nat -> t -> t*)
 val deBruijn_inc_defn = Hol_defn "deBruijn_inc" `

(deBruijn_inc skip n (Tvar tv) = (Tvar tv))
/\
(deBruijn_inc skip n (Tvar_db m) =  
(if m < skip then
    Tvar_db m
  else
    Tvar_db (m + n)))
/\
(deBruijn_inc skip n (Tapp ts tn) = (Tapp (MAP (deBruijn_inc skip n) ts) tn))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn deBruijn_inc_defn;

(* skip the lowest given indices and replace the next (LENGTH ts) with the given types and reduce all the higher ones *)
(*val deBruijn_subst : nat -> list t -> t -> t*)
 val deBruijn_subst_defn = Hol_defn "deBruijn_subst" `

(deBruijn_subst skip ts (Tvar tv) = (Tvar tv))
/\
(deBruijn_subst skip ts (Tvar_db n) =  
(if ~ (n < skip) /\ (n < (LENGTH ts + skip)) then
    EL (n - skip) ts
  else if ~ (n < skip) then
    Tvar_db (n - LENGTH ts)
  else
    Tvar_db n))
/\
(deBruijn_subst skip ts (Tapp ts' tn) =  
(Tapp (MAP (deBruijn_subst skip ts) ts') tn))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn deBruijn_subst_defn;

(* constructor type environments: each constructor has a type
 * forall tyvars. t list -> (tyvars) typeN *)
val _ = type_abbrev( "tenvC" , ``: (( conN id), ( tvarN list # t list # tid_or_exn)) env``);

(* Type environments *)
val _ = Hol_datatype `
 tenvE =
    Empty
  (* Binds several de Bruijn type variables *)
  | Bind_tvar of num => tenvE
  (* The number is how many de Bruijn type variables the typescheme binds *)
  | Bind_name of varN => num => t => tenvE`;


val _ = type_abbrev( "tenvM" , ``: (modN, ( (varN, (num # t))env)) env``);

val _ = Define `
 (bind_tvar tvs tenv = (if tvs = 0 then tenv else Bind_tvar tvs tenv))`;


(*val lookup_tenv : varN -> nat -> tenvE -> maybe (nat * t)*) 
 val lookup_tenv_defn = Hol_defn "lookup_tenv" `

(lookup_tenv n inc Empty = NONE)
/\
(lookup_tenv n inc (Bind_tvar tvs e) = (lookup_tenv n (inc + tvs) e))
/\
(lookup_tenv n inc (Bind_name n' tvs t e) =  
(if n' = n then
    SOME (tvs, deBruijn_inc tvs inc t)
  else
    lookup_tenv n inc e))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn lookup_tenv_defn;

(*val bind_tenv : varN -> nat -> t -> tenvE -> tenvE*)
val _ = Define `
 (bind_tenv n tvs t e = (Bind_name n tvs t e))`;


(*val t_lookup_var_id : id varN -> tenvM -> tenvE -> maybe (nat * t)*)
val _ = Define `
 (t_lookup_var_id id tenvM tenvE =  
((case id of
      Short x => lookup_tenv x( 0) tenvE
    | Long x y =>
        (case lookup x tenvM of
            NONE => NONE
          | SOME tenvE' => lookup y tenvE'
        )
  )))`;


(*val num_tvs : tenvE -> nat*)
 val num_tvs_defn = Hol_defn "num_tvs" `
 
(num_tvs Empty =( 0))
/\
(num_tvs (Bind_tvar tvs e) = (tvs + num_tvs e))
/\
(num_tvs (Bind_name n tvs t e) = (num_tvs e))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn num_tvs_defn;

(* A pattern matches values of a certain type and extends the type environment
 * with the pattern's binders. The number is the maximum deBruijn type variable
 * allowed. *)
(*val type_p : nat -> tenvC -> pat -> t -> list (varN * t) -> bool*)

(* An expression has a type *)
(*val type_e : tenvM -> tenvC -> tenvE -> exp -> t -> bool*)

(* A list of expressions has a list of types *)
(*val type_es : tenvM -> tenvC -> tenvE -> list exp -> list t -> bool*)

(* Type a mutually recursive bundle of functions.  Unlike pattern typing, the
 * resulting environment does not extend the input environment, but just
 * represents the functions *)
(*val type_funs : tenvM -> tenvC -> tenvE -> list (varN * varN * exp) ->
                list (varN * t) -> bool*)

(* Check a declaration and update the top-level environments *)
(*val type_d : maybe modN -> tenvM -> tenvC -> tenvE -> dec -> tenvC -> env varN (nat * t) -> bool*)

(*val type_ds : maybe modN -> tenvM -> tenvC -> tenvE -> list dec -> tenvC -> env varN (nat * t) -> bool*)
(*val weakE : env varN (nat * t) -> env varN (nat * t) -> bool*)
(*val weakC : tenvC -> tenvC -> bool*)
(*val check_signature : maybe modN -> tenvC -> env varN (nat * t) -> maybe specs -> tenvC -> env varN (nat * t) -> bool*)
(*val type_specs : maybe modN -> tenvC -> env varN (nat * t) -> specs -> tenvC -> env varN (nat * t) -> bool*)
(*val type_prog : tenvM -> tenvC -> tenvE -> list top -> tenvM -> tenvC -> env varN (nat * t) -> bool*)

(* Check that the operator can have type (t1 -> t2 -> t3) *)
(*val type_op : op -> t -> t -> t -> bool*)
val _ = Define `
 (type_op op t1 t2 t3 =  
((case (op,t1,t2) of
      (Opapp, Tapp [t2'; t3'] TC_fn, _) => (t2 = t2') /\ (t3 = t3')
    | (Opn _, Tapp [] TC_int, Tapp [] TC_int) => (t3 = Tint)
    | (Opb _, Tapp [] TC_int, Tapp [] TC_int) => (t3 = Tbool)
    | (Equality, t1, t2) => (t1 = t2) /\ (t3 = Tbool)
    | (Opassign, Tapp [t1] TC_ref, t2) => (t1 = t2) /\ (t3 = Tunit)
    | _ => F
  )))`;


(* Check that the operator can have type (t1 -> t2) *)
(*val type_uop : uop -> t -> t -> bool*)
val _ = Define `
 (type_uop uop t1 t2 =  
((case (uop,t1) of
      (Opref, _) => t2 = Tref t1
    | (Opderef, Tapp [t1'] TC_ref) => t2 = t1'
    | _ => F
  )))`;


(* Check that the free type variables are in the given list.  Every deBruijn
 * variable must be smaller than the first argument.  So if it is 0, no deBruijn
 * indices are permitted. *)
(*val check_freevars : nat -> list tvarN -> t -> bool*)
 val check_freevars_defn = Hol_defn "check_freevars" `

(check_freevars dbmax tvs (Tvar tv) =  
(MEM tv tvs))
/\
(check_freevars dbmax tvs (Tapp ts tn) =  
(EVERY (check_freevars dbmax tvs) ts))
/\
(check_freevars dbmax tvs (Tvar_db n) = (n < dbmax))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn check_freevars_defn;

(* Check that a type definition defines no already defined (or duplicate)
 * constructors or types, and that the free type variables of each constructor
 * argument type are included in the type's type parameters. *)
(*val check_ctor_tenv :
   maybe modN -> tenvC -> list (list tvarN * typeN * list (conN * list t)) -> bool*)
val _ = Define `
 (check_ctor_tenv mn tenvC tds =  
(check_dup_ctors mn tenvC tds /\  
(EVERY
    (\ (tvs,tn,ctors) . 
       ALL_DISTINCT tvs /\
       EVERY
         (\ (cn,ts) .  (EVERY (check_freevars( 0) tvs) ts))
         ctors)
    tds /\  
(ALL_DISTINCT (MAP (\p .  
  (case (p ) of ( (_,tn,_) ) => tn )) tds) /\
  EVERY
    (\ (tvs,tn,ctors) . 
       EVERY (\p .  (case (p ) of ( (_,(_,_,tn')) ) => TypeId (mk_id mn tn) <> tn' )) tenvC)
    tds))))`;


(*val build_ctor_tenv : maybe modN -> list (list tvarN * typeN * list (conN * list t)) -> tenvC*)
val _ = Define `
 (build_ctor_tenv mn tds =  
(FLAT
    (MAP
       (\ (tvs,tn,ctors) . 
          MAP (\ (cn,ts) .  (mk_id mn cn,(tvs,ts, TypeId (mk_id mn tn)))) ctors)
       tds)))`;


(* Simultaneous substitution of types for type variables in a type *)
(*val type_subst : env tvarN t -> t -> t*)
 val type_subst_defn = Hol_defn "type_subst" `

(type_subst s (Tvar tv) =  
((case lookup tv s of
      NONE => Tvar tv
    | SOME(t) => t
  )))
/\
(type_subst s (Tapp ts tn) =  
(Tapp (MAP (type_subst s) ts) tn))
/\
(type_subst s (Tvar_db n) = (Tvar_db n))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn type_subst_defn;

(*val bind_var_list : nat -> list (varN * t) -> tenvE -> tenvE*)
 val bind_var_list_defn = Hol_defn "bind_var_list" `

(bind_var_list tvs [] tenv = tenv)
/\
(bind_var_list tvs ((n,t)::binds) tenv =  
(bind_tenv n tvs t (bind_var_list tvs binds tenv)))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn bind_var_list_defn;

(*val bind_var_list2 : env varN (nat * t) -> tenvE -> tenvE*)
 val bind_var_list2_defn = Hol_defn "bind_var_list2" `

(bind_var_list2 [] tenv = tenv)
/\
(bind_var_list2 ((n,(tvs,t))::binds) tenv =  
(bind_tenv n tvs t (bind_var_list2 binds tenv)))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn bind_var_list2_defn;


(* For the value restriction on let-based polymorphism *)
(*val is_value : exp -> bool*)
 val is_value_defn = Hol_defn "is_value" `
 
(is_value (Lit _) = T)
/\
(is_value (Con _ es) = (EVERY is_value es))
/\
(is_value (Var _) = T)
/\
(is_value (Fun _ _) = T)
/\
(is_value _ = F)`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) Defn.save_defn is_value_defn;

(*val tid_exn_to_tc : tid_or_exn -> tc*)
val _ = Define `
 (tid_exn_to_tc t =  
((case t of
      TypeId tid => TC_name tid
    | TypeExn => TC_exn
  )))`;


val _ = Hol_reln ` (! tvs cenv n t.
(check_freevars tvs [] t)
==>
type_p tvs cenv (Pvar n) t [(n,t)])

/\ (! tvs cenv b.
T
==>
type_p tvs cenv (Plit (Bool b)) Tbool [])

/\ (! tvs cenv n.
T
==>
type_p tvs cenv (Plit (IntLit n)) Tint [])

/\ (! tvs cenv s.
T
==>
type_p tvs cenv (Plit (StrLit s)) Tstring [])

/\ (! tvs cenv.
T
==>
type_p tvs cenv (Plit Unit) Tunit [])

/\ (! tvs cenv cn ps ts tvs' tn ts' tenv.
(EVERY (check_freevars tvs []) ts' /\
((LENGTH ts' = LENGTH tvs') /\
(type_ps tvs cenv ps (MAP (type_subst (ZIP (tvs', ts'))) ts) tenv /\
(lookup cn cenv = SOME (tvs', ts, tn)))))
==>
type_p tvs cenv (Pcon (SOME cn) ps) (Tapp ts' (tid_exn_to_tc tn)) tenv)

/\ (! tvs cenv ps ts tenv.
(type_ps tvs cenv ps ts tenv)
==>
type_p tvs cenv (Pcon NONE ps) (Tapp ts TC_tup) tenv)

/\ (! tvs cenv p t tenv.
(type_p tvs cenv p t tenv)
==>
type_p tvs cenv (Pref p) (Tref t) tenv)

/\ (! tvs cenv.
T
==>
type_ps tvs cenv [] [] [])

/\ (! tvs cenv p ps t ts tenv tenv'.
(type_p tvs cenv p t tenv /\
type_ps tvs cenv ps ts tenv')
==>
type_ps tvs cenv (p::ps) (t::ts) (tenv'++tenv))`;

val _ = Hol_reln ` (! menv cenv tenv b.
T
==>
type_e menv cenv tenv (Lit (Bool b)) Tbool)

/\ (! menv cenv tenv n.
T
==>
type_e menv cenv tenv (Lit (IntLit n)) Tint)

/\ (! menv cenv tenv s.
T
==>
type_e menv cenv tenv (Lit (StrLit s)) Tstring)

/\ (! menv cenv tenv.
T
==>
type_e menv cenv tenv (Lit Unit) Tunit)

/\ (! menv cenv tenv e t.
(check_freevars (num_tvs tenv) [] t /\
type_e menv cenv tenv e Texn) 
==>
type_e menv cenv tenv (Raise e) t)

/\ (! menv cenv tenv e pes t.
(type_e menv cenv tenv e t /\
(( ~ (pes = [])) /\
(! ((p,e) :: LIST_TO_SET pes). ? tenv'.
   ALL_DISTINCT (pat_bindings p []) /\   
(type_p (num_tvs tenv) cenv p Texn tenv' /\
   type_e menv cenv (bind_var_list( 0) tenv' tenv) e t))))
==>
type_e menv cenv tenv (Handle e pes) t)

/\ (! menv cenv tenv cn es tvs tn ts' ts.
(EVERY (check_freevars (num_tvs tenv) []) ts' /\
((LENGTH tvs = LENGTH ts') /\
(type_es menv cenv tenv es (MAP (type_subst (ZIP (tvs, ts'))) ts) /\
(lookup cn cenv = SOME (tvs, ts, tn)))))
==>
type_e menv cenv tenv (Con (SOME cn) es) (Tapp ts' (tid_exn_to_tc tn)))

/\ (! menv cenv tenv es ts.
(type_es menv cenv tenv es ts)
==>
type_e menv cenv tenv (Con NONE es) (Tapp ts TC_tup))

/\ (! menv cenv tenv n t targs tvs.
((tvs = LENGTH targs) /\
(EVERY (check_freevars (num_tvs tenv) []) targs /\
(t_lookup_var_id n menv tenv = SOME (tvs,t))))
==>
type_e menv cenv tenv (Var n) (deBruijn_subst( 0) targs t))

/\ (! menv cenv tenv n e t1 t2.
(check_freevars (num_tvs tenv) [] t1 /\
type_e menv cenv (bind_tenv n( 0) t1 tenv) e t2)
==>
type_e menv cenv tenv (Fun n e) (Tfn t1 t2))

/\ (! menv cenv tenv uop e t1 t2.
(type_e menv cenv tenv e t1 /\
type_uop uop t1 t2)
==>
type_e menv cenv tenv (Uapp uop e) t2)

/\ (! menv cenv tenv op e1 e2 t1 t2 t3.
(type_e menv cenv tenv e1 t1 /\
(type_e menv cenv tenv e2 t2 /\
type_op op t1 t2 t3))
==>
type_e menv cenv tenv (App op e1 e2) t3)

/\ (! menv cenv tenv l e1 e2.
(type_e menv cenv tenv e1 Tbool /\
type_e menv cenv tenv e2 Tbool)
==>
type_e menv cenv tenv (Log l e1 e2) Tbool)

/\ (! menv cenv tenv e1 e2 e3 t.
(type_e menv cenv tenv e1 Tbool /\
(type_e menv cenv tenv e2 t /\
type_e menv cenv tenv e3 t))
==>
type_e menv cenv tenv (If e1 e2 e3) t)

/\ (! menv cenv tenv e pes t1 t2.
(type_e menv cenv tenv e t1 /\
(( ~ (pes = [])) /\
(! ((p,e) :: LIST_TO_SET pes) . ? tenv'.
   ALL_DISTINCT (pat_bindings p []) /\   
(type_p (num_tvs tenv) cenv p t1 tenv' /\
   type_e menv cenv (bind_var_list( 0) tenv' tenv) e t2))))
==>
type_e menv cenv tenv (Mat e pes) t2)

/\ (! menv cenv tenv n e1 e2 t1 t2 tvs.
(is_value e1 /\
(type_e menv cenv (bind_tvar tvs tenv) e1 t1 /\
type_e menv cenv (bind_tenv n tvs t1 tenv) e2 t2))
==>
type_e menv cenv tenv (Let n e1 e2) t2)

/\ (! menv cenv tenv n e1 e2 t1 t2.
(type_e menv cenv tenv e1 t1 /\
type_e menv cenv (bind_tenv n( 0) t1 tenv) e2 t2)
==>
type_e menv cenv tenv (Let n e1 e2) t2)

/\ (! menv cenv tenv funs e t tenv' tvs.
(type_funs menv cenv (bind_var_list( 0) tenv' (bind_tvar tvs tenv)) funs tenv' /\
type_e menv cenv (bind_var_list tvs tenv' tenv) e t)
==>
type_e menv cenv tenv (Letrec funs e) t)

/\ (! menv cenv tenv.
T
==>
type_es menv cenv tenv [] [])

/\ (! menv cenv tenv e es t ts.
(type_e menv cenv tenv e t /\
type_es menv cenv tenv es ts)
==>
type_es menv cenv tenv (e::es) (t::ts))

/\ (! menv cenv env.
T
==>
type_funs menv cenv env [] [])

/\ (! menv cenv env fn n e funs env' t1 t2.
(check_freevars (num_tvs env) [] (Tfn t1 t2) /\
(type_e menv cenv (bind_tenv n( 0) t1 env) e t2 /\
(type_funs menv cenv env funs env' /\
(lookup fn env' = NONE))))
==>
type_funs menv cenv env ((fn, n, e)::funs) ((fn, Tfn t1 t2)::env'))`;

(*val tenv_add_tvs : nat -> env varN t -> env varN (nat * t)*)
val _ = Define `
 (tenv_add_tvs tvs tenv =  
(MAP (\ (n,t) .  (n,(tvs,t))) tenv))`;


val _ = Hol_reln ` (! tvs mn menv cenv tenv p e t tenv'.
(is_value e /\
(ALL_DISTINCT (pat_bindings p []) /\
(type_p tvs cenv p t tenv' /\
type_e menv cenv (bind_tvar tvs tenv) e t)))
==>
type_d mn menv cenv tenv (Dlet p e) emp (tenv_add_tvs tvs tenv'))

/\ (! mn menv cenv tenv p e t tenv'.
(ALL_DISTINCT (pat_bindings p []) /\
(type_p( 0) cenv p t tenv' /\
type_e menv cenv tenv e t))
==>
type_d mn menv cenv tenv (Dlet p e) emp (tenv_add_tvs( 0) tenv'))

/\ (! mn menv cenv tenv funs tenv' tvs.
(type_funs menv cenv (bind_var_list( 0) tenv' (bind_tvar tvs tenv)) funs tenv')
==>
type_d mn menv cenv tenv (Dletrec funs) emp (tenv_add_tvs tvs tenv'))

/\ (! mn menv cenv tenv tdecs.
(check_ctor_tenv mn cenv tdecs)
==>
type_d mn menv cenv tenv (Dtype tdecs) (build_ctor_tenv mn tdecs) emp)

/\ (! mn menv cenv tenv cn ts.
((lookup (mk_id mn cn) cenv = NONE) /\
EVERY (check_freevars( 0) []) ts)
==>
type_d mn menv cenv tenv (Dexn cn ts) (bind (mk_id mn cn) ([], ts, TypeExn) emp) emp)`;

val _ = Hol_reln ` (! mn menv cenv tenv.
T
==>
type_ds mn menv cenv tenv [] emp emp)

/\ (! mn menv cenv tenv d ds cenv' tenv' cenv'' tenv''.
(type_d mn menv cenv tenv d cenv' tenv' /\
type_ds mn menv (merge cenv' cenv) (bind_var_list2 tenv' tenv) ds cenv'' tenv'')
==>
type_ds mn menv cenv tenv (d::ds) (merge cenv'' cenv') (merge tenv'' tenv'))`;

val _ = Hol_reln ` (! cenv tenv mn.
T
==>
type_specs mn cenv tenv [] cenv tenv)

/\ (! mn cenv tenv x t specs cenv' tenv' fvs.
(check_freevars( 0) fvs t /\
type_specs mn cenv (bind x (LENGTH fvs, type_subst (ZIP (fvs, (MAP Tvar_db (COUNT_LIST (LENGTH fvs))))) t) tenv) specs cenv' tenv')
==>
type_specs mn cenv tenv (Sval x t :: specs) cenv' tenv') 

/\ (! mn cenv tenv td specs cenv' tenv'.
(check_ctor_tenv mn cenv td /\
type_specs mn (merge (build_ctor_tenv mn td) cenv) tenv specs cenv' tenv')
==>
type_specs mn cenv tenv (Stype td :: specs) cenv' tenv')

/\ (! mn cenv tenv cn ts specs cenv' tenv'.
((lookup (mk_id mn cn) cenv = NONE) /\
(EVERY (check_freevars( 0) []) ts /\
type_specs mn (bind (mk_id mn cn) ([], ts, TypeExn) cenv) tenv specs cenv' tenv'))
==>
type_specs mn cenv tenv (Sexn cn ts :: specs) cenv' tenv')

/\ (! mn cenv tenv tn specs cenv' tenv' tvs.
(ALL_DISTINCT tvs /\
(EVERY (\p .  (case (p ) of ( (_,(_,_,tn')) ) => TypeId (mk_id mn tn) <> tn' )) cenv /\
type_specs mn cenv tenv specs cenv' tenv'))
==>
type_specs mn cenv tenv (Stype_opq tvs tn :: specs) cenv' tenv')`;

val _ = Define `
 (weakE tenv_impl tenv_spec =  
(! x.
    (case lookup x tenv_spec of
        SOME (tvs_spec, t_spec) =>
          (case lookup x tenv_impl of
              NONE => F
            | SOME (tvs_impl, t_impl) =>
                ? subst.                  
 (LENGTH subst = tvs_impl) /\                  
(check_freevars tvs_impl [] t_impl /\                  
(EVERY (check_freevars tvs_spec []) subst /\                  
(deBruijn_subst( 0) subst t_impl = t_spec)))
          )
        | NONE => T
    )))`;


val _ = Define `
 (weakC cenv_impl cenv_spec =  
(! cn.
    (case lookup cn cenv_spec of
        SOME (tvs_spec,ts_spec,tn_spec) =>
          (case lookup cn cenv_impl of
              NONE => F
            | SOME (tvs_impl, ts_impl, tn_impl) =>                
(tn_spec = tn_impl) /\                
((
                (* For simplicity, we reject matches that differ only by renaming of bound type variables *)tvs_spec = tvs_impl) /\                
(ts_spec = ts_impl)) 
          )
      | NONE => T
    )))`;


val _ = Hol_reln ` (! mn cenv tenv.
T
==>
check_signature mn cenv tenv NONE cenv tenv)

/\ (! mn cenv tenv specs tenv' cenv'.
(weakE tenv tenv' /\
(weakC cenv cenv' /\
type_specs mn emp emp specs cenv' tenv'))
==>
check_signature mn cenv tenv (SOME specs) cenv' tenv')`;

val _ = Hol_reln ` (! menv cenv tenv d cenv' tenv'.
(type_d NONE menv cenv tenv d cenv' tenv')
==>
type_top menv cenv tenv (Tdec d) emp cenv' tenv')

/\ (! menv cenv tenv mn spec ds cenv' tenv' cenv'' tenv''.
(~ (MEM mn (MAP FST menv)) /\
(type_ds (SOME mn) menv cenv tenv ds cenv' tenv' /\
check_signature (SOME mn) cenv' tenv' spec cenv'' tenv''))
==>
type_top menv cenv tenv (Tmod mn spec ds) [(mn,tenv'')] cenv'' emp)`;

val _ = Hol_reln ` (! menv cenv tenv.
T
==>
type_prog menv cenv tenv [] emp emp emp)

/\ (! menv cenv tenv top tops menv' cenv' tenv' menv'' cenv'' tenv''.
(type_top menv cenv tenv top menv' cenv' tenv' /\
type_prog (merge menv' menv) (merge cenv' cenv) (bind_var_list2 tenv' tenv) tops menv'' cenv'' tenv'')
==>
type_prog menv cenv tenv (top :: tops) (merge menv'' menv') (merge cenv'' cenv') (merge tenv'' tenv'))`;
val _ = export_theory()


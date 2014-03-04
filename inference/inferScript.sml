open preamble miscTheory astTheory typeSystemTheory;
open unifyTheory;
open stringTheory monadsyntax;

val _ = new_theory "infer";

(* 'a is the type of the state, 'b is the type of successful computations, and
 * 'c is the type of exceptions *)

val _ = Hol_datatype `
  exc = Success of 'a | Failure of 'b`;

val _ = type_abbrev("M", ``:'a -> ('b, 'c) exc # 'a``);

val st_ex_bind_def = Define `
(st_ex_bind : (α, β, γ) M -> (β -> (α, δ, γ) M) -> (α, δ, γ) M) x f =
  λs.
    case x s of
      (Success y,s) => f y s
    | (Failure e,s) => (Failure e,s)`;

val st_ex_return_def = Define `
(st_ex_return (*: α -> (β, α, γ) M*)) x = 
  λs. (Success x, s)`;

(*
val monad_bind_success = Q.prove (
`!m f r.
  (ex_bind m f = Success r)
  =
  (?r'. (m = Success r') ∧ (f r' = Success r))`,
rw [ex_bind_def] >>
cases_on `m` >>
rw [] >>
metis_tac []);
*)

val _ = temp_overload_on ("monad_bind", ``st_ex_bind``);
val _ = temp_overload_on ("monad_unitbind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("monad_ignore_bind", ``\x y. st_ex_bind x (\z. y)``);
val _ = temp_overload_on ("return", ``st_ex_return``);

val failwith_def = Define `
(failwith : α -> (β, γ, α) M) msg = (\s. (Failure msg, s))`;

val guard_def = Define `
guard P msg = if P then return () else failwith msg`;

val read_def = Define `
(read : (α, α, β) M) =
  \s. (Success s, s)`;

val write_def = Define `
(write : α -> (α, unit, β) M) v =
  \s. (Success (), v)`;

val id_to_string_def = Define `
(id_to_string (Short x) = x) ∧
(id_to_string (Long x y) = x ++ "." ++ y)`;

val lookup_st_ex_def = Define `
(lookup_st_ex pr x [] = failwith ("failed lookup: " ++ pr x)) ∧
(lookup_st_ex pr x ((y,v)::e) =
  if x = y then
    return v
  else
    lookup_st_ex pr x e)`;

val _ = Hol_datatype `
infer_st = <| next_uvar : num; 
              subst : 'a |>`;

val fresh_uvar_def = Define `
(fresh_uvar : ('b infer_st, infer_t, α) M) =
  \s. (Success (Infer_Tuvar s.next_uvar), s with <| next_uvar := s.next_uvar + 1 |>)`;

val n_fresh_uvar_def = Define  `
n_fresh_uvar (n:num) =
  if n = 0 then
    return []
  else
    do v <- fresh_uvar;
       vs <- n_fresh_uvar (n - 1);
       return (v::vs)
    od`;

val init_infer_state_def = Define `
  (init_infer_state : (num |-> infer_t) infer_st) = <| next_uvar := 0; subst := FEMPTY |>`;

val init_state_def = Define `
init_state =
  \st.
    (Success (), init_infer_state)`;

val add_constraint_def = Define `
add_constraint t1 t2 =
  \st. 
    case t_unify st.subst t1 t2 of
      | NONE =>
          (Failure "Type mismatch", st)
      | SOME s =>
          (Success (), st with <| subst := s |>)`;

val add_constraints_def = Define `
(add_constraints [] [] =
  return ()) ∧
(add_constraints (t1::ts1) (t2::ts2) =
  do () <- add_constraint t1 t2;
     () <- add_constraints ts1 ts2;
     return ()
  od) ∧
(add_constraints _ _ =
  failwith "Bad call to add_constraints")`;

val get_next_uvar_def = Define `
get_next_uvar =
  \st. (Success st.next_uvar, st)`;

val apply_subst_def = Define `
apply_subst t =
  do st <- read;
     return (t_walkstar st.subst t)
  od`;

val apply_subst_list_def = Define `
apply_subst_list ts =
  do st <- read;
     return (MAP (t_walkstar st.subst) ts)
  od`;

(* Generalise the unification variables greater than m, starting at deBruijn index n.
 * Return how many were generalised, the generalised type, and a substitution
 * that describes the generalisation *)
val generalise_def = Define `
(generalise m n s (Infer_Tapp ts tc) =
  let (num_gen, s', ts') = generalise_list m n s ts in
    (num_gen, s', Infer_Tapp ts' tc)) ∧
(generalise m n s (Infer_Tuvar uv) =
  case FLOOKUP s uv of
    | SOME n => (0, s, Infer_Tvar_db n)
    | NONE =>
        if m ≤ uv then
          (1, s|+(uv,n), Infer_Tvar_db n)
        else
          (0, s, Infer_Tuvar uv)) ∧
(generalise m n s (Infer_Tvar_db k) =
    (0, s, Infer_Tvar_db k)) ∧
(generalise_list m n s [] = 
  (0,s,[])) ∧
(generalise_list m n s (t::ts) =
  let (num_gen, s', t') = generalise m n s t in
  let (num_gen', s'', ts') = generalise_list m (num_gen + n) s' ts in
    (num_gen+num_gen', s'', t'::ts'))`;

val infer_type_subst_def = tDefine "infer_type_subst" `
(infer_type_subst s (Tvar tv) =
  case lookup tv s of 
   | SOME t => t
   | NONE => Infer_Tvar_db 0) ∧ (* should not happen *)
(infer_type_subst s (Tvar_db n) =
  Infer_Tvar_db n) ∧
(infer_type_subst s (Tapp ts tn) =
  Infer_Tapp (MAP (infer_type_subst s) ts) tn)`
(WF_REL_TAC `measure (t_size o SND)` >>
 rw [] >>
 TRY (induct_on `ts`) >>
 rw [t_size_def] >>
 res_tac >>
 decide_tac);

val infer_deBruijn_subst_def = tDefine "infer_deBruijn_subst" `
(infer_deBruijn_subst s (Infer_Tvar_db n) =
  if n < LENGTH s then
    EL n s 
  else 
    (* should not happen *) 
    Infer_Tvar_db (n - LENGTH s)) ∧
(infer_deBruijn_subst s (Infer_Tapp ts tn) =
  Infer_Tapp (MAP (infer_deBruijn_subst s) ts) tn) ∧
(infer_deBruijn_subst s (Infer_Tuvar n) =
  Infer_Tuvar n)`
(WF_REL_TAC `measure (infer_t_size o SND)` >>
 rw [] >>
 TRY (induct_on `ts`) >>
 rw [infer_t_size_def] >>
 res_tac >>
 decide_tac);

val lookup_tenvC_st_ex_def = Define `
(lookup_tenvC_st_ex (Short cn) (cenvm, cenv) =
  lookup_st_ex (\x.x) cn cenv) ∧
(lookup_tenvC_st_ex (Long mn cn) (cenvm, cenv) =
  do cenv' <- lookup_st_ex (\x. id_to_string (Long x cn)) mn cenvm;
     lookup_st_ex (\x. id_to_string (Long mn x)) cn cenv'
  od)`;

val infer_p_def = tDefine "infer_p" `
(infer_p (cenv:tenvC) (Pvar n) =
  do t <- fresh_uvar;
     return (t, [(n,t)])
  od) ∧
(infer_p cenv (Plit (Bool b)) =
  return (Infer_Tapp [] TC_bool, [])) ∧
(infer_p cenv (Plit (IntLit i)) =
  return (Infer_Tapp [] TC_int, [])) ∧
(infer_p cenv (Plit (StrLit s)) =
  return (Infer_Tapp [] TC_string, [])) ∧
(infer_p cenv (Plit Unit) =
  return (Infer_Tapp [] TC_unit, [])) ∧
(infer_p cenv (Pcon cn_opt ps) =
  case cn_opt of 
    | NONE =>
        do (ts,tenv) <- infer_ps cenv ps;
           return (Infer_Tapp ts TC_tup, tenv)
        od
    | SOME cn =>
        do (tvs',ts,tn) <- lookup_tenvC_st_ex cn cenv;
           (ts'',tenv) <- infer_ps cenv ps;
           ts' <- n_fresh_uvar (LENGTH tvs');
           () <- add_constraints ts'' (MAP (infer_type_subst (ZIP(tvs',ts'))) ts);
           return (Infer_Tapp ts' (tid_exn_to_tc tn), tenv)
        od) ∧
(infer_p cenv (Pref p) =
  do (t,tenv) <- infer_p cenv p;
    return (Infer_Tapp [t] TC_ref, tenv)
  od) ∧
(infer_ps cenv [] =
  return ([], [])) ∧
(infer_ps cenv (p::ps) =
  do (t, tenv) <- infer_p cenv p; 
     (ts, tenv') <- infer_ps cenv ps; 
     return (t::ts, tenv'++tenv)
  od)`
(WF_REL_TAC `measure (\x. case x of INL (_,p) => pat_size p 
                                  | INR (_,ps) => pat1_size ps)` >>
 rw []);

val infer_p_ind = fetch "-" "infer_p_ind"

val constrain_uop_def = Define `
constrain_uop uop t =
  case uop of
   | Opref => return (Infer_Tapp [t] TC_ref)
   | Opderef =>
       do uvar <- fresh_uvar;
          () <- add_constraint t (Infer_Tapp [uvar] TC_ref);
          return uvar
       od`;

val constrain_op_def = Define `
constrain_op op t1 t2 =
  case op of
   | Opn opn =>
       do () <- add_constraint t1 (Infer_Tapp [] TC_int);
          () <- add_constraint t2 (Infer_Tapp [] TC_int);
          return (Infer_Tapp [] TC_int)
       od
   | Opb opb => 
       do () <- add_constraint t1 (Infer_Tapp [] TC_int);
          () <- add_constraint t2 (Infer_Tapp [] TC_int);
          return (Infer_Tapp [] TC_bool)
       od
   | Equality =>
       do () <- add_constraint t1 t2;
          return (Infer_Tapp [] TC_bool)
       od
   | Opapp =>
       do uvar <- fresh_uvar;
          () <- add_constraint t1 (Infer_Tapp [t2;uvar] TC_fn);
          return uvar
       od
   | Opassign =>
       do () <- add_constraint t1 (Infer_Tapp [t2] TC_ref);
          return (Infer_Tapp [] TC_unit)
       od`;

val infer_e_def = tDefine "infer_e" `
(infer_e menv (cenv : tenvC) env (Raise e) =
  do t2 <- infer_e menv cenv env e;
     () <- add_constraint t2 (Infer_Tapp [] TC_exn);
     t1 <- fresh_uvar;
     return t1
  od) ∧
(infer_e menv cenv env (Handle e pes) =
  if pes = [] then
    failwith "Empty pattern match"
  else
    do t1 <- infer_e menv cenv env e;
       () <- infer_pes menv cenv env pes (Infer_Tapp [] TC_exn) t1;
       return t1
    od) ∧
(infer_e menv cenv tenv (Lit (Bool b)) =
  return (Infer_Tapp [] TC_bool)) ∧
(infer_e menv cenv tenv (Lit (IntLit i)) =
  return (Infer_Tapp [] TC_int)) ∧
(infer_e menv cenv tenv (Lit (StrLit s)) =
  return (Infer_Tapp [] TC_string)) ∧
(infer_e menv cenv tenv (Lit Unit) =
  return (Infer_Tapp [] TC_unit)) ∧
(infer_e menv cenv env (Var (Short n)) =
  do (tvs,t) <- lookup_st_ex (\x.x) n env;
     uvs <- n_fresh_uvar tvs;
     return (infer_deBruijn_subst uvs t)
  od) ∧
(infer_e menv cenv env (Var (Long mn n)) =
  do env' <- lookup_st_ex (\x. id_to_string (Long x n)) mn menv;
     (tvs,t) <- lookup_st_ex (\x. id_to_string (Long mn x)) n env';
     uvs <- n_fresh_uvar tvs;
     return (infer_deBruijn_subst uvs t)
  od) ∧
(infer_e menv (cenv:tenvC) env (Con cn_opt es) =
  case cn_opt of
      NONE =>
       do ts <- infer_es menv cenv env es;
          return (Infer_Tapp ts TC_tup)
       od
    | SOME cn =>
       do (tvs',ts,tn) <- lookup_tenvC_st_ex cn cenv;
          ts'' <- infer_es menv cenv env es;
          ts' <- n_fresh_uvar (LENGTH tvs');
          () <- add_constraints ts'' (MAP (infer_type_subst (ZIP(tvs',ts'))) ts);
          return (Infer_Tapp ts' (tid_exn_to_tc tn))
       od) ∧
(infer_e menv cenv env (Fun x e) =
  do t1 <- fresh_uvar;
     t2 <- infer_e menv cenv (bind x (0,t1) env) e;
     return (Infer_Tapp [t1;t2] TC_fn)
  od) ∧
(infer_e menv cenv env (Uapp uop e) =
  do t <- infer_e menv cenv env e;
     t' <- constrain_uop uop t;
     return t'
  od) ∧
(infer_e menv cenv env (App op e1 e2) =
  do t1 <- infer_e menv cenv env e1;
     t2 <- infer_e menv cenv env e2;
     t3 <- constrain_op op t1 t2;
     return t3
  od) ∧
(infer_e menv cenv env (Log log e1 e2) =
  do t1 <- infer_e menv cenv env e1;
     t2 <- infer_e menv cenv env e2;
     () <- add_constraint t1 (Infer_Tapp [] TC_bool);
     () <- add_constraint t2 (Infer_Tapp [] TC_bool);
     return (Infer_Tapp [] TC_bool) 
  od) ∧
(infer_e menv cenv env (If e1 e2 e3) =
  do t1 <- infer_e menv cenv env e1;
     () <- add_constraint t1 (Infer_Tapp [] TC_bool);
     t2 <- infer_e menv cenv env e2;
     t3 <- infer_e menv cenv env e3;
     () <- add_constraint t2 t3;
     return t2
  od) ∧
(infer_e menv cenv env (Mat e pes) =
  if pes = [] then
    failwith "Empty pattern match"
  else
    do t1 <- infer_e menv cenv env e;
       t2 <- fresh_uvar;
       () <- infer_pes menv cenv env pes t1 t2;
       return t2
  od) ∧
(infer_e menv cenv env (Let x e1 e2) =
(* Don't do polymorphism for non-top-level lets 
  if is_value e1 then
    do n <- get_next_uvar;
       t1 <- infer_e menv cenv env e1;
       t1' <- apply_subst t1;
       (num_gen,s,t1'') <- return (generalise n 0 FEMPTY t1');
       t2 <- infer_e menv cenv (bind x (num_gen,t1'') env) e2;
       return t2
    od
  else
    *)
    do t1 <- infer_e menv cenv env e1;
       t2 <- infer_e menv cenv (bind x (0,t1) env) e2;
       return t2
    od) ∧
(* Don't do polymorphism for non-top-level let recs
(infer_e menv cenv env (Letrec funs e) =
  do () <- guard (ALL_DISTINCT (MAP FST funs)) "Duplicate function name variable";
     next <- get_next_uvar;
     uvars <- n_fresh_uvar (LENGTH funs);
     env' <- return (merge (list$MAP2 (\(f,x,e) uvar. (f,(0,uvar))) funs uvars) env);
     funs_ts <- infer_funs menv cenv env' funs;
     () <- add_constraints uvars funs_ts;
     ts <- apply_subst_list uvars;
     (num_gen,s,ts') <- return (generalise_list next 0 FEMPTY ts);
     env'' <- return (merge (list$MAP2 (\(f,x,e) t. (f,(num_gen,t))) funs ts') env);
     t <- infer_e menv cenv env'' e;
     return t
  od) ∧
  *)
(infer_e menv cenv env (Letrec funs e) =
  do () <- guard (ALL_DISTINCT (MAP FST funs)) "Duplicate function name";
     uvars <- n_fresh_uvar (LENGTH funs);
     env' <- return (merge (list$MAP2 (\(f,x,e) uvar. (f,(0,uvar))) funs uvars) env);
     funs_ts <- infer_funs menv cenv env' funs;
     () <- add_constraints uvars funs_ts;
     t <- infer_e menv cenv env' e;
     return t
  od) ∧
(infer_es menv cenv env [] =
  return []) ∧
(infer_es menv cenv env (e::es) =
  do t <- infer_e menv cenv env e;
     ts <- infer_es menv cenv env es;
     return (t::ts)
  od) ∧
(infer_pes menv cenv env [] t1 t2 =
   return ()) ∧
(infer_pes menv cenv env ((p,e)::pes) t1 t2 =
  do (t1', env') <- infer_p cenv p;
     () <- guard (ALL_DISTINCT (MAP FST env')) "Duplicate pattern variable";
     () <- add_constraint t1 t1';
     t2' <- infer_e menv cenv (merge (MAP (\(n,t). (n,(0,t))) env') env) e;
     () <- add_constraint t2 t2';
     () <- infer_pes menv cenv env pes t1 t2;
     return ()
  od) ∧
(infer_funs menv cenv env [] = return []) ∧
(infer_funs menv cenv env ((f, x, e)::funs) =
  do uvar <- fresh_uvar;
     t <- infer_e menv cenv (bind x (0,uvar) env) e;
     ts <- infer_funs menv cenv env funs;
     return (Infer_Tapp [uvar;t] TC_fn::ts)
  od)`
(WF_REL_TAC `measure (\x. case x of | INL (_,_,_,e) => exp_size e
                                    | INR (INL (_,_,_,es)) => exp6_size es
                                    | INR (INR (INL (_,_,_,pes,_,_))) => exp3_size pes
                                    | INR (INR (INR (_,_,_,funs))) => exp1_size funs)` >>
 rw []);

val infer_d_def = Define `
(infer_d mn tdecs menv cenv env (Dlet p e) = 
  do () <- init_state;
     n <- get_next_uvar;
     t1 <- infer_e menv cenv env e;
     (t2,env') <- infer_p cenv p;
     () <- guard (ALL_DISTINCT (MAP FST env')) "Duplicate pattern variable";
     () <- add_constraint t1 t2;
     ts <- apply_subst_list (MAP SND env');
     (num_tvs, s, ts') <- return (generalise_list n 0 FEMPTY ts);
     () <- guard (num_tvs = 0 ∨ is_value e) "Value restriction violated";
     return (tdecs, [], ZIP (MAP FST env', MAP (\t. (num_tvs, t)) ts'))
  od) ∧
(infer_d mn tdecs menv cenv env (Dletrec funs) =
  do () <- guard (ALL_DISTINCT (MAP FST funs)) "Duplicate function name";
     () <- init_state;
     next <- get_next_uvar;
     uvars <- n_fresh_uvar (LENGTH funs);
     env' <- return (merge (list$MAP2 (\(f,x,e) uvar. (f,(0,uvar))) funs uvars) env);
     funs_ts <- infer_funs menv cenv env' funs;
     () <- add_constraints uvars funs_ts;
     ts <- apply_subst_list uvars;
     (num_gen,s,ts') <- return (generalise_list next 0 FEMPTY ts);
     return (tdecs, [], list$MAP2 (\(f,x,e) t. (f,(num_gen,t))) funs ts')
  od) ∧
(infer_d mn tdecs menv cenv env (Dtype tdefs) =
  if check_ctor_tenv mn cenv tdefs then
    return (tdecs, build_ctor_tenv mn tdefs, [])
  else
    failwith "Bad type definition") ∧
(infer_d mn tdecs menv cenv env (Dexn cn ts) =
  if check_exn_tenv mn cenv cn ts then
    return (tdecs, bind cn ([], ts, TypeExn (mk_id mn cn) emp, [])
  else
    failwith "Bad type definition")`;

val infer_ds_def = Define `
(infer_ds mn menv cenv env [] =
  return ([],[])) ∧
(infer_ds mn menv cenv env (d::ds) =
  do
    (cenv',env') <- infer_d mn menv cenv env d;
    (cenv'',env'') <- infer_ds mn menv (merge_tenvC ([],cenv') cenv) (env' ++ env) ds;
    return (merge cenv'' cenv', env'' ++ env')
  od)`;

val t_to_freevars_def = Define `
(t_to_freevars (Tvar tn) = 
  return [tn]) ∧
(t_to_freevars (Tvar_db _) = 
  failwith "deBruijn index in type definition") ∧
(t_to_freevars (Tapp ts tc) =
  ts_to_freevars ts) ∧
(ts_to_freevars [] = return []) ∧
(ts_to_freevars (t::ts) =
  do fvs1 <- t_to_freevars t;
     fvs2 <- ts_to_freevars ts;
     return (fvs1++fvs2)
  od)`;

val check_specs_def = Define `
(check_specs mn cenv env [] =
  return (cenv,env)) ∧
(check_specs mn cenv env (Sval x t::specs) =
  do fvs <- t_to_freevars t;
     fvs' <- return (nub fvs);
     check_specs mn cenv (bind x (LENGTH fvs', infer_type_subst (ZIP (fvs', MAP Infer_Tvar_db (COUNT_LIST (LENGTH fvs')))) t) env) specs
  od) ∧
(check_specs mn cenv env (Stype td :: specs) =
  do () <- guard (check_ctor_tenv mn ((emp,cenv):tenvC) td) "Bad type definition";
     check_specs mn (merge (build_ctor_tenv mn td) cenv) env specs
  od) ∧
(check_specs mn cenv env (Sexn cn ts :: specs) =
  do () <- guard (check_exn_tenv mn ((emp,cenv):tenvC) cn ts) "Bad exception definition";
     check_specs mn (bind cn ([], ts, TypeExn mn) cenv) env specs
  od) ∧
(check_specs mn cenv env (Stype_opq tvs tn :: specs) =
  do () <- guard (EVERY (\(cn,(x,y,tn')). TypeId (mk_id mn tn) ≠ tn') cenv) "Duplicate type definition";
     () <- guard (ALL_DISTINCT tvs) "Duplicate type variables";
     check_specs mn cenv env specs
  od)`;

val check_flat_weakC_def = Define `
(check_flat_weakC cenv_impl cenv_spec =
  EVERY (\(cn, (tvs_spec, ts_spec, tn_spec)).
            case lookup cn cenv_impl of
              | NONE => F
              | SOME (tvs_impl,ts_impl,tn_impl) =>
                  (tn_spec = tn_impl) ∧ 
                  (tvs_spec = tvs_impl) ∧
                  (ts_spec = ts_impl))
        cenv_spec)`;

val check_weakE_def = Define `
(check_weakE env_impl [] = return ()) ∧
(check_weakE env_impl ((n, (tvs_spec, t_spec)) :: env_spec) =
  case lookup n env_impl of
    | NONE => failwith "Signature mismatch"
    | SOME (tvs_impl,t_impl) =>
        do () <- init_state;
           uvs <- n_fresh_uvar tvs_impl;
           t <- return (infer_deBruijn_subst uvs t_impl);
           () <- add_constraint t_spec t;
           check_weakE env_impl env_spec
        od)`;

val check_signature_def = Define `
(check_signature mn cenv env NONE = 
  return (cenv, env)) ∧
(check_signature mn cenv env (SOME specs) =
  do (cenv', env') <- check_specs mn [] [] specs;
     () <- guard (check_flat_weakC cenv cenv') "Signature mismatch";
     () <- check_weakE env env';
     return (cenv',env')
  od)`;

val infer_top_def = Define `
(infer_top menv cenv env (Tdec d) =
  do
    (cenv',env') <- infer_d NONE menv cenv env d;
    return (emp, (emp,cenv'), env')
  od) ∧
(infer_top menv cenv env (Tmod mn spec ds1) =
  do
    () <- guard (~MEM mn (MAP FST menv)) ("Duplicate module: " ++ mn);
    (cenv',env') <- infer_ds (SOME mn) menv cenv env ds1;
    (cenv'',env'') <- check_signature (SOME mn) cenv' env' spec;
    return ([(mn,env'')], ([(mn,cenv'')],emp), emp)
  od)`;

val infer_prog_def = Define `
(infer_prog menv cenv env [] =
  return ([],([],[]),[])) ∧
(infer_prog menv cenv env (top::ds) =
  do
    (menv',cenv',env') <- infer_top menv cenv env top;
    (menv'', cenv'', env'') <- infer_prog menv (merge_tenvC cenv' cenv) (env' ++ env) ds;
    return (menv''++menv', merge_tenvC cenv'' cenv', env'' ++ env')
  od)`;

val Infer_Tfn_def = Define `
Infer_Tfn t1 t2 = Infer_Tapp [t1;t2] TC_fn`;

val Infer_Tint = Define `
Infer_Tint = Infer_Tapp [] TC_int`;

val Infer_Tbool = Define `
Infer_Tbool = Infer_Tapp [] TC_bool`;

val Infer_Tunit = Define `
Infer_Tunit = Infer_Tapp [] TC_unit`;

val Infer_Tref = Define `
Infer_Tref t = Infer_Tapp [t] TC_ref`;

val init_type_env_def = Define `
init_type_env =
  [("+", (0:num, Infer_Tfn Infer_Tint (Infer_Tfn Infer_Tint Infer_Tint)));
   ("-", (0, Infer_Tfn Infer_Tint (Infer_Tfn Infer_Tint Infer_Tint)));
   ("*", (0, Infer_Tfn Infer_Tint (Infer_Tfn Infer_Tint Infer_Tint)));
   ("div", (0, Infer_Tfn Infer_Tint (Infer_Tfn Infer_Tint Infer_Tint)));
   ("mod", (0, Infer_Tfn Infer_Tint (Infer_Tfn Infer_Tint Infer_Tint)));
   ("<", (0, Infer_Tfn Infer_Tint (Infer_Tfn Infer_Tint Infer_Tbool)));
   (">", (0, Infer_Tfn Infer_Tint (Infer_Tfn Infer_Tint Infer_Tbool)));
   ("<=", (0, Infer_Tfn Infer_Tint (Infer_Tfn Infer_Tint Infer_Tbool)));
   (">=", (0, Infer_Tfn Infer_Tint (Infer_Tfn Infer_Tint Infer_Tbool)));
   ("=", (1, Infer_Tfn (Infer_Tvar_db 0) (Infer_Tfn (Infer_Tvar_db 0) Infer_Tbool)));
   (":=", (1, Infer_Tfn (Infer_Tref (Infer_Tvar_db 0)) (Infer_Tfn (Infer_Tvar_db 0) Infer_Tunit)));
   ("~", (0, Infer_Tfn Infer_Tint Infer_Tint));
   ("!", (1, Infer_Tfn (Infer_Tref (Infer_Tvar_db 0)) (Infer_Tvar_db 0)));
   ("ref", (1, Infer_Tfn (Infer_Tvar_db 0) (Infer_Tref (Infer_Tvar_db 0))))]`;

(* The following aren't needed to run the inferencer, but are useful in the proofs
 * about it *)

val infer_deBruijn_inc_def = tDefine "infer_deBruijn_inc" `
(infer_deBruijn_inc n (Infer_Tvar_db m) = 
  Infer_Tvar_db (m + n)) ∧
(infer_deBruijn_inc n (Infer_Tapp ts tn) =
  Infer_Tapp (MAP (infer_deBruijn_inc n) ts) tn) ∧
(infer_deBruijn_inc n (Infer_Tuvar m) = 
  Infer_Tuvar m)`
(WF_REL_TAC `measure (infer_t_size o SND)` >>
 rw [] >>
 induct_on `ts` >>
 rw [infer_t_size_def] >>
 res_tac >>
 decide_tac);

val infer_subst_def = tDefine "infer_subst" `
(infer_subst s (Infer_Tvar_db n) = Infer_Tvar_db n) ∧
(infer_subst s (Infer_Tapp ts tc) = Infer_Tapp (MAP (infer_subst s) ts) tc) ∧
(infer_subst s (Infer_Tuvar n) =
  case FLOOKUP s n of
      NONE => Infer_Tuvar n
    | SOME m => Infer_Tvar_db m)`
(wf_rel_tac `measure (infer_t_size o SND)` >>
 rw [] >>
 induct_on `ts` >>
 srw_tac[ARITH_ss] [infer_t_size_def] >>
 res_tac >>
 decide_tac);

val pure_add_constraints_def = Define `
(pure_add_constraints s [] s' = (s = s')) ∧
(pure_add_constraints s1 ((t1,t2)::rest) s' = 
  ?s2. (t_unify s1 t1 t2 = SOME s2) ∧
       pure_add_constraints s2 rest s')`;

val check_t_def = tDefine "check_t" `
(check_t n uvars (Infer_Tuvar v) = (v ∈ uvars)) ∧
(check_t n uvars (Infer_Tvar_db n') = 
  (n' < n)) ∧
(check_t n uvars (Infer_Tapp ts tc) = EVERY (check_t n uvars) ts)`
(WF_REL_TAC `measure (infer_t_size o SND o SND)` >>
 rw [] >>
 induct_on `ts` >>
 rw [infer_t_size_def] >>
 res_tac >>
 decide_tac);

val check_env_def = Define `
check_env uvars env =
  EVERY (\(x, (tvs,t)). check_t tvs uvars t) env`;

val check_menv_def = Define `
check_menv menv =
  EVERY (\(mn,env). EVERY (\(x, (tvs,t)). check_t tvs {} t) env) menv`;

val check_flat_cenv_def = Define `
check_flat_cenv (cenv : flat_tenvC) = 
  EVERY (\(cn,(tvs,ts,t)). EVERY (check_freevars 0 tvs) ts) cenv`;

val check_cenv_def = Define `
check_cenv (mcenv, cenv) ⇔
  EVERY (\(cn,cenv'). check_flat_cenv cenv') mcenv ∧
  check_flat_cenv cenv`;

val check_s_def = Define `
check_s tvs uvs s = 
  !uv. uv ∈ FDOM s ⇒ check_t tvs uvs (s ' uv)`;

(* Adding the constraints extra_constraints moves the constraint set from s1 to
 * s2, and s2 is required to be complete in that it assigns to (at least) all
 * the uvars ≤ next_uvar, and when we apply it to any uvar, we get back a type
 * without any uvars in it. *)
val sub_completion_def = Define `
sub_completion tvs next_uvar s1 extra_constraints s2 =
  (pure_add_constraints s1 extra_constraints s2 ∧
   (count next_uvar SUBSET FDOM s2) ∧
   (!uv. uv ∈ FDOM s2 ⇒ check_t tvs {} (t_walkstar s2 (Infer_Tuvar uv))))`;

val _ = export_theory ();

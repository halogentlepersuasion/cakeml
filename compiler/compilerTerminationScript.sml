open HolKernel boolLib boolSimps bossLib Defn pairTheory pred_setTheory listTheory finite_mapTheory state_transformerTheory lcsymtacs
open terminationTheory compilerLibTheory intLangTheory toIntLangTheory toBytecodeTheory compilerTheory printerTheory bytecodeTheory
open modLangTheory conLangTheory intLang4Theory;
val _ = new_theory "compilerTermination"

(* size helper theorems *)

val MEM_pair_MAP = store_thm(
"MEM_pair_MAP",
``MEM (a,b) ls ==> MEM a (MAP FST ls) /\ MEM b (MAP SND ls)``,
rw[MEM_MAP,pairTheory.EXISTS_PROD] >> PROVE_TAC[])

val tac = Induct >- rw[Cexp_size_def,Cv_size_def,ov_size_def] >> srw_tac [ARITH_ss][Cexp_size_def,Cv_size_def,ov_size_def]
fun tm t1 t2 =  ``∀ls. ^t1 ls = SUM (MAP ^t2 ls) + LENGTH ls``
fun size_thm name t1 t2 = store_thm(name,tm t1 t2,tac)
val Cexp1_size_thm = size_thm "Cexp1_size_thm" ``Cexp1_size`` ``Cexp2_size``
val Cexp4_size_thm = size_thm "Cexp4_size_thm" ``Cexp4_size`` ``Cexp_size``
val Cv1_size_thm = size_thm "Cv1_size_thm" ``Cv1_size`` ``Cv_size``
val ov1_size_thm = size_thm "ov1_size_thm" ``ov1_size`` ``ov_size``

val SUM_MAP_Cexp3_size_thm = store_thm(
"SUM_MAP_Cexp3_size_thm",
``∀env. SUM (MAP Cexp3_size env) =
  SUM (MAP FST env)
+ SUM (MAP Cexp_size (MAP SND env))
+ LENGTH env``,
Induct >- rw[Cexp_size_def] >> Cases >>
srw_tac[ARITH_ss][Cexp_size_def])

val SUM_MAP_Cexp2_size_thm = store_thm("SUM_MAP_Cexp2_size_thm",
  ``∀defs. SUM (MAP Cexp2_size defs) =
    SUM (MAP (option_size (pair_size (λx. x) (pair_size (list_size ccbind_size) (pair_size (list_size (λx. x)) (list_size (λx. x))))) o FST) defs) +
    SUM (MAP (Cexp3_size o SND) defs) +
    LENGTH defs``,
  Induct >- rw[Cexp_size_def] >>
  qx_gen_tac`h` >> PairCases_on`h` >>
  Cases_on`h0`>>srw_tac[ARITH_ss][Cexp_size_def,basicSizeTheory.pair_size_def,arithmeticTheory.ADD1,basicSizeTheory.option_size_def])

val list_size_thm = store_thm(
"list_size_thm",
``∀f ls. list_size f ls = SUM (MAP f ls) + LENGTH ls``,
gen_tac >> Induct >> srw_tac[ARITH_ss][list_size_def])

val bc_value1_size_thm = store_thm(
"bc_value1_size_thm",
``∀ls. bc_value1_size ls = SUM (MAP bc_value_size ls) + LENGTH ls``,
Induct >- rw[bytecodeTheory.bc_value_size_def] >>
srw_tac [ARITH_ss][bytecodeTheory.bc_value_size_def])

(* termination proofs *)

fun register name (def,ind) = let
  val _ = save_thm(name^"_def", def)
  val _ = save_thm(name^"_ind", ind)
  val _ = computeLib.add_persistent_funs [name^"_def"]
in (def,ind) end

val (free_vars_def, free_vars_ind) = register "free_vars" (
  tprove_no_defn ((free_vars_def,free_vars_ind),
  WF_REL_TAC `inv_image $< (λx. case x of
    | INL e => Cexp_size e
    | INR (INL es) => Cexp4_size es
    | INR (INR (INL (n,defs))) => Cexp1_size defs
    | INR (INR (INR (n,def))) => Cexp2_size def)`))

val (no_closures_def, no_closures_ind) = register "no_closures" (
  tprove_no_defn ((no_closures_def, no_closures_ind),
  WF_REL_TAC `measure Cv_size` >>
  rw[Cv1_size_thm] >>
  imp_res_tac SUM_MAP_MEM_bound >>
  pop_assum (qspec_then `Cv_size` mp_tac) >>
  srw_tac[ARITH_ss][]))

val (Cv_to_ov_def,Cv_to_ov_ind) = register "Cv_to_ov" (
  tprove_no_defn ((Cv_to_ov_def,Cv_to_ov_ind),
  WF_REL_TAC `measure (Cv_size o SND o SND)` >>
  rw[Cv1_size_thm] >>
  Q.ISPEC_THEN `Cv_size` imp_res_tac SUM_MAP_MEM_bound >>
  srw_tac[ARITH_ss][]))

val (v_to_ov_def,v_to_ov_ind) = register "v_to_ov" (
  tprove_no_defn ((v_to_ov_def,v_to_ov_ind),
  WF_REL_TAC `measure (v_size o SND)` >>
  rw[SIMP_RULE (std_ss) [vs_size_def] vs_size_thm] >>
  Q.ISPEC_THEN `v_size` imp_res_tac SUM_MAP_MEM_bound >>
  srw_tac[ARITH_ss][]))

val (mkshift_def,mkshift_ind) = register "mkshift" (
  tprove_no_defn ((mkshift_def,mkshift_ind),
  WF_REL_TAC `measure (Cexp_size o SND o SND)` >>
  srw_tac[ARITH_ss][Cexp4_size_thm,Cexp1_size_thm,SUM_MAP_Cexp3_size_thm] >>
  Q.ISPEC_THEN`Cexp_size`imp_res_tac SUM_MAP_MEM_bound >>
  srw_tac[ARITH_ss][] >>
  imp_res_tac MEM_pair_MAP >>
  Q.ISPEC_THEN`Cexp2_size`imp_res_tac SUM_MAP_MEM_bound >>
  fsrw_tac[ARITH_ss][Cexp_size_def]))

val (exp_to_Cexp_def,exp_to_Cexp_ind) = register "exp_to_Cexp" (
  tprove_no_defn ((exp_to_Cexp_def,exp_to_Cexp_ind),
  WF_REL_TAC `inv_image $< (λx. case x of
    | INL e => exp_i4_size e
    | INR es => exp_i41_size es)`))

val (compile_envref_def, compile_envref_ind) = register "compile_envref" (
  tprove_no_defn ((compile_envref_def, compile_envref_ind),
  WF_REL_TAC `measure (λp. case p of (_,_,CCEnv _) => 0 | (_,_,CCRef _) => 1)`))

(*
val [s1,s2,s3,s4] = CONJUNCTS stackshift_def
val stackshift_alt = prove(
``stackshift j k =
  if k = 0 then ^(rhs(concl(Q.SPEC`j`s1)))
  else if j = 0 then ^(rhs(concl(Q.SPEC`k-1`s2)))
  else if j = 1 then ^(rhs(concl(Q.SPEC`k-1`s3)))
  else ^(rhs(concl(Q.SPECL[`j-2`,`k-1`]s4)))``,
SIMP_TAC(srw_ss()++ARITH_ss)[arithmeticTheory.ADD1] THEN
Cases_on`k`THEN ASM_SIMP_TAC(srw_ss())[stackshift_def] THEN
Cases_on`j`THEN ASM_SIMP_TAC(srw_ss())[stackshift_def] THEN
Cases_on`n'`THEN ASM_SIMP_TAC(srw_ss())[stackshift_def])
|> SIMP_RULE (srw_ss()++ARITH_ss)[arithmeticTheory.ADD1]
val _ = register "stackshift"(stackshift_alt,stackshift_ind)

val [s1,s2] = CONJUNCTS stackshiftaux_def
val stackshiftaux_alt = prove(
``stackshiftaux i j k =
  if i = 0 then ^(rhs(concl(Q.SPECL[`k`,`j`]s1)))
  else ^(rhs(concl(Q.SPECL[`i-1`,`k`,`j`]s2)))``,
SIMP_TAC(srw_ss()++ARITH_ss)[arithmeticTheory.ADD1] THEN
Cases_on`i`THEN ASM_SIMP_TAC(srw_ss())[stackshiftaux_def])
|> SIMP_RULE (srw_ss()++ARITH_ss)[arithmeticTheory.ADD1]
val _ = save_thm("stackshiftaux_alt",stackshiftaux_alt)

val _ = computeLib.del_persistent_consts[``stackshift``,``stackshiftaux``]
val _ = computeLib.add_persistent_funs["stackshiftaux_alt","stackshift_alt"]
*)

val (compile_def, compile_ind) = register "compile" (
  tprove_no_defn ((compile_def, compile_ind),
  WF_REL_TAC `inv_image ($< LEX $<) (λx. case x of
       | INL (env,t,sz,s,e) => (Cexp_size e, 3:num)
       | INR (INL (env,t,sz,e,n,s,0))=> (Cexp_size e, 4)
       | INR (INL (env,t,sz,e,n,s,ns))=> (Cexp_size e + ns, 1)
       | INR (INR (env,sz,s,es))=> (SUM (MAP Cexp_size es), 3 + LENGTH es)) ` >>
  srw_tac[ARITH_ss][] >>
  srw_tac[ARITH_ss][Cexp1_size_thm,Cexp4_size_thm,Cexp_size_def,list_size_thm,SUM_MAP_Cexp3_size_thm] >>
  BasicProvers.CASE_TAC >> fsrw_tac[ARITH_ss][] >>
  BasicProvers.CASE_TAC >> fsrw_tac[ARITH_ss][]))

val zero_vars_def = Lib.with_flag (computeLib.auto_import_definitions, false) (tDefine "zero_vars"`
  (zero_vars (CRaise e) = CRaise (zero_vars e)) ∧
  (zero_vars (CHandle e1 e2) = CHandle (zero_vars e1) (zero_vars e2)) ∧
  (zero_vars (CVar _) = CVar 0) ∧
  (zero_vars (CGvar n) = CGvar n) ∧
  (zero_vars (CLit c) = CLit c) ∧
  (zero_vars (CCon cn es) = CCon cn (zero_vars_list es)) ∧
  (zero_vars (CLet bd e1 e2) = CLet bd (zero_vars e1) (zero_vars e2)) ∧
  (zero_vars (CLetrec defs e) = CLetrec (zero_vars_defs defs) (zero_vars e)) ∧
  (zero_vars (CCall ck e es) = CCall ck (zero_vars e) (zero_vars_list es)) ∧
  (zero_vars (CPrim1 p1 e2) = CPrim1 p1 (zero_vars e2)) ∧
  (zero_vars (CPrim2 p2 e1 e2) = CPrim2 p2 (zero_vars e1) (zero_vars e2)) ∧
  (zero_vars (CUpd e1 e2) = CUpd (zero_vars e1) (zero_vars e2)) ∧
  (zero_vars (CIf e1 e2 e3) = CIf (zero_vars e1) (zero_vars e2) (zero_vars e3)) ∧
  (zero_vars (CExtG n) = CExtG n) ∧
  (zero_vars_list [] = []) ∧
  (zero_vars_list (e::es) = (zero_vars e)::(zero_vars_list es)) ∧
  (zero_vars_defs [] = []) ∧
  (zero_vars_defs (def::defs) = (zero_vars_def def)::(zero_vars_defs defs)) ∧
  (zero_vars_def (NONE,(xs,b)) = (NONE,(xs,zero_vars b))) ∧
  (zero_vars_def (SOME x,y) = (SOME x,y))`)
  (WF_REL_TAC`inv_image $< (λx. case x of INL e => Cexp_size e |
    INR (INL es) => Cexp4_size es |
    INR (INR (INL defs)) => Cexp1_size defs |
    INR(INR(INR def)) => Cexp2_size def)`)

val zero_vars_list_MAP = prove(
  ``(∀ls. (zero_vars_list ls = MAP (zero_vars) ls)) ∧
    (∀ls. (zero_vars_defs ls = MAP (zero_vars_def) ls))``,
  conj_tac >> Induct >> rw[zero_vars_def])
val _ = augment_srw_ss[rewrites [zero_vars_def,zero_vars_list_MAP]]

val zero_vars_mkshift = prove(
  ``∀f k e. zero_vars (mkshift f k e) = zero_vars e``,
  ho_match_mp_tac mkshift_ind >>
  rw[mkshift_def,MAP_MAP_o,combinTheory.o_DEF,LET_THM] >>
  lrw[MAP_EQ_f,UNCURRY] >>
  BasicProvers.CASE_TAC >>
  BasicProvers.CASE_TAC >> rw[] >>
  BasicProvers.CASE_TAC >> rw[] >>
  fsrw_tac[ARITH_ss][])
val _ = augment_srw_ss[rewrites [zero_vars_mkshift]]

val (label_closures_def,label_closures_ind) = register "label_closures" (
  tprove_no_defn ((label_closures_def, label_closures_ind),
  WF_REL_TAC`inv_image $< (λx. case x of
    | INL (ez,j,e) => Cexp_size (zero_vars e)
    | INR (INL (ez,j,es)) => Cexp4_size (zero_vars_list es)
    | INR (INR (ez,j,nz,k,defs)) => SUM (MAP Cexp2_size (MAP (zero_vars_def o ($, NONE)) defs)))` >>
  srw_tac[ARITH_ss][Cexp_size_def,SUM_MAP_Cexp3_size_thm,Cexp1_size_thm,SUM_MAP_Cexp2_size_thm,basicSizeTheory.pair_size_def] >- (
    simp[MAP_MAP_o,combinTheory.o_DEF] >>
    qmatch_abbrev_tac`a + (b + c) < d + ((2 * f) + (g + (h + 1:num)))` >>
    qsuff_tac`a ≤ f ∧ (b = 0) ∧ (c ≤ h)` >- simp[] >>
    unabbrev_all_tac >>
    conj_tac >- simp[rich_listTheory.LENGTH_FILTER_LEQ] >>
    conj_tac >- (
      simp[SUM_eq_0,MEM_MAP,MEM_FILTER] >>
      qx_gen_tac`a` >> fsrw_tac[DNF_ss][] >>
      qx_gen_tac`b` >>
      PairCases_on`b`>>simp[]>>
      simp[basicSizeTheory.option_size_def]) >>
    qmatch_abbrev_tac`SUM (MAP f (FILTER P defs)) ≤ SUM (MAP g defs)` >>
    `MAP f (FILTER P defs) = MAP g (FILTER P defs)` by (
      lrw[MAP_EQ_f,MEM_FILTER,Abbr`f`,Abbr`g`,Abbr`P`] >>
      PairCases_on`x`>>fs[]) >>
    pop_assum SUBST1_TAC >>
    Induct_on`defs` >> simp[] >>
    qx_gen_tac`x` >> PairCases_on`x` >>
    Cases_on`x0`>>simp[Abbr`P`,Abbr`g`]) >>
  fsrw_tac[ARITH_ss][bind_fv_def,LET_THM]))

val _ = map delete_const ["zero_vars","zero_vars_list","zero_vars_defs","zero_vars_def","zero_vars_UNION"]
val _ = delete_binding "zero_vars_ind"

val _ = register "free_labs" (
  tprove_no_defn ((free_labs_def, free_labs_ind),
  WF_REL_TAC`inv_image $< (λx. case x of
    | INL (ez,e) => Cexp_size e
    | INR (INL (ez,es)) => Cexp4_size es
    | INR (INR (INL (ez,nz,ix,ds))) => Cexp1_size ds
    | INR (INR (INR (ez,nz,ix,def))) => Cexp2_size def)`))

val _ = register "no_labs" (
  tprove_no_defn ((no_labs_def, no_labs_ind),
  WF_REL_TAC`inv_image $< (λx. case x of
    | INL (e) => Cexp_size e
    | INR (INL (es)) => Cexp4_size es
    | INR (INR (INL (ds))) => Cexp1_size ds
    | INR (INR (INR (def))) => Cexp2_size def)`))

val _ = register "all_labs" (
  tprove_no_defn ((all_labs_def, all_labs_ind),
  WF_REL_TAC`inv_image $< (λx. case x of
    | INL (e) => Cexp_size e
    | INR (INL (es)) => Cexp4_size es
    | INR (INR (INL (ds))) => Cexp1_size ds
    | INR (INR (INR (def))) => Cexp2_size def)`))

val (bv_to_ov_def,bv_to_ov_ind) = register "bv_to_ov" (
  tprove_no_defn ((bv_to_ov_def,bv_to_ov_ind),
  WF_REL_TAC `measure (bc_value_size o SND)` >>
  rw[bc_value1_size_thm] >>
  Q.ISPEC_THEN `bc_value_size` imp_res_tac SUM_MAP_MEM_bound >>
  srw_tac[ARITH_ss][]))

val (do_Ceq_def,do_Ceq_ind) = register "do_Ceq" (
  tprove_no_defn((do_Ceq_def,do_Ceq_ind),
  WF_REL_TAC`measure (\x. case x of INL (cv,_) => Cv_size cv | INR (cvs,_) => Cv1_size cvs)`));

val (exp_to_i1_def, exp_to_i1_ind) =
  tprove_no_defn ((exp_to_i1_def, exp_to_i1_ind),
  WF_REL_TAC `inv_image $< (\x. case x of INL (x,y,e) => exp_size e
                                        | INR (INL (x,y,es)) => exps_size es
                                        | INR (INR (INL (x,y,pes))) => pes_size pes
                                        | INR (INR (INR (x,y,funs))) => funs_size funs)` >>
  srw_tac [ARITH_ss] [size_abbrevs, astTheory.exp_size_def]);
val _ = register "exp_to_i1" (exp_to_i1_def,exp_to_i1_ind);

val (pmatch_i1_def, pmatch_i1_ind) =
  tprove_no_defn ((pmatch_i1_def, pmatch_i1_ind),
  WF_REL_TAC `inv_image $< (\x. case x of INL (a,x,p,y,z) => pat_size p
                                        | INR (a,x,ps,y,z) => pats_size ps)` >>
  srw_tac [ARITH_ss] [size_abbrevs, astTheory.pat_size_def]);
val _ = register "pmatch_i1" (pmatch_i1_def,pmatch_i1_ind);

val (do_eq_i1_def, do_eq_i1_ind) =
  tprove_no_defn ((do_eq_i1_def, do_eq_i1_ind),
  WF_REL_TAC `inv_image $< (\x. case x of INL (x,y) => v_i1_size x
                                        | INR (xs,ys) => v_i14_size xs)`);
val _ = register "do_eq_i1" (do_eq_i1_def,do_eq_i1_ind);

val (pat_to_i2_def, pat_to_i2_ind) =
  tprove_no_defn ((pat_to_i2_def, pat_to_i2_ind),
  WF_REL_TAC `inv_image $< (\(x,p). pat_size p)` >>
  srw_tac [ARITH_ss] [astTheory.pat_size_def] >>
  Induct_on `ps` >>
  srw_tac [ARITH_ss] [astTheory.pat_size_def] >>
  srw_tac [ARITH_ss] [astTheory.pat_size_def] >>
  res_tac >>
  decide_tac);
val _ = register "pat_to_i2" (pat_to_i2_def,pat_to_i2_ind);

val (exp_to_i2_def, exp_to_i2_ind) =
  tprove_no_defn ((exp_to_i2_def, exp_to_i2_ind),
  cheat);
  (*
  WF_REL_TAC `inv_image $< (\x. case x of INL (x,e) => exp_i1_size e
                                        | INR (INL (x,es)) => exp_i16_size es
                                        | INR (INR (INL (x,pes))) => exp_i13_size pes
                                        | INR (INR (INR (x,funs))) => exp_i11_size funs)` >>
  srw_tac [ARITH_ss] [exp_i1_size_def]);
  *)

val _ = register "exp_to_i2" (exp_to_i2_def,exp_to_i2_ind);

val (pmatch_i2_def, pmatch_i2_ind) =
  tprove_no_defn ((pmatch_i2_def, pmatch_i2_ind),
  WF_REL_TAC `inv_image $< (\x. case x of INL (a,x,p,y,z) => pat_i2_size p
                                        | INR (a,x,ps,y,z) => pat_i21_size ps)` >>
  srw_tac [ARITH_ss] [pat_i2_size_def]);
val _ = register "pmatch_i2" (pmatch_i2_def,pmatch_i2_ind);

val (do_eq_i2_def, do_eq_i2_ind) =
  tprove_no_defn ((do_eq_i2_def, do_eq_i2_ind),
  WF_REL_TAC `inv_image $< (\x. case x of INL (x,y) => v_i2_size x
                                        | INR (xs,ys) => v_i23_size xs)`);
val _ = register "do_eq_i2" (do_eq_i2_def,do_eq_i2_ind);

val (exp_to_i4_def, exp_to_i4_ind) =
  tprove_no_defn ((exp_to_i4_def, exp_to_i4_ind),
  WF_REL_TAC `inv_image $< (\x. case x of INL (bvs,e) => exp_exh_size e
                                        | INR (INL (bvs,es)) => exp_exh6_size es
                                        | INR (INR (INL (bvs,funs))) => exp_exh1_size funs
                                        | INR (INR (INR (bvs,pes))) => exp_exh3_size pes)`);
val _ = register "exp_to_i4" (exp_to_i4_def,exp_to_i4_ind);

val (pat_to_i4_def, pat_to_i4_ind) =
  tprove_no_defn ((pat_to_i4_def, pat_to_i4_ind),
  WF_REL_TAC `inv_image $< (\x. case x of INL p => pat_exh_size p
                                        | INR (n,ps) => pat_exh1_size ps)`);
val _ = register "pat_to_i4" (pat_to_i4_def,pat_to_i4_ind);

val (row_to_i4_def, row_to_i4_ind) =
  tprove_no_defn ((row_to_i4_def, row_to_i4_ind),
  WF_REL_TAC `inv_image $< (\x. case x of INL (bvs,p) => pat_exh_size p
                                        | INR (bvs,n,k,ps) => pat_exh1_size ps)`);
val _ = register "row_to_i4" (row_to_i4_def,row_to_i4_ind);

val (Let_Els_i4_def, Let_Els_i4_ind) =
  tprove_no_defn ((Let_Els_i4_def, Let_Els_i4_ind),
  WF_REL_TAC `measure (FST o SND)`);
val _ = register "Let_Els_i4" (Let_Els_i4_def,Let_Els_i4_ind);

val (do_eq_i4_def, do_eq_i4_ind) =
  tprove_no_defn ((do_eq_i4_def, do_eq_i4_ind),
  WF_REL_TAC`inv_image $< (\x. case x of INL (v1,v2) => v_i4_size v1
                                       | INR (vs1,vs2) => v_i41_size vs1)`);
val _ = register "do_eq_i4" (do_eq_i4_def,do_eq_i4_ind);


(* export rewrites *)
val _ = export_rewrites
  ["exp_to_i4_def"
  ,"intLang4.uop_to_i4_def"
  ,"intLang4.fo_i4_def"
  ,"intLang4.ground_i4_def"
  ,"intLang4.pure_uop_i4_def"
  ,"intLang4.pure_op_def"]

(* TODO: add missing *)
val _ = export_rewrites
["toBytecode.emit_def","toBytecode.get_label_def","toBytecode.emit_ceref_def","toBytecode.emit_ceenv_def"
,"toBytecode.prim1_to_bc_def","toBytecode.prim2_to_bc_def"
,"free_vars_def","no_closures_def"
,"Cv_to_ov_def","v_to_ov_def"
,"toBytecode.compile_varref_def","compile_envref_def"
,"mkshift_def"
,"label_closures_def"
,"intLang.doPrim2_def","intLang.CevalPrim2_def","intLang.CevalUpd_def","intLang.CevalPrim1_def"
,"free_labs_def","no_labs_def","all_labs_def"
,"do_Ceq_def"];

(*
val _ = export_rewrites
["toBytecode.emit_def","toBytecode.get_label_def","toBytecode.emit_ceref_def","toBytecode.emit_ceenv_def"
,"toBytecode.prim1_to_bc_def","toBytecode.prim2_to_bc_def","compiler.cmap_def","toIntLang.cbv_def"
,"toIntLang.remove_mat_vp_def","free_vars_def","no_closures_def"
,"Cv_to_ov_def","v_to_ov_def"
,"toBytecode.compile_varref_def","compile_envref_def"
,"mkshift_def"
,"label_closures_def"
,"toIntLang.Cpat_vars_def"
,"intLang.doPrim2_def","intLang.CevalPrim2_def","intLang.CevalUpd_def","intLang.CevalPrim1_def"
,"free_labs_def","no_labs_def","all_labs_def"
,"intLang.CDiv_excv_def","intLang.CBind_excv_def","intLang.CEq_excv_def"
,"intLang.CDiv_exc_def","intLang.CBind_exc_def","intLang.CEq_exc_def"
,"toIntLang.opn_to_prim2_def"
,"do_Ceq_def"];
*)

val _ = export_theory()

open HolKernel bossLib boolLib boolSimps listTheory pairTheory rich_listTheory pred_setTheory arithmeticTheory finite_mapTheory relationTheory sortingTheory stringTheory
open miscLib miscTheory bigStepTheory semanticPrimitivesTheory bigClockTheory replTheory terminationTheory
open bytecodeTheory bytecodeExtraTheory bytecodeEvalTheory bytecodeClockTheory bytecodeLabelsTheory bytecodeTerminationTheory
open conLangTheory intLangTheory toIntLangTheory toBytecodeTheory compilerTheory intLangExtraTheory modLangProofTheory conLangProofTheory decLangProofTheory exhLangProofTheory intLangProofTheory bytecodeProofTheory compilerTerminationTheory
open patLangProofTheory

val _ = new_theory"compilerProof"

(* TODO: remove

val good_v_def = tDefine"good_v"`
  (good_v (Litv _) ⇔ T) ∧
  (good_v (Conv _ vs) ⇔ good_vs vs) ∧
  (good_v (Closure (envM,envC,envE) _ _) ⇔
    good_envM envM ∧ good_envE envE) ∧
  (good_v (Recclosure (envM,envC,envE) funs f) ⇔
   good_envM envM ∧ good_envE envE ∧
   ALL_DISTINCT (MAP FST funs) ∧ MEM f (MAP FST funs)) ∧
  (good_v (Loc _) ⇔ T) ∧
  (good_vs [] ⇔ T) ∧
  (good_vs (v::vs) ⇔ good_v v ∧ good_vs vs) ∧
  (good_envE [] ⇔ T) ∧
  (good_envE ((_,v)::envE) ⇔ good_v v ∧ good_envE envE) ∧
  (good_envM [] ⇔ T) ∧
  (good_envM ((_,envE)::envM) ⇔ good_envE envE ∧ good_envM envM)`
(WF_REL_TAC`inv_image $< (\x. case x of
  | INL v => v_size v
  | INR (INL vs) => v7_size vs
  | INR (INR (INL envE)) => v5_size envE
  | INR (INR (INR envM)) => v3_size envM)`)
val _ = export_rewrites["good_v_def"]

val good_vs_EVERY = store_thm("good_vs_EVERY",
  ``∀vs. good_vs vs ⇔ EVERY good_v vs``,
  Induct >> simp[])
val _ = export_rewrites["good_vs_EVERY"]

val good_envE_EVERY = store_thm("good_envE_EVERY",
  ``∀envE. good_envE envE ⇔ EVERY good_v (MAP SND envE)``,
  Induct >> simp[] >> Cases >> simp[])

val good_envM_EVERY = store_thm("good_envM_EVERY",
  ``∀envM. good_envM envM ⇔ EVERY good_envE (MAP SND envM)``,
  Induct >> simp[] >> Cases >> simp[])

val _ = export_rewrites["good_envM_EVERY","good_envE_EVERY","good_vs_EVERY"]

val good_v_i1_def = tDefine"good_v_i1"`
  (good_v_i1 (Litv_i1 _) ⇔ T) ∧
  (good_v_i1 (Conv_i1 _ vs) ⇔ good_vs_i1 vs) ∧
  (good_v_i1 (Closure_i1 (_,env) _ _) ⇔ good_vs_i1 (MAP SND env)) ∧
  (good_v_i1 (Recclosure_i1 (_,env) funs f) ⇔
   good_vs_i1 (MAP SND env) ∧ ALL_DISTINCT (MAP FST funs) ∧ MEM f (MAP FST funs)) ∧
  (good_v_i1 (Loc_i1 _) ⇔ T) ∧
  (good_vs_i1 [] ⇔ T) ∧
  (good_vs_i1 (v::vs) ⇔ good_v_i1 v ∧ good_vs_i1 vs)`
  (WF_REL_TAC`inv_image $< (\x. case x of INL v => v_i1_size v | INR vs => v_i14_size vs)` >>
   simp[] >> conj_tac >> rpt gen_tac >> Induct_on`env` >> simp[v_i1_size_def] >>
   Cases >> simp[v_i1_size_def] >> rw[] >> res_tac >> simp[])
val _ = export_rewrites["good_v_i1_def"]

val good_vs_i1_EVERY = store_thm("good_vs_i1_EVERY",
  ``∀vs. good_vs_i1 vs ⇔ EVERY good_v_i1 vs``,
  Induct >> simp[])
val _ = export_rewrites["good_vs_i1_EVERY"]

val good_v_i2_def = tDefine"good_v_i2"`
  (good_v_i2 (Litv_i2 _) ⇔ T) ∧
  (good_v_i2 (Conv_i2 _ vs) ⇔ good_vs_i2 vs) ∧
  (good_v_i2 (Closure_i2 env _ _) ⇔ good_vs_i2 (MAP SND env)) ∧
  (good_v_i2 (Recclosure_i2 env funs f) ⇔
   good_vs_i2 (MAP SND env) ∧ ALL_DISTINCT (MAP FST funs) ∧ MEM f (MAP FST funs)) ∧
  (good_v_i2 (Loc_i2 _) ⇔ T) ∧
  (good_vs_i2 [] ⇔ T) ∧
  (good_vs_i2 (v::vs) ⇔ good_v_i2 v ∧ good_vs_i2 vs)`
  (WF_REL_TAC`inv_image $< (\x. case x of INL v => v_i2_size v | INR vs => v_i23_size vs)` >>
   simp[] >> conj_tac >> rpt gen_tac >> Induct_on`env` >> simp[v_i2_size_def] >>
   Cases >> simp[v_i2_size_def] >> rw[] >> res_tac >> simp[])
val _ = export_rewrites["good_v_i2_def"]

val good_vs_i2_EVERY = store_thm("good_vs_i2_EVERY",
  ``∀vs. good_vs_i2 vs ⇔ EVERY good_v_i2 vs``,
  Induct >> simp[])
val _ = export_rewrites["good_vs_i2_EVERY"]

val funs_to_i1_MAP = store_thm("funs_to_i1_MAP",
  ``∀menv env funs. funs_to_i1 menv env funs = MAP (λ(f,x,e). (f,x,exp_to_i1 menv (env \\ x) e)) funs``,
  Induct_on`funs` >> simp[exp_to_i1_def] >>
  qx_gen_tac`p`>>PairCases_on`p`>>simp[exp_to_i1_def])

val v_to_i1_preserves_good = store_thm("v_to_i1_preserves_good",
  ``(∀genv v v1. v_to_i1 genv v v1 ⇒ good_v v ⇒ good_v_i1 v1) ∧
    (∀genv vs vs1. vs_to_i1 genv vs vs1 ⇒ good_vs vs ⇒ good_vs_i1 vs1) ∧
    (∀genv env env1. env_to_i1 genv env env1 ⇒ good_envE env ⇒ good_vs_i1 (MAP SND env1)) ∧
    (∀genv tops shadowers env. global_env_inv_flat genv tops shadowers env ⇒
      good_envE env ∧
      (∀n. n < LENGTH genv ∧ IS_SOME (EL n genv) ⇒
        ∃x. x ∉ shadowers ∧ IS_SOME (lookup x env) ∧ FLOOKUP tops x = SOME n) ⇒
      EVERY (OPTION_EVERY good_v_i1) genv) ∧
    (∀genv mods tops menv shadowers env. global_env_inv genv mods tops menv shadowers env ⇒
      good_envE env ∧ good_envM menv
      ⇒ EVERY (OPTION_EVERY good_v_i1) genv)``,
  ho_match_mp_tac v_to_i1_ind >> simp[] >>
  conj_tac >- (
    simp[funs_to_i1_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX]) >>
  conj_tac >- (
    simp[EVERY_MEM,MEM_EL,PULL_EXISTS] >>
    rw[] >> res_tac >>
    Cases_on`EL n genv`>>fs[] >>
    qmatch_assum_rename_tac`z ∉ shadowers`[] >>
    Cases_on`lookup z env`>>fs[] >>
    res_tac >> fs[] >> rw[] >> fs[] >> rw[] >>
    imp_res_tac libPropsTheory.lookup_in >>
    fs[MEM_EL] ) >>
  rw[] >> fs[] >>
  cheat (* false? TODO: need help fixing the statement *))

val funs_to_i2_MAP = store_thm("funs_to_i2_MAP",
  ``∀g funs. funs_to_i2 g funs = MAP (λ(f,x,e). (f,x,exp_to_i2 g e)) funs``,
  Induct_on`funs` >> simp[exp_to_i2_def] >>
  qx_gen_tac`p`>>PairCases_on`p`>>simp[exp_to_i2_def])

val v_to_i2_preserves_good = store_thm("v_to_i2_preserves_good",
  ``(∀g v v2. v_to_i2 g v v2 ⇒ good_v_i1 v ⇒ good_v_i2 v2) ∧
    (∀g vs vs2. vs_to_i2 g vs vs2 ⇒ good_vs_i1 vs ⇒ good_vs_i2 vs2) ∧
    (∀g env env2. env_to_i2 g env env2 ⇒ good_vs_i1 (MAP SND env) ⇒ good_vs_i2 (MAP SND env2))``,
  ho_match_mp_tac v_to_i2_ind >>
  simp[funs_to_i2_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX])

val funs_to_exh_MAP = store_thm("funs_to_exh_MAP",
  ``∀exh funs. funs_to_exh exh funs = MAP (λ(f,x,e). (f,x,exp_to_exh exh e)) funs``,
  Induct_on`funs` >> simp[exp_to_exh_def] >>
  qx_gen_tac`p`>>PairCases_on`p`>>simp[exp_to_exh_def])

val vs_to_exh_MAP = store_thm("vs_to_exh_MAP",
  ``∀exh vs. vs_to_exh exh vs = MAP (v_to_exh exh) vs``,
  Induct_on`vs`>>simp[v_to_exh_def])

val v_to_exh_preserves_good = store_thm("v_to_exh_preserves_good",
  ``(∀v exh. good_v_i2 v ⇒ good_v_exh (v_to_exh exh v)) ∧
    (∀env exh. good_vs_i2 (MAP SND env) ⇒ good_vs_exh (MAP SND (env_to_exh exh env))) ∧
    (∀(p:string#v_i2) exh. good_v_i2 (SND p) ⇒ good_v_exh (v_to_exh exh (SND p))) ∧
    (∀vs exh. good_vs_i2 vs ⇒ good_vs_exh (vs_to_exh exh vs))``,
  ho_match_mp_tac (TypeBase.induction_of(``:v_i2``)) >>
  simp[v_to_exh_def] >>
  conj_tac >- (
    Induct >> simp[v_to_exh_def] >- (
      simp[funs_to_exh_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] ) >>
    Cases >> simp[v_to_exh_def] >>
    metis_tac[] ) >>
  Cases >> simp[v_to_exh_def])

val genv_to_exh_preserves_good = prove(
  ``∀exh genv2.
    EVERY (OPTION_EVERY good_v_i2) genv2 ⇒
    EVERY (OPTION_EVERY good_v_exh)
      (MAP (OPTION_MAP (v_to_exh exh)) genv2)``,
  simp[EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >>
  Cases >> simp[] >> strip_tac >>
  res_tac >> fs[] >>
  metis_tac[v_to_exh_preserves_good])

val genv_to_i2_preserves_good = prove(
  ``∀g genv genv2. genv_to_i2 g genv genv2 ⇒
      EVERY (OPTION_EVERY good_v_i1) genv ⇒
      EVERY (OPTION_EVERY good_v_i2) genv2``,
  ho_match_mp_tac genv_to_i2_ind >>
  simp[] >> metis_tac[v_to_i2_preserves_good])
*)

(* misc *)

val code_env_cd_append = store_thm("code_env_cd_append",
  ``∀code cd code'. code_env_cd code cd ∧ ALL_DISTINCT (FILTER is_Label (code ++ code')) ⇒ code_env_cd (code ++ code') cd``,
  rw[] >> PairCases_on`cd` >>
  fs[code_env_cd_def] >>
  HINT_EXISTS_TAC>>simp[]>>
  HINT_EXISTS_TAC>>simp[])

val FOLDL_emit_thm = store_thm("FOLDL_emit_thm",
  ``∀ls s. FOLDL (λs i. s with out := i::s.out) s ls = s with out := REVERSE ls ++ s.out``,
  Induct >> simp[compiler_result_component_equality])

(* label_closures *)

val label_closures_thm = store_thm("label_closures_thm",
  ``(∀ez j e. (no_labs e) ∧ set (free_vars e) ⊆ count ez ⇒
     let (e',j') = label_closures ez j e in
     (j' = j + (LENGTH (free_labs ez e'))) ∧
     (MAP (FST o FST o SND) (free_labs ez e') = (GENLIST ($+ j) (LENGTH (free_labs ez e')))) ∧
     set (free_vars e') ⊆ set (free_vars e) ∧
     all_labs e' ∧ EVERY good_cd (free_labs ez e') ∧
     syneq_exp ez ez $= e e') ∧
    (∀ez j es.
     (no_labs_list es) ∧ set (free_vars_list es) ⊆ count ez ⇒
     let (es',j') = label_closures_list ez j es in
     (j' = j + LENGTH (free_labs_list ez es')) ∧
     (MAP (FST o FST o SND) (free_labs_list ez es') = (GENLIST ($+ j) (LENGTH (free_labs_list ez es')))) ∧
     set (free_vars_list es') ⊆ set (free_vars_list es) ∧
     all_labs_list es' ∧ EVERY good_cd (free_labs_list ez es') ∧
     EVERY2 (syneq_exp ez ez $=) es es') ∧
    (∀ez j nz k defs ds0 ls0.
     (no_labs_defs (ls0 ++ MAP ($, NONE) defs)) ∧
     set (free_vars_defs nz (MAP ($, NONE) defs)) ⊆ count ez ∧
     (LENGTH ds0 = k) ∧ (LENGTH defs = nz - k) ∧ k ≤ nz ∧ (LENGTH ls0 = k) ∧
     syneq_defs ez ez $= (ls0 ++ MAP ($, NONE) defs) (ds0 ++ MAP ($, NONE) defs) (λv1 v2. v1 < nz ∧ (v2 = v1))
     ⇒
     let (defs',j') = label_closures_defs ez j nz k defs in
     (j' = j + LENGTH (free_labs_defs ez nz k defs')) ∧
     (MAP (FST o FST o SND) (free_labs_defs ez nz k defs') = GENLIST ($+ j) (LENGTH (free_labs_defs ez nz k defs'))) ∧
     set (free_vars_defs nz defs') ⊆ set (free_vars_defs nz (MAP ($, NONE) defs)) ∧
     (LENGTH defs' = LENGTH defs) ∧
     all_labs_defs defs' ∧
     EVERY good_cd (free_labs_defs ez nz k defs') ∧
     syneq_defs ez ez $= (ls0 ++ (MAP ($, NONE) defs)) (ds0 ++ defs') (λv1 v2. v1 < nz ∧ (v2 = v1)))``,
  ho_match_mp_tac label_closures_ind >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >> strip_tac >>
    fs[LET_THM,UNCURRY] >>
    simp[Once syneq_exp_cases] ) >>
  strip_tac >- (
    ntac 2 gen_tac >>
    map_every qx_gen_tac[`e1`,`e2`] >>
    rpt strip_tac >> fs[] >>
    `set (free_vars e2) ⊆ count (ez + 1)` by (
      fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1] >>
      Cases>>fsrw_tac[ARITH_ss][] ) >> fs[] >>
    qabbrev_tac`p = label_closures ez j e1` >> PairCases_on`p`>>fs[LET_THM] >>
    qabbrev_tac`q = label_closures (ez+1) (j + LENGTH (free_labs ez p0)) e2` >> PairCases_on`q`>>fs[] >>
    simp[LIST_EQ_REWRITE] >>
    conj_tac >- (
      gen_tac >>
      Cases_on`x<LENGTH (free_labs ez p0)`>>
      lrw[EL_APPEND1,EL_APPEND2] ) >>
    rfs[] >>
    conj_tac >- (
      fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1] >>
      Cases >> rw[ADD1] >>
      res_tac >>
      disj2_tac >> HINT_EXISTS_TAC >>
      fsrw_tac[ARITH_ss][] ) >>
    simp[Once syneq_exp_cases] >>
    match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_mono_V)) >>
    HINT_EXISTS_TAC >>
    simp[]) >>
  strip_tac >- (rw[] >> rw[syneq_exp_refl]) >>
  strip_tac >- (rw[] >> rw[syneq_exp_refl]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    fs[LET_THM,UNCURRY] >>
    simp[Once syneq_exp_cases] ) >>
  strip_tac >- (
    rw[] >> fs[LET_THM] >>
    rw[Once syneq_exp_cases] >> rfs[]) >>
  strip_tac >- (
    Cases_on`bd` >- (
      ntac 2 gen_tac >>
      map_every qx_gen_tac[`e1`,`e2`] >>
      rpt strip_tac >> fs[] >>
      `set (free_vars e2) ⊆ count (ez + 1)` by (
        fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1] >>
        Cases>>fsrw_tac[ARITH_ss][] ) >> fs[] >>
      qabbrev_tac`p = label_closures ez j e1` >> PairCases_on`p`>>fs[LET_THM] >>
      qabbrev_tac`q = label_closures (ez+1) (j + LENGTH (free_labs ez p0)) e2` >> PairCases_on`q`>>fs[] >>
      simp[LIST_EQ_REWRITE] >>
      conj_tac >- (
        gen_tac >>
        Cases_on`x<LENGTH (free_labs ez p0)`>>
        lrw[EL_APPEND1,EL_APPEND2] ) >>
      rfs[] >>
      conj_tac >- (
        fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1] >>
        Cases >> rw[ADD1] >>
        res_tac >>
        disj2_tac >> HINT_EXISTS_TAC >>
        fsrw_tac[ARITH_ss][] ) >>
      simp[Once syneq_exp_cases] >>
      match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_mono_V)) >>
      HINT_EXISTS_TAC >>
      simp[]) >>
    simp[] >>
    ntac 2 gen_tac >>
    map_every qx_gen_tac[`e1`,`e2`] >>
    rpt strip_tac >> fs[] >>
    simp[Once syneq_exp_cases] >>
    qabbrev_tac`p = label_closures ez j e1` >>
    PairCases_on`p`>>fs[LET_THM] >>
    qabbrev_tac`q = label_closures ez (j + LENGTH (free_labs ez p0)) e2` >>
    PairCases_on`q`>>fs[LET_THM] >>
    simp[LIST_EQ_REWRITE] >>
    conj_tac >- (
      gen_tac >>
      Cases_on`x<LENGTH (free_labs ez p0)`>>
      lrw[EL_APPEND1,EL_APPEND2] ) >>
    rfs[] >>
    fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1] ) >>
  strip_tac >- (
    rpt strip_tac >>
    simp[] >>
    `FILTER (IS_NONE o FST) defs = defs` by (
      simp[FILTER_EQ_ID] >>
      fs[FLAT_EQ_NIL,EVERY_MAP] >>
      fs[EVERY_MEM,FORALL_PROD] >>
      qx_gen_tac`z` >> rpt strip_tac >>
      res_tac >> Cases_on`z`>>fs[] ) >>
    full_simp_tac std_ss [LET_THM] >>
    full_simp_tac std_ss [FILTER_EQ_ID,LENGTH_MAP] >>
    qabbrev_tac`p = label_closures_defs ez j (LENGTH defs) 0 (MAP SND defs)` >>
    PairCases_on`p`>>
    `no_labs e`by fs[] >>
    `set (free_vars e) ⊆ count (ez + LENGTH defs)` by (
      qpat_assum`set (free_vars X) ⊆ Y`mp_tac >>
      rpt (pop_assum kall_tac) >>
      fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,LET_THM] >>
      srw_tac[ARITH_ss][ADD1] >>
      res_tac >> fsrw_tac[ARITH_ss][] ) >>
    full_simp_tac std_ss [] >>
    qabbrev_tac`q = label_closures (ez + LENGTH defs) p1 e` >>
    PairCases_on`q` >>
    full_simp_tac std_ss [] >>
    `MAP ($, NONE) (MAP SND defs) = defs` by (
      fs[EVERY_MEM] >>
      lrw[MAP_MAP_o] >>
      CONV_TAC(RAND_CONV(REWRITE_CONV[Once (CONJUNCT2 (GSYM MAP_ID)),SimpRHS])) >>
      lrw[MAP_EQ_f,FORALL_PROD] >> res_tac >> fs[]) >>
    full_simp_tac std_ss [] >>
    first_x_assum(qspecl_then[`[]`,`[]`]mp_tac) >>
    simp[syneq_defs_refl,EVERY_MAP] >>
    fs[LET_THM] >>
    strip_tac >>
    fsrw_tac[ETA_ss][] >>
    rfs[] >> simp[] >>
    conj_tac >- (
      lrw[LIST_EQ_REWRITE] >>
      Cases_on`x < LENGTH (free_labs_defs ez (LENGTH defs) 0 p0)` >>
      lrw[EL_APPEND1,EL_APPEND2] ) >>
    conj_tac >- (
      fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,free_vars_defs_MAP] >>
      gen_tac >> strip_tac >>
      disj2_tac >>
      qexists_tac`m` >>
      simp[] ) >>
    simp[Once syneq_exp_cases] >>
    HINT_EXISTS_TAC >> simp[] >>
    match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_mono_V)) >>
    HINT_EXISTS_TAC >>
    simp[]) >>
  strip_tac >- (
    ntac 3 gen_tac >>
    map_every qx_gen_tac[`e`,`es`] >>
    rpt strip_tac >>
    qabbrev_tac`p = label_closures ez j e` >> PairCases_on`p`>>fs[LET_THM] >>
    qabbrev_tac`q = label_closures_list ez (j + LENGTH (free_labs ez p0)) es` >> PairCases_on`q`>>fs[] >>
    fs[] >>
    simp[LIST_EQ_REWRITE] >>
    conj_tac >- (
      gen_tac >>
      Cases_on`x<LENGTH (free_labs ez p0)`>>
      lrw[EL_APPEND1,EL_APPEND2] ) >>
    rfs[] >>
    conj_tac >- (
      fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
    simp[Once syneq_exp_cases]) >>
  strip_tac >- (
    rw[] >> fs[LET_THM] >> rfs[] >>
    simp[Once syneq_exp_cases] ) >>
  strip_tac >- (
    ntac 2 gen_tac >>
    map_every qx_gen_tac[`p2`,`e1`,`e2`] >>
    rpt strip_tac >> fs[] >>
    qabbrev_tac`p = label_closures ez j e1` >> PairCases_on`p`>>fs[LET_THM] >>
    qabbrev_tac`q = label_closures ez (j + LENGTH (free_labs ez p0)) e2` >> PairCases_on`q`>>fs[] >>
    simp[LIST_EQ_REWRITE] >>
    conj_tac >- (
      gen_tac >> strip_tac >>
      Cases_on`x < LENGTH (free_labs ez p0)`>>
      lrw[EL_APPEND1,EL_APPEND2]) >>
    conj_tac >- (
      rfs[] >>
      fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
    simp[Once syneq_exp_cases]) >>
  strip_tac >- (
    ntac 2 gen_tac >>
    map_every qx_gen_tac[`e1`,`e2`] >>
    rpt strip_tac >> fs[] >>
    qabbrev_tac`p = label_closures ez j e1` >> PairCases_on`p`>>fs[LET_THM] >>
    qabbrev_tac`q = label_closures ez (j + LENGTH (free_labs ez p0)) e2` >> PairCases_on`q`>>fs[] >>
    simp[LIST_EQ_REWRITE] >>
    conj_tac >- (
      gen_tac >> strip_tac >>
      Cases_on`x < LENGTH (free_labs ez p0)`>>
      lrw[EL_APPEND1,EL_APPEND2]) >>
    conj_tac >- (
      rfs[] >>
      fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
    simp[Once syneq_exp_cases]) >>
  strip_tac >- (
    ntac 2 gen_tac >>
    map_every qx_gen_tac[`e1`,`e2`,`e3`] >>
    rpt strip_tac >> fs[] >>
    qabbrev_tac`p = label_closures ez j e1` >> PairCases_on`p`>>fs[LET_THM] >>
    qabbrev_tac`q = label_closures ez (j + LENGTH (free_labs ez p0)) e2` >> PairCases_on`q`>>fs[] >>
    qabbrev_tac`r = label_closures ez (j + LENGTH (free_labs ez p0) + LENGTH (free_labs ez q0)) e3` >> PairCases_on`r`>>fs[] >>
    simp[LIST_EQ_REWRITE] >>
    conj_tac >- (
      gen_tac >> strip_tac >>
      Cases_on`x < LENGTH (free_labs ez p0)`>>
      lrw[EL_APPEND1,EL_APPEND2] >>
      Cases_on`x < LENGTH (free_labs ez p0) + LENGTH (free_labs ez q0)` >>
      lrw[EL_APPEND1,EL_APPEND2] ) >>
    conj_tac >- (
      rfs[] >>
      fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,MEM_GENLIST] ) >>
    simp[Once syneq_exp_cases]) >>
  strip_tac >- (
    simp[] >> simp[Once syneq_exp_cases] ) >>
  strip_tac >- simp[] >>
  strip_tac >- (
    rpt strip_tac >>
    fs[] >>
    qabbrev_tac`p = label_closures ez j e` >>
    PairCases_on`p`>>fs[LET_THM] >>
    qabbrev_tac`q = label_closures_list ez (j + LENGTH (free_labs ez p0)) es` >>
    PairCases_on`q`>>fs[] >> simp[] >> rfs[] >>
    conj_tac >- (
      lrw[LIST_EQ_REWRITE] >>
      Cases_on`x < LENGTH (free_labs ez p0)`>>
      lrw[EL_APPEND1,EL_APPEND2] ) >>
    conj_tac >- (
      fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
    fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
  strip_tac >- (
    simp[] >> rw[FUNION_FEMPTY_2] >>
    fs[LENGTH_NIL]) >>
  rpt gen_tac >> rpt strip_tac >>
  full_simp_tac (std_ss++ARITH_ss) [] >>
  last_x_assum mp_tac >>
  last_x_assum mp_tac >>
  simp[] >> ntac 2 strip_tac >>
  Q.PAT_ABBREV_TAC`r = bind_fv X Y Z` >>
  PairCases_on`r`>>fs[] >>
  Q.PAT_ABBREV_TAC`ezz:num = az + (X + (Y + 1))` >>
  qabbrev_tac`p = label_closures ezz (j+1) r3` >>
  PairCases_on`p` >> full_simp_tac std_ss [] >>
  qabbrev_tac`q = label_closures_defs ez p1 nz (k+1) defs` >>
  PairCases_on`q` >> full_simp_tac std_ss [] >>
  `no_labs r3` by (
    fs[bind_fv_def,LET_THM,markerTheory.Abbrev_def] ) >>
  `set (free_vars r3) ⊆ count ezz` by (
    fs[bind_fv_def,LET_THM,markerTheory.Abbrev_def] >>
    first_x_assum(qspec_then`[]`kall_tac) >>
    qpat_assum`P⇒Q`kall_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    srw_tac[ARITH_ss][] >- (
      qho_match_abbrev_tac`(the n (find_index x ls n)) < y` >>
      qho_match_abbrev_tac`P (the n (find_index x ls n))` >>
      ho_match_mp_tac the_find_index_suff >>
      simp[Abbr`P`,Abbr`x`,Abbr`ls`,MEM_FILTER,ADD1,MEM_GENLIST,Abbr`n`,Abbr`y`] >>
      rw[] >>
      qmatch_abbrev_tac`m < A + B` >>
      Cases_on`m=A`>>fsrw_tac[ARITH_ss][]>>
      Cases_on`B=0`>>fsrw_tac[ARITH_ss][]>>
      fs[LENGTH_NIL_SYM,FILTER_EQ_NIL,EVERY_MEM,QSORT_MEM,markerTheory.Abbrev_def] >>
      res_tac >> fsrw_tac[ARITH_ss][]) >>
    qho_match_abbrev_tac`(the 0 (find_index x ls n)) < y` >>
    qho_match_abbrev_tac`P (the 0 (find_index x ls n))` >>
    ho_match_mp_tac the_find_index_suff >>
    `n ≤ nz` by (
      unabbrev_all_tac >>
      simp[GSYM ADD1] >>
      simp[GSYM LESS_EQ] >>
      qmatch_abbrev_tac`LENGTH (FILTER P ls) < nz` >>
      `nz = LENGTH ls` by rw[Abbr`ls`] >> pop_assum SUBST1_TAC >>
      match_mp_tac LENGTH_FILTER_LESS >>
      simp[Abbr`P`,Abbr`ls`,EXISTS_MEM,MEM_GENLIST] >>
      qexists_tac`LENGTH ls0` >>
      simp[] ) >>
    reverse conj_tac >- (
      unabbrev_all_tac >>
      simp[MEM_MAP,MEM_FILTER,sortingTheory.QSORT_MEM] >>
      qexists_tac`v` >> simp[] ) >>
    simp[Abbr`P`,Abbr`y`] >>
    qx_gen_tac`m`>>strip_tac >>
    qmatch_abbrev_tac`m + n < l1 + l2` >>
    `l2 = LENGTH ls + 1` by rw[Abbr`l2`,Abbr`ls`] >> rw[] >>
    qsuff_tac`n ≤ l1 + 1` >- DECIDE_TAC >>
    simp[Abbr`n`]) >>
  full_simp_tac std_ss [LET_THM] >>
  Q.PAT_ABBREV_TAC`cd:def = (SOME X,az,p0)` >>
  last_x_assum(qspecl_then[`ds0++[cd]`,`ls0++[(NONE,az,b)]`]mp_tac) >>
  discharge_hyps >- (
    simp[] >>
    rator_x_assum`syneq_defs`mp_tac >>
    simp[Once syneq_exp_cases] >>
    simp[EVERY_MAP] >> strip_tac >>
    simp[Once syneq_exp_cases,EVERY_MAP] >>
    qx_gen_tac`v` >> strip_tac >>
    first_x_assum(qspec_then`v`mp_tac) >> simp[] >>
    REWRITE_TAC[GSYM APPEND_ASSOC] >>
    Cases_on`v < k`>>simp[EL_APPEND1,EL_APPEND2,ADD1,EL_MAP] >- (
      strip_tac >>
      ntac 2 (first_x_assum (mp_tac o SYM)) >>
      ntac 2 strip_tac >>
      fsrw_tac[ARITH_ss][ADD1] ) >>
    Cases_on`v=k` >- (
      simp[Abbr`cd`] >> strip_tac >>
      simp[syneq_cb_aux_def] >>
      fsrw_tac[ARITH_ss][ADD1] >>
      simp[syneq_cb_aux_def] >>
      conj_asm1_tac >- (
        fs[bind_fv_def,LET_THM,markerTheory.Abbrev_def] >>
        simp[EVERY_MEM,MEM_MAP,MEM_FILTER,QSORT_MEM,MEM_FILTER,MEM_GENLIST] >>
        simp[GSYM LEFT_FORALL_IMP_THM] >>
        qpat_assum`Y ⊆ count ez` mp_tac >>
        qpat_assum`Y ⊆ count ez` mp_tac >>
        simp[SUBSET_DEF,GSYM LEFT_FORALL_IMP_THM] >>
        srw_tac[DNF_ss,ARITH_ss][NOT_LESS] >>
        metis_tac[] ) >>
      qmatch_abbrev_tac`syneq_exp z1 ezz V b p0` >>
      qsuff_tac`syneq_exp z1 ezz V b r3` >- (
        strip_tac >>
        `V = $= O V` by metis_tac[Id_O] >> pop_assum SUBST1_TAC >>
        match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_trans)) >>
        PROVE_TAC[] ) >>
      qpat_assum`Abbrev(X = bind_fv A Y Z)`mp_tac >>
      simp[bind_fv_def,markerTheory.Abbrev_def] >> rw[] >>
      match_mp_tac mkshift_thm >>
      simp[Abbr`z1`,Abbr`ezz`] >>
      conj_tac >- simp[Abbr`V`,syneq_cb_V_def] >>
      reverse conj_tac >- (
        qpat_assum`Y ⊆ count ez`mp_tac >>
        qpat_assum`Y ⊆ count ez`mp_tac >>
        simp[SUBSET_DEF,GSYM LEFT_FORALL_IMP_THM] >>
        srw_tac[DNF_ss,ARITH_ss][NOT_LESS] >>
        Cases_on`az + nz ≤ x`>>simp[]) >>
      gen_tac >> strip_tac >>
      reverse conj_tac >- (
        rw[] >- (
          qho_match_abbrev_tac`the 0 (find_index a w c) < X` >>
          qunabbrev_tac`X` >>
          qho_match_abbrev_tac`P (the c (find_index a w c))` >>
          match_mp_tac the_find_index_suff >>
          reverse conj_tac >- (
            unabbrev_all_tac >>
            fs[SUBSET_DEF] >>
            simp[MEM_FILTER,MEM_GENLIST] ) >>
          simp[Abbr`w`,Abbr`c`,Abbr`P`]) >>
        qho_match_abbrev_tac`the 0 (find_index a w c) < X` >>
        qunabbrev_tac`X` >>
        qho_match_abbrev_tac`P (the 0 (find_index a w c))` >>
        match_mp_tac the_find_index_suff >>
        reverse conj_tac >- (
          unabbrev_all_tac >>
          simp[MEM_MAP,MEM_FILTER,QSORT_MEM] >>
          qexists_tac`x`>>simp[]) >>
        simp[Abbr`w`,Abbr`c`,Abbr`P`]) >>
      Q.PAT_ABBREV_TAC`envs:num list = MAP X (FILTER Y Z)` >>
      `¬(x < az + nz) ⇒ MEM (x-(az+nz)) envs` by (
        simp[Abbr`envs`,MEM_MAP,MEM_FILTER,QSORT_MEM] >>
        strip_tac >>
        qexists_tac`x` >> simp[] ) >>
      Q.PAT_ABBREV_TAC`recs = LENGTH ls0::X` >>
      `x < az + nz ⇒ MEM (x - az) recs` by (
        simp[Abbr`recs`,MEM_FILTER,MEM_GENLIST] ) >>
      simp[Abbr`V`] >>
      reverse(rw[]) >- (
        fs[] >>
        simp[syneq_cb_V_def] >>
        Q.PAT_ABBREV_TAC`rz = LENGTH (FILTER X Y) + 1` >>
        Q.ISPECL_THEN[`envs`,`x-(az+nz)`,`rz`]mp_tac find_index_MEM >>
        simp[] >> disch_then strip_assume_tac >> simp[] >>
        simp[Abbr`rz`] ) >>
      simp[syneq_cb_V_def] >> fs[] >>
      Q.ISPECL_THEN[`recs`,`x-az`,`0:num`]mp_tac find_index_MEM >>
      simp[] >> disch_then strip_assume_tac >> simp[] >>
      Cases_on`i=0` >- (
        simp[] >> fs[Abbr`recs`]) >>
      simp[] >>
      qpat_assum`EL X Y = x - def0`mp_tac >>
      simp[Abbr`recs`,EL_CONS,PRE_SUB1] >>
      fsrw_tac[ARITH_ss][]) >>
    lrw[EL_CONS] >>
    ntac 2 (qpat_assum`X = Y`(mp_tac o SYM)) >>
    simp[PRE_SUB1,EL_MAP] >>
    Q.PAT_ABBREV_TAC`p = EL X defs` >>
    PairCases_on`p` >>
    simp[syneq_cb_aux_def] >>
    ntac 2 strip_tac >>
    fsrw_tac[ARITH_ss][] >> rw[] >> fs[] >>
    fsrw_tac[ARITH_ss][ADD1] >>
    `LENGTH defs + (LENGTH ls0 + 1) = nz` by simp[] >>
    pop_assum SUBST1_TAC >>
    match_mp_tac (MP_CANON(CONJUNCT1 syneq_exp_mono_V)) >>
    HINT_EXISTS_TAC >>
    simp[]) >>
  simp[] >> strip_tac >>
  simp[Abbr`cd`,ADD1]>>
  conj_tac >- (
    fsrw_tac[ARITH_ss][] >>
    lrw[LIST_EQ_REWRITE,EL_CONS,ADD1] >>
    Cases_on`x=0` >> lrw[EL_CONS,PRE_SUB1] >>
    Cases_on`x < LENGTH (free_labs ezz p0)` >>
    lrw[EL_APPEND1,EL_APPEND2] >>
    Cases_on `x-1 < LENGTH (free_labs ezz p0)` >>
    lrw[EL_APPEND1,EL_APPEND2]) >>
  conj_tac >- (
    rev_full_simp_tac std_ss [] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
  reverse conj_tac >- (
    metis_tac[CONS_APPEND,APPEND_ASSOC] ) >>
  simp[good_cd_def] >>
  conj_tac >- (
    fs[bind_fv_def,LET_THM,markerTheory.Abbrev_def] >>
    simp[EVERY_MAP,EVERY_FILTER] >>
    simp[EVERY_MEM,QSORT_MEM] >>
    qpat_assum`Y ⊆ count ez` mp_tac >>
    qpat_assum`Y ⊆ count ez` mp_tac >>
    srw_tac[DNF_ss][SUBSET_DEF] >>
    res_tac >> fsrw_tac[ARITH_ss][] ) >>
  conj_tac >- (
    fs[bind_fv_def,LET_THM,markerTheory.Abbrev_def] >>
    qpat_assum`set (free_vars p0) ⊆ X`mp_tac >>
    simp[SUBSET_DEF] >> strip_tac >>
    gen_tac >> strip_tac >>
    first_x_assum(qspec_then`x`mp_tac) >>
    simp[] >> strip_tac >>
    Cases_on`v<az`>>fsrw_tac[ARITH_ss][]>>
    Cases_on`v<az+nz`>>fsrw_tac[ARITH_ss][]>- (
      qho_match_abbrev_tac`the 0 (find_index a ls n) < X` >>
      qho_match_abbrev_tac`P (the n (find_index a ls n))` >>
      match_mp_tac the_find_index_suff >>
      simp[Abbr`ls`,Abbr`P`,Abbr`X`,MEM_FILTER,MEM_GENLIST,Abbr`n`,Abbr`a`,MEM_MAP,QSORT_MEM] ) >>
    rw[] >>
    qho_match_abbrev_tac`the 0 (find_index a ls n) < X` >>
    qho_match_abbrev_tac`P (the 0 (find_index a ls n))` >>
    match_mp_tac the_find_index_suff >>
    simp[Abbr`ls`,Abbr`P`,Abbr`X`,MEM_FILTER,MEM_GENLIST,Abbr`n`,Abbr`a`,MEM_MAP,QSORT_MEM] >>
    HINT_EXISTS_TAC >> simp[] ) >>
  map_every qexists_tac[`b`,`r3`] >>
  simp[])

(* compile_code_env *)

val FOLDL_cce_aux_thm = store_thm("FOLDL_cce_aux_thm",
  ``∀c s. let s' = FOLDL cce_aux s c in
     ALL_DISTINCT (MAP (FST o FST) c) ∧
     EVERY (combin$C $< s.next_label) (MAP (FST o FST) c)
      ⇒
     ∃code.
     (s'.out = REVERSE code ++ s.out) ∧
     (s.next_label ≤ s'.next_label) ∧
     ALL_DISTINCT (FILTER is_Label code) ∧
     EVERY (λn. MEM n (MAP (FST o FST) c) ∨ between s.next_label s'.next_label n)
       (MAP dest_Label (FILTER is_Label code)) ∧
     (EVERY all_labs (MAP (SND o SND) c) ⇒ ∀l. uses_label code l ⇒
       MEM (Label l) code ∨ MEM l (MAP (FST o FST o SND) (FLAT (MAP (λ(p,p3,p4). free_labs (LENGTH (FST(SND p))) p4) c)))) ∧
     (∀l. MEM l (MAP (FST o FST) c) ⇒ MEM (Label l) code) ∧
     ∃cs.
     ∀i. i < LENGTH c ⇒ let ((l,ccenv,ce),(az,body)) = EL i c in
         s.next_label ≤ (cs i).next_label ∧
         (∀j. j < i ⇒ (cs j).next_label ≤ (cs i).next_label) ∧
         ∃cc. ((compile (MAP CTEnv ccenv) (TCTail az 0) 0 (cs i) body).out = cc ++ (cs i).out) ∧
              l < (cs i).next_label ∧
              ∃bc0 bc1. (code = bc0 ++ Label l::REVERSE cc ++ bc1) ∧
                        EVERY (combin$C $< (cs i).next_label o dest_Label)
                          (FILTER is_Label bc0)``,
   Induct >- ( simp[Once SWAP_REVERSE] ) >>
   simp[] >>
   qx_gen_tac`p`>> PairCases_on`p` >>
   rpt gen_tac >>
   simp[cce_aux_def] >>
   strip_tac >>
   Q.PAT_ABBREV_TAC`s0 = s with out := X::y` >>
   qspecl_then[`MAP CTEnv p1`,`TCTail p3 0`,`0`,`s0`,`p4`]
     strip_assume_tac(CONJUNCT1 compile_append_out) >>
   Q.PAT_ABBREV_TAC`s1 = compile X Y Z A B` >>
   first_x_assum(qspecl_then[`s1`]mp_tac) >>
   simp[] >>
   discharge_hyps >- (
     fsrw_tac[ARITH_ss][EVERY_MEM,Abbr`s0`] >>
     rw[] >> res_tac >> DECIDE_TAC ) >>
   disch_then(Q.X_CHOOSE_THEN`c0`strip_assume_tac) >>
   simp[Abbr`s0`] >>
   simp[Once SWAP_REVERSE] >>
   fs[] >> simp[] >>
   simp[FILTER_APPEND,FILTER_REVERSE,MEM_FILTER,ALL_DISTINCT_REVERSE,ALL_DISTINCT_APPEND] >>
   conj_tac >- (
     rfs[FILTER_APPEND] >>
     fs[EVERY_MAP,EVERY_FILTER,EVERY_REVERSE,between_def] >>
     fsrw_tac[DNF_ss,ARITH_ss][EVERY_MEM,MEM_MAP] >>
     rw[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][]
       >- metis_tac[] >>
     res_tac >> fsrw_tac[ARITH_ss][] ) >>
   conj_tac >- (
     fs[EVERY_MAP,EVERY_REVERSE,EVERY_FILTER,is_Label_rwt,GSYM LEFT_FORALL_IMP_THM] >>
     fsrw_tac[DNF_ss][EVERY_MEM,between_def] >>
     rw[] >> spose_not_then strip_assume_tac >> res_tac >>
     fsrw_tac[ARITH_ss][] ) >>
   conj_tac >- (
     rw[] >>
     Cases_on`l=p0`>>rw[]>>
     Cases_on`MEM (Label l)c0`>>rw[]>>
     Cases_on`MEM (Label l)bc`>>rw[]>>
     fs[uses_label_thm,EXISTS_REVERSE] >>
     metis_tac[] ) >>
   conj_tac >- metis_tac[] >>
   qexists_tac`λi. if i = 0 then (s with out := Label p0::s.out) else cs (i-1)` >>
   Cases >> simp[] >- (
     map_every qexists_tac[`[]`,`c0`] >> simp[] ) >>
   strip_tac >>
   first_x_assum(qspec_then`n`mp_tac) >>
   simp[UNCURRY] >> strip_tac >>
   simp[] >>
   conj_asm1_tac >- ( Cases >> simp[] ) >>
   qexists_tac`Label p0::(REVERSE bc ++ bc0)` >>
   simp[FILTER_APPEND,FILTER_REVERSE,EVERY_REVERSE,EVERY_FILTER,is_Label_rwt,GSYM LEFT_FORALL_IMP_THM] >>
   qpat_assum`EVERY X (FILTER is_Label bc0)`mp_tac >>
   qpat_assum`EVERY X (MAP Y (FILTER is_Label bc))`mp_tac >>
   simp[EVERY_FILTER,EVERY_MAP,is_Label_rwt,GSYM LEFT_FORALL_IMP_THM,between_def] >>
   asm_simp_tac(srw_ss()++ARITH_ss++DNF_ss)[EVERY_MEM] >>
   rw[] >> res_tac >> DECIDE_TAC)

val compile_code_env_thm = store_thm("compile_code_env_thm",
  ``∀ez s e. let s' = compile_code_env s e in
      ALL_DISTINCT (MAP (FST o FST o SND) (free_labs ez e)) ∧
      EVERY (combin$C $< s.next_label) (MAP (FST o FST o SND) (free_labs ez e)) ∧
      EVERY good_cd (free_labs ez e)
      ⇒
      ∃code.
      (s'.out = REVERSE code ++ s.out) ∧
      (s.next_label < s'.next_label) ∧
      ALL_DISTINCT (FILTER is_Label code) ∧
      EVERY (λn. MEM n (MAP (FST o FST o SND) (free_labs ez e)) ∨ between s.next_label s'.next_label n)
        (MAP dest_Label (FILTER is_Label code)) ∧
      (EVERY all_labs (MAP (SND o SND o SND) (free_labs ez e)) ⇒
       ∀l. uses_label code l ⇒ MEM (Label l) code ∨
         MEM l (MAP (FST o FST o SND)
           (FLAT (MAP (λ(p,p3,p4). free_labs (LENGTH (FST (SND p))) p4) (MAP SND (free_labs ez e)))))) ∧
      (∀l. MEM l (MAP (FST o FST o SND) (free_labs ez e)) ⇒ MEM (Label l) code) ∧
      ∀bs bc0 bc1.
        (bs.code = bc0 ++ code ++ bc1) ∧
        (bs.pc = next_addr bs.inst_length bc0) ∧
        ALL_DISTINCT (FILTER is_Label bc0) ∧
        (∀l1 l2. MEM l1 (MAP dest_Label (FILTER is_Label bc0)) ∧ ((l2 = s.next_label) ∨ MEM l2 (MAP (FST o FST o SND) (free_labs ez e))) ⇒ l1 < l2)
        ⇒
        EVERY (code_env_cd (bc0++code)) (free_labs ez e) ∧
        bc_next bs (bs with pc := next_addr bs.inst_length (bc0++code))``,
  rw[compile_code_env_def] >> rw[] >>
  `MAP SND (free_labs 0 e) = MAP SND (free_labs ez e)` by metis_tac[MAP_SND_free_labs_any_ez] >>
  fs[] >>
  Q.ISPECL_THEN[`MAP SND (free_labs ez e)`,`s''`]mp_tac FOLDL_cce_aux_thm >>
  simp[Abbr`s''`] >>
  discharge_hyps >- (
    fsrw_tac[ARITH_ss][EVERY_MEM,MAP_MAP_o] >>
    rw[] >> res_tac >> DECIDE_TAC ) >>
  disch_then(Q.X_CHOOSE_THEN`c0`strip_assume_tac) >>
  simp[Once SWAP_REVERSE,Abbr`s''''`] >>
  conj_tac >- (
    simp[ALL_DISTINCT_APPEND,FILTER_APPEND,MEM_FILTER] >>
    fs[EVERY_MAP,EVERY_FILTER] >> fs[EVERY_MEM] >>
    spose_not_then strip_assume_tac >> res_tac >>
    fsrw_tac[ARITH_ss][between_def,MEM_MAP,MAP_MAP_o] >>
    res_tac >> rw[] >> DECIDE_TAC ) >>
  conj_tac >- (
    fs[EVERY_MAP,EVERY_FILTER,is_Label_rwt,GSYM LEFT_FORALL_IMP_THM,between_def] >>
    reverse conj_tac >- (disj2_tac >> DECIDE_TAC) >>
    fsrw_tac[DNF_ss][EVERY_MEM,MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
    rw[] >> res_tac >>
    TRY(metis_tac[]) >>
    disj2_tac >> DECIDE_TAC ) >>
  conj_tac >- (
    rw[] >>
    fs[MAP_MAP_o] >>
    fs[uses_label_thm] >>
    metis_tac[] ) >>
  conj_tac >- fs[MAP_MAP_o] >>
  rpt gen_tac >>
  strip_tac >>
  conj_tac >- (
    fs[EVERY_MEM] >>
    qx_gen_tac`z` >>
    PairCases_on`z` >> strip_tac >>
    simp[code_env_cd_def] >>
    qmatch_assum_abbrev_tac`MEM cd (free_labs ez e)` >>
    `∃i. i < LENGTH (free_labs ez e) ∧ (EL i (free_labs ez e) = cd)` by metis_tac[MEM_EL] >>
    qpat_assum`∀i. P ⇒ Q`(qspec_then`i`mp_tac) >>
    simp[EL_MAP] >>
    simp[Abbr`cd`] >> strip_tac >>
    qexists_tac`cs i`>>simp[] >>
    qexists_tac`bc0++Jump (Lab s.next_label)::bc0'` >>
    simp[] >>
    fs[EVERY_MEM,MEM_MAP,FILTER_APPEND] >>
    fsrw_tac[DNF_ss][] >- (
      rpt strip_tac >> res_tac >> DECIDE_TAC) >>
    rpt strip_tac >> res_tac >> DECIDE_TAC) >>
  `bc_fetch bs = SOME (Jump (Lab s.next_label))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0` >> simp[] ) >>
  simp[bc_eval1_thm,bc_eval1_def,bc_state_component_equality,bc_find_loc_def] >>
  match_mp_tac bc_find_loc_aux_append_code >>
  match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
  qexists_tac`LENGTH bc0 + 1 + LENGTH c0` >>
  simp[EL_APPEND2,TAKE_APPEND2,FILTER_APPEND,SUM_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER] >>
  fs[EVERY_MAP,EVERY_FILTER,between_def] >>
  fsrw_tac[DNF_ss][EVERY_MEM,is_Label_rwt,MEM_MAP,EXISTS_PROD,FORALL_PROD,MEM_FILTER] >>
  rw[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] >>
  res_tac >> fsrw_tac[ARITH_ss][])

(* printing *)

val _ = Parse.overload_on("print_bv",``λm. ov_to_string o bv_to_ov m``)
val print_bv_str_def = Define`print_bv_str m t v w = "val "++v++":"++(tystr t v)++" = "++(print_bv m w)++"\n"`

val append_cons_lemma = prove(``ls ++ [x] ++ a::b = ls ++ x::a::b``,lrw[])

val MAP_PrintC_thm = store_thm("MAP_PrintC_thm",
  ``∀ls bs bc0 bc1 bs'.
    bs.code = bc0 ++ (MAP PrintC ls) ++ bc1 ∧
    bs.pc = next_addr bs.inst_length bc0 ∧
    bs' = bs with <| output := bs.output ++ ls; pc := next_addr bs.inst_length (bc0 ++ (MAP PrintC ls))|>
    ⇒
    bc_next^* bs bs'``,
  Induct >- (
    simp[] >> rw[] >>
    simp[Once RTC_CASES1] >> disj1_tac >>
    simp[bc_state_component_equality] ) >>
  simp[] >> rw[] >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  `bc_fetch bs = SOME (PrintC h)` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0` >>
    simp[] ) >>
  simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
  first_x_assum match_mp_tac >>
  simp[bc_state_component_equality,IMPLODE_EXPLODE_I] >>
  qexists_tac`bc0 ++ [PrintC h]` >>
  simp[FILTER_APPEND,SUM_APPEND])

val _ = Parse.overload_on("print_bv_list",``λm t vs ws. FLAT (MAP (UNCURRY (print_bv_str m t)) (ZIP (vs,ws)))``)

val print_envE_cons = store_thm("print_envE_cons",
  ``print_envE types (x::xs) = print_envE types [x]++print_envE types xs``,
  rw[print_envE_def]);

val v_to_ov_exh_def = tDefine"v_to_ov_exh"`
  (v_to_ov_exh m (Litv l) = Litv_exh l) ∧
  (v_to_ov_exh m (Conv c vs) = Conv_exh (m c) (MAP (v_to_ov_exh m) vs)) ∧
  (v_to_ov_exh m (Loc n) = Loc_exh n) ∧
  (v_to_ov_exh m _ = Closure_exh [] "" (Extend_global_exh 0))`
(WF_REL_TAC`measure (v_size o SND)` >>
 gen_tac >> Induct >> simp[v_size_def] >> rw[] >>
 res_tac >> fsrw_tac[ARITH_ss][])
val _ = export_rewrites["v_to_ov_exh_def"]

val print_v_ov = store_thm("print_v_ov",
  ``(∀v m1 m2 sm. ov_to_string (Cv_to_ov m2 sm (v_to_Cv (v_to_pat (v_to_ov_exh m1 v)))) = print_v v)
    ∧ (∀x:all_env. T)
    ∧ (∀x:envC#envE. T)
    ∧ (∀x:envM. T)
    ∧ (∀x:string#envE. T)
    ∧ (∀x:envE. T)
    ∧ (∀x:string#v. T)
    ∧ (∀vs:v list. T)``,
  ho_match_mp_tac(TypeBase.induction_of``:v``) >>
  simp[print_v_def,v_to_Cv_def,printerTheory.ov_to_string_def] >>
  Cases >> simp[printerTheory.ov_to_string_def,print_lit_def] >>
  Cases_on`b`>>simp[printerTheory.ov_to_string_def,print_lit_def])

val print_bv_list_print_envE = store_thm("print_bv_list_print_envE",
  ``∀cm pp vars vs m Cvs bvs types env.
    EVERY2 syneq (MAP (v_to_Cv o v_to_pat o v_to_ov_exh cm) vs) Cvs ∧
    EVERY2 (Cv_bv pp) Cvs bvs ∧ LENGTH vars = LENGTH vs ∧
    set vars ⊆ FDOM types ∧
    env = ZIP(vars,vs)
    ⇒
    print_bv_list m types vars bvs = print_envE types env``,
  ntac 2 gen_tac >>
  Induct >- ( Cases >> simp[print_envE_def] ) >>
  qx_gen_tac`x`>>
  qx_gen_tac`ws`>>
  gen_tac >>
  map_every qx_gen_tac[`wvs`,`wbs`] >>
  ntac 3 strip_tac >>
  `∃v vs. ws = v::vs` by ( Cases_on`ws`>>fs[] ) >>
  `∃Cv Cvs. wvs = Cv::Cvs` by ( Cases_on`wvs`>>fs[EVERY2_EVERY] ) >>
  `∃bv bvs. wbs = bv::bvs` by ( Cases_on`wbs`>>fs[EVERY2_EVERY] ) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  simp[Once print_envE_cons] >>
  first_x_assum(qspecl_then[`vs`,`m`,`Cvs`,`bvs`,`types`]mp_tac) >>
  simp[] >>
  discharge_hyps >- fs[EVERY2_EVERY] >> rw[] >>
  rw[print_envE_def,print_bv_str_def] >>
  fs[EVERY2_EVERY] >>
  imp_res_tac Cv_bv_ov >>
  `bv_to_ov m bv = Cv_to_ov m (FST pp).sm (v_to_Cv (v_to_pat (v_to_ov_exh cm v)))` by
    metis_tac[syneq_ov] >>
  pop_assum SUBST1_TAC >>
  simp[print_v_ov,tystr_def,FLOOKUP_DEF])

val code_labels_ok_MAP_PrintC = store_thm("code_labels_ok_MAP_PrintC",
  ``∀ls. code_labels_ok (MAP PrintC ls)``,
  Induct>>simp[]>>rw[]>>match_mp_tac code_labels_ok_cons>>simp[])
val _ = export_rewrites["code_labels_ok_MAP_PrintC"]

val can_Print_list_EVERY = store_thm("can_Print_list_EVERY",
  ``∀ls. can_Print_list ls = EVERY can_Print ls``,
  Induct >> simp[])
val _ = export_rewrites["can_Print_list_EVERY"]

val compile_print_vals_thm = store_thm("compile_print_vals_thm",
  ``∀vs types i cs. let cs' = compile_print_vals types i vs cs in
    ∃code. cs'.out = REVERSE code ++ cs.out
         ∧ cs'.next_label = cs.next_label
         ∧ EVERY ($~ o is_Label) code ∧
         code_labels_ok code ∧
    ∀bs bc0 bvs st0.
    bs.code = bc0 ++ code
    ∧ bs.pc = next_addr bs.inst_length bc0
    ∧ bs.stack = bvs ++ st0
    ∧ can_Print_list bvs
    ∧ i + LENGTH vs ≤ LENGTH bvs
    ⇒
    let bs' = bs with <|pc := next_addr bs.inst_length (bc0++code)
                       ;output := bs.output ++ print_bv_list bs.cons_names types vs (TAKE (LENGTH vs) (DROP i bvs))|> in
    bc_next^* bs bs'``,
  Induct >> simp[compile_print_vals_def] >- (
    simp[Once SWAP_REVERSE] >> rw[] >>
    simp[Once RTC_CASES1] >>
    disj1_tac >>
    simp[bc_state_component_equality] )>>
  simp[FOLDL_emit_thm] >>
  qx_gen_tac`v` >>
  rpt strip_tac >>
  Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd X Y` >>
  first_x_assum(qspecl_then[`types`,`i+1`,`cs1`]mp_tac) >>
  simp[] >>
  disch_then(qx_choosel_then[`c1`]strip_assume_tac) >>
  simp[Abbr`cs1`,Once SWAP_REVERSE] >>
  simp[EVERY_MAP] >> fs[] >>
  Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd X Y` >>
  qmatch_assum_abbrev_tac`(compile_print_vals types (i+1) vs cs1').next_label = X` >>
  `cs1' = cs1` by (
    simp[Abbr`cs1`,Abbr`cs1'`,compiler_result_component_equality] ) >>
  fs[Abbr`cs1'`] >> pop_assum kall_tac >>
  simp [FLOOKUP_DEF] >>
  conj_tac >- (
    rpt(match_mp_tac code_labels_ok_cons>>simp[])>>
    match_mp_tac code_labels_ok_append>>simp[IMPLODE_EXPLODE_I]>>
    rpt(match_mp_tac code_labels_ok_append>>simp[]>>(TRY conj_tac)>>TRY(simp[code_labels_ok_def,uses_label_thm]>>NO_TAC))) >>
  rpt gen_tac >>
  strip_tac >>
  fs[IMPLODE_EXPLODE_I] >>
  `bs.code = bc0 ++ (MAP PrintC ("val "++v++":"++tystr types v++" = ")) ++ [Stack(Load i);Print;PrintC(#"\n")] ++ c1` by (
    simp[] ) >>
  qmatch_assum_abbrev_tac`bs.code = bc0 ++ l1 ++ l2 ++ c1` >>
  `bc_next^* bs (bs with <|pc:=next_addr bs.inst_length (bc0++l1)
                          ;output:=STRCAT bs.output ("val "++v++":"++tystr types v++" = ")|>)` by (
    match_mp_tac MAP_PrintC_thm >>
    qexists_tac`"val "++v++":"++tystr types v++" = "`>>
    qexists_tac`bc0` >>
    simp[Abbr`l1`] ) >>
  qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
  `bc_fetch bs1 = SOME (Stack (Load i))` by (
    match_mp_tac bc_fetch_next_addr >>
    simp[Abbr`bs1`] >>
    qexists_tac`bc0++l1` >>
    simp[Abbr`l2`] ) >>
  `bc_next^* bs1 (bs1 with <|pc:=next_addr bs.inst_length(bc0++l1++l2)
                            ;output := STRCAT bs1.output (print_bv bs.cons_names (EL i bvs))++"\n"|>)` by (
    simp[RTC_eq_NRC] >>
    qexists_tac`SUC(SUC(SUC 0))` >>
    simp[NRC] >>
    qho_match_abbrev_tac`∃z. bc_next bs1 z ∧ P z` >>
    simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
    simp[Abbr`bs1`,bc_eval_stack_def,EL_APPEND1]>>
    simp[Abbr`P`]>>
    qho_match_abbrev_tac`∃z. bc_next bs1 z ∧ P z` >>
    `bc_fetch bs1 = SOME Print` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac`bc0++l1++[HD l2]` >>
      simp[Abbr`bs1`,Abbr`l2`] >>
      simp[FILTER_APPEND,SUM_APPEND] ) >>
    simp[bc_eval1_thm,bc_eval1_def,bump_pc_def]>>
    simp[Abbr`bs1`]>>
    conj_tac >- (
      fs[EVERY_MEM] >> first_x_assum match_mp_tac >>
      simp[MEM_EL] >> qexists_tac`i` >> simp[] ) >>
    simp[Abbr`P`] >>
    qmatch_abbrev_tac`bc_next bs1 bs2` >>
    `bc_fetch bs1 = SOME (PrintC(#"\n"))` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac`bc0++l1++FRONT l2` >>
      simp[Abbr`bs1`,Abbr`l2`] >>
      simp[FILTER_APPEND,SUM_APPEND] ) >>
    simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
    simp[Abbr`bs1`,Abbr`bs2`,bc_state_component_equality,IMPLODE_EXPLODE_I] >>
    simp[FILTER_APPEND,SUM_APPEND,Abbr`l2`] ) >>
  qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
  `bc_next^* bs bs2` by metis_tac[RTC_TRANSITIVE,transitive_def] >>
  pop_assum mp_tac >>
  rpt(qpat_assum`bc_next^* a Y`kall_tac) >>
  first_x_assum(qspecl_then[`bs2`,`bc0++l1++l2`,`bvs`]mp_tac) >>
  simp[Abbr`bs2`,Abbr`bs1`,ADD1] >>
  strip_tac >>
  qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
  strip_tac >>
  qmatch_abbrev_tac`bc_next^* bs bs2'` >>
  `bs2' = bs2` by (
    simp[Abbr`bs2`,Abbr`bs2'`,bc_state_component_equality,Abbr`l1`] >>
    conj_tac >- (
      simp[SUM_APPEND,FILTER_APPEND] ) >>
    REWRITE_TAC[Once ADD_SYM] >>
    simp[TAKE_SUM] >>
    simp[DROP_DROP] >>
    `TAKE 1 (DROP i bvs) = [EL i bvs]` by (
      qpat_assum`X ≤ LENGTH bvs`mp_tac >>
      rpt (pop_assum kall_tac) >>
      qid_spec_tac`vs` >>
      qid_spec_tac`i` >>
      Induct_on`bvs`>>simp[] >>
      rw[] >>
      simp[EL_CONS,PRE_SUB1] >>
      first_x_assum match_mp_tac >>
      pop_assum mp_tac >>
      simp[ADD1] >> strip_tac >>
      qexists_tac`vs` >>
      simp[] ) >>
    simp[print_bv_str_def]) >>
  metis_tac[RTC_TRANSITIVE,transitive_def] )

val _ = Parse.overload_on("print_ctor",``λx. STRCAT x " = <constructor>\n"``)
val _ = Parse.overload_on("print_ctors",``λls. FLAT (MAP (λ(x,y). print_ctor x) ls)``)

val compile_print_ctors_thm = store_thm("compile_print_ctors_thm",
  ``∀ls cs. let cs' = compile_print_ctors ls cs in
    ∃code. cs'.out = REVERSE code ++ cs.out
      ∧ EVERY ($~ o is_Label) code
      ∧ code_labels_ok code
      ∧ cs'.next_label = cs.next_label ∧
      ∀bs bc0.
      bs.code = bc0 ++ code
      ∧ bs.pc = next_addr bs.inst_length bc0
      ⇒
      let bs' = bs with <|pc := next_addr bs.inst_length bs.code
           ; output := STRCAT bs.output (print_ctors ls)|> in
      bc_next^* bs bs'``,
  Induct >- (
    simp[compile_print_ctors_def,Once SWAP_REVERSE] >>
    rw[] >> simp[Once RTC_CASES1] >> simp[bc_state_component_equality] ) >>
  qx_gen_tac`x` >> PairCases_on`x` >>
  simp[compile_print_ctors_def,FOLDL_emit_thm,IMPLODE_EXPLODE_I] >>
  rw[] >>
  Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd x y` >>
  first_x_assum(qspec_then`cs1`mp_tac) >>
  simp[] >>
  disch_then(Q.X_CHOOSE_THEN`c1`strip_assume_tac) >>
  simp[Abbr`cs1`,Once SWAP_REVERSE,EVERY_MAP] >> fs[] >>
  qmatch_assum_abbrev_tac`(compile_print_ctors ls cs1).next_label = X` >>
  conj_tac >- (
    match_mp_tac code_labels_ok_append >> simp[]>>
    match_mp_tac code_labels_ok_append >> simp[]>>
    rpt(match_mp_tac code_labels_ok_cons >> simp[]) ) >>
  qmatch_abbrev_tac`((compile_print_ctors ls cs1').next_label = X) ∧ Y` >>
  `cs1' = cs1` by (
    simp[Abbr`cs1`,Abbr`cs1'`,compiler_result_component_equality] ) >>
  simp[Abbr`X`,Abbr`Y`] >>
  rpt strip_tac >>
  qmatch_assum_abbrev_tac`bs.code = bc0 ++ l1 ++ l2 ++ c1` >>
  `bc_next^* bs (bs with <|pc := next_addr bs.inst_length (bc0++l1++l2)
                          ;output := bs.output ++ (x0++" = <constructor>\n")|>)` by (
    match_mp_tac MAP_PrintC_thm >>
    qexists_tac`x0 ++ " = <constructor>\n"` >>
    qexists_tac`bc0` >>
    simp[Abbr`l1`,Abbr`l2`] ) >>
  qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
  first_x_assum(qspecl_then[`bs1`,`bc0++l1++l2`]mp_tac) >>
  simp[Abbr`bs1`] >>
  strip_tac >>
  qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
  qmatch_assum_abbrev_tac`bc_next^* bs1' bs2` >>
  `bs1' = bs1` by (
    simp[Abbr`bs1'`,Abbr`bs1`,bc_state_component_equality] ) >>
  qmatch_abbrev_tac`bc_next^* bs bs3` >>
  `bs2 = bs3` by (
    simp[Abbr`bs3`,bc_state_component_equality,semanticPrimitivesTheory.id_to_string_def] ) >>
  metis_tac[RTC_TRANSITIVE,transitive_def])

val new_dec_vs_def = Define`
  (new_dec_vs (Dtype _) = []) ∧
  (new_dec_vs (Dexn _ _) = []) ∧
  (new_dec_vs (Dlet p e) = pat_bindings p []) ∧
  (new_dec_vs (Dletrec funs) = MAP FST funs)`
val _ = export_rewrites["new_dec_vs_def"]

val compile_print_dec_thm = store_thm("compile_print_dec_thm",
  ``∀d types cs. let cs' = compile_print_dec types d cs in
      ∃code. cs'.out = REVERSE code ++ cs.out
        ∧ EVERY ($~ o is_Label) code
        ∧ cs'.next_label = cs.next_label
        ∧ code_labels_ok code ∧
      ∀bs bc0 bvs st0.
      bs.code = bc0 ++ code
      ∧ bs.pc = next_addr bs.inst_length bc0
      ∧ bs.stack = bvs ++ st0
      ∧ can_Print_list bvs
      ∧ LENGTH bvs = LENGTH (new_dec_vs d)
      ⇒
      let str =
        case d of
        | Dtype ts => print_envC ([],REVERSE(build_tdefs NONE ts))
        | Dexn cn ts => print_envC ([],[(cn, (LENGTH ts, TypeExn))])
        | d => print_bv_list bs.cons_names types (new_dec_vs d) bvs in
      let bs' = bs with
        <|pc := next_addr bs.inst_length (bc0++code)
         ;output := bs.output ++ str|> in
      bc_next^* bs bs'``,
  Cases >- (
    simp[compile_print_dec_def] >>
    rw[] >>
    qspecl_then[`pat_bindings p []`,`types`, `0`,`cs`]mp_tac compile_print_vals_thm >>
    simp[] >> rw[] >> simp[] >> rpt gen_tac >> strip_tac >>
    first_x_assum(qspecl_then[`bs`,`bc0`,`bvs`]mp_tac) >>
    simp[TAKE_LENGTH_ID_rwt] )
  >- (
    simp[compile_print_dec_def] >>
    rw[] >>
    Q.PAT_ABBREV_TAC`vs:string list = MAP X l` >>
    qspecl_then[`vs`,`types`,`0`,`cs`]mp_tac compile_print_vals_thm >>
    simp[] >> rw[] >> simp[] >> rpt gen_tac >> strip_tac >>
    first_x_assum(qspecl_then[`bs`,`bc0`,`bvs`]mp_tac) >>
    `vs = MAP FST l` by (
      simp[Abbr`vs`,MAP_EQ_f,FORALL_PROD] ) >>
    simp[TAKE_LENGTH_ID_rwt])
  >- (
    simp[] >>
    simp[compile_print_dec_def] >>
    Induct_on`l` >- (
      simp[compile_print_types_def,Once SWAP_REVERSE] >>
      simp[print_envC_def,semanticPrimitivesTheory.build_tdefs_def,LENGTH_NIL] >>
      rw[] >> simp[Once RTC_CASES1] >> simp[bc_state_component_equality] ) >>
    qx_gen_tac`x` >> PairCases_on`x` >>
    simp[compile_print_types_def] >>
    gen_tac >>
    qspecl_then[`x2`,`cs`]mp_tac (INST_TYPE[alpha|->``:t list``]compile_print_ctors_thm) >>
    simp[] >>
    disch_then(qx_choosel_then[`c1`]strip_assume_tac) >>
    first_x_assum(qspec_then`compile_print_ctors x2 cs`mp_tac) >>
    simp[] >>
    disch_then(qx_choosel_then[`c2`]strip_assume_tac) >>
    simp[] >>
    simp[Once SWAP_REVERSE] >>
    conj_tac >- (
      simp[code_labels_ok_append]>>simp[] ) >>
    rpt strip_tac >>
    last_x_assum(qspecl_then[`bs with code := bc0 ++ c1`,`bc0`]mp_tac) >>
    simp[] >> strip_tac >>
    qmatch_assum_abbrev_tac`bc_next^* bs0 bs1` >>
    `bc_next^* bs (bs1 with code := bs.code)` by (
      match_mp_tac RTC_bc_next_append_code >>
      map_every qexists_tac[`bs0`,`bs1`] >>
      simp[Abbr`bs0`,Abbr`bs1`,bc_state_component_equality] ) >>
    first_x_assum(qspecl_then[`bs1 with code := bs.code`]mp_tac) >>
    simp[Abbr`bs1`] >>
    simp[LENGTH_NIL] >>
    strip_tac >>
    qmatch_assum_abbrev_tac`bc_next^* bs1' bs2` >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
    `bs1' = bs1` by (
      simp[Abbr`bs1`,Abbr`bs1'`] ) >>
    qmatch_abbrev_tac`bc_next^* bs bs2'` >>
    `bs2' = bs2` by (
      simp[Abbr`bs2`,Abbr`bs2'`] >>
      simp[bc_state_component_equality] >>
      simp[semanticPrimitivesTheory.build_tdefs_def,print_envC_def] >>
      simp[MAP_MAP_o,combinTheory.o_DEF] >>
      simp[UNCURRY,astTheory.mk_id_def] >>
      simp[LAMBDA_PROD] ) >>
    metis_tac[RTC_TRANSITIVE,transitive_def])
  >- (
    simp[] >>
    simp[compile_print_dec_def] >>
    simp[compile_print_types_def] >>
    rw[] >>
    qspecl_then[`[s,l]`,`cs`]mp_tac (INST_TYPE[alpha|->``:t list``]compile_print_ctors_thm) >>
    simp[] >> rw[] >> simp[] >>
    simp[print_envC_def]))

val only_chars_lemma = prove(
  ``∀s. only_chars (MAP (Number o $& o ORD) s)``,
  Induct >> simp [only_chars_def,is_char_def,stringTheory.ORD_BOUND]);

val Cv_bv_can_Print = save_thm("Cv_bv_can_Print",prove(
  ``(∀Cv bv. Cv_bv pp Cv bv ⇒ can_Print bv) ∧
    (∀bvs ce env defs. benv_bvs pp bvs ce env defs ⇒ T)``,
  ho_match_mp_tac Cv_bv_ind >> simp[only_chars_lemma,only_chars_def] >>
  simp[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >> rw[] >>
  rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,MEM_EL])
  |> CONJUNCT1)

(* compile_Cexp *)

val good_labels_def = Define`
  good_labels nl code ⇔
    ALL_DISTINCT (FILTER is_Label code) ∧
    EVERY (combin$C $< nl o dest_Label) (FILTER is_Label code)`

val between_labels_def = Define`
  between_labels bc l1 l2 ⇔
  ALL_DISTINCT (FILTER is_Label bc) ∧
  EVERY (between l1 l2) (MAP dest_Label (FILTER is_Label bc)) ∧
  l1 ≤ l2`

val compile_Cexp_thm = store_thm("compile_Cexp_thm",
  ``∀renv rsz cs exp.
      set (free_vars exp) ⊆ count (LENGTH renv)
    ∧ no_labs exp
    ⇒
    let cs' = compile_Cexp renv rsz cs exp in
    ∃c0 code. cs'.out = REVERSE code ++ REVERSE c0 ++ cs.out ∧ between_labels (code++c0) cs.next_label cs'.next_label ∧
    code_labels_ok (c0++code) ∧
    ∀s env res rd csz bs bc0 bc00.
      Cevaluate s env exp res
    ∧ closed_vlabs env s bc0
    ∧ Cenv_bs rd s env renv rsz (bs with code := bc00)
    ∧ (bc00 = bc0 ∨ bc00 = bc0 ++ c0)
    ∧ bs.code = bc0 ++ c0 ++ code
    ∧ bs.pc = next_addr bs.inst_length bc0
    ∧ bs.clock = SOME (FST (FST s))
    ∧ good_labels cs.next_label bc0
    ⇒
    case SND res of
    | Rval v =>
        ∃s' w. syneq v w ∧
        csg_rel syneq (FST res) s' ∧
        closed_vlabs env s' (bc0++c0) ∧
        all_vlabs w ∧ (∀cd. cd ∈ vlabs w ⇒ code_env_cd (bc0++c0) cd) ∧
        code_for_push rd bs (bc0++c0) bc0 (c0++code) s' env [w] renv rsz
    | Rerr (Rraise err) =>
      ∀st hdl sp ig.
        bs.stack = ig++StackPtr sp::CodePtr hdl::st
      ∧ bs.handler = LENGTH st + 1
      ⇒
        ∃s' w. syneq err w ∧
         csg_rel syneq (FST res) s' ∧
         closed_vlabs env s' (bc0++c0) ∧
         code_for_return rd bs (bc0++c0) st hdl sp w s'
    | Rerr Rtimeout_error =>
      ∃bs'. bc_next^* bs bs' ∧ bs'.clock = SOME 0 ∧ bc_fetch bs' = SOME Tick ∧ bs'.output = bs.output
    | _ => T``,
  rw[compile_Cexp_def] >>
  qspecl_then[`LENGTH renv`,`cs.next_label`,`exp`]mp_tac (CONJUNCT1 label_closures_thm) >>
  simp[] >> strip_tac >>
  qspecl_then[`LENGTH renv`,`cs with next_label := nl`,`Ce`]mp_tac compile_code_env_thm >>
  simp[] >>
  discharge_hyps >- (
    simp[ALL_DISTINCT_GENLIST,EVERY_GENLIST] ) >>
  disch_then(Q.X_CHOOSE_THEN`c0`strip_assume_tac) >>
  qspecl_then[`renv`,`TCNonTail`,`rsz`,`cs'`,`Ce`]mp_tac(CONJUNCT1 compile_append_out) >>
  disch_then(Q.X_CHOOSE_THEN`c1`strip_assume_tac) >>
  simp[Abbr`cs''`] >>
  qexists_tac`c0` >> simp[Once SWAP_REVERSE] >>
  conj_tac >- (
    simp[between_labels_def,FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE] >>
    fsrw_tac[DNF_ss][EVERY_MEM,MEM_FILTER,MEM_MAP,is_Label_rwt,between_def] >>
    rw[] >> spose_not_then strip_assume_tac >>
    fsrw_tac[DNF_ss][MEM_GENLIST] >>
    res_tac >> DECIDE_TAC ) >>
  conj_tac >- (
    rfs[code_labels_ok_def,uses_label_thm,EXISTS_REVERSE] >>
    qmatch_assum_abbrev_tac`P ⇒ Q` >>
    `P` by (
      simp[Abbr`P`] >>
      imp_res_tac all_labs_free_labs >>
      fs[all_labs_list_MAP] ) >>
    qunabbrev_tac`P`>>fs[Abbr`Q`] >>
    reverse(rw[])>- metis_tac[] >>
    last_x_assum(qspec_then`l`mp_tac) >>
    simp[] >> strip_tac >> fs[] >>
    qsuff_tac`MEM l (MAP (FST o FST o SND) (free_labs (LENGTH renv) Ce))`>-metis_tac[] >>
    qmatch_assum_abbrev_tac`MEM l a` >>
    qmatch_abbrev_tac`MEM l b` >>
    qsuff_tac`set a ⊆ set b`>-rw[SUBSET_DEF]>>
    unabbrev_all_tac >>
    simp[LIST_TO_SET_FLAT,MAP_MAP_o,LIST_TO_SET_MAP,GSYM IMAGE_COMPOSE] >>
    simp[combinTheory.o_DEF,LAMBDA_PROD] >>
    metis_tac[SIMP_RULE(srw_ss())[combinTheory.o_DEF,LAMBDA_PROD](CONJUNCT1 free_labs_free_labs)] ) >>
  rpt gen_tac >>
  Q.PAT_ABBREV_TAC`bc00A = (X ∨ Y)` >>
  strip_tac >>
  first_x_assum(qspecl_then[`bs`,`bc0`]mp_tac) >>
  simp[] >>
  discharge_hyps >- (
    simp[MEM_MAP,MEM_GENLIST,MEM_FILTER,is_Label_rwt] >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    fsrw_tac[DNF_ss][EVERY_MEM,MEM_FILTER,is_Label_rwt,good_labels_def] >>
    rw[] >> res_tac >> DECIDE_TAC ) >>
  strip_tac >>
  `LENGTH renv = LENGTH env` by (
    fs[Cenv_bs_def,env_renv_def,EVERY2_EVERY] ) >>
  fs[] >>
  qmatch_assum_abbrev_tac`bc_next bs bs0` >>
  qspecl_then[`s`,`env`,`exp`,`res`]mp_tac (CONJUNCT1 Cevaluate_syneq) >>
  simp[] >>
  disch_then(qspecl_then[`$=`,`s`,`env`,`Ce`]mp_tac) >>
  simp[] >>
  disch_then(Q.X_CHOOSE_THEN`Cres`strip_assume_tac) >>
  qspecl_then[`s`,`env`,`Ce`,`Cres`]mp_tac(CONJUNCT1 compile_val) >>
  PairCases_on`Cres`>>simp[]>>
  disch_then(qspecl_then[`rd`,`cs'`,`renv`,`rsz`,`bs0`,`bc0 ++ c0`,`REVERSE c1`,`bc0 ++ c0`,`REVERSE c1`,`[]`]mp_tac) >>
  discharge_hyps >- (
    simp[Abbr`bs0`] >>
    simp[CONJ_ASSOC] >>
    qmatch_abbrev_tac`(A ∧ B) ∧ C` >>
    `B ∧ C` by (
      simp[Abbr`A`,Abbr`B`,Abbr`C`,FILTER_APPEND,ALL_DISTINCT_APPEND] >>
      fsrw_tac[DNF_ss][EVERY_MEM,MEM_FILTER,is_Label_rwt,MEM_MAP,MEM_GENLIST,between_def,good_labels_def] >>
      rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
    simp[Abbr`A`,Abbr`B`,Abbr`C`,GSYM CONJ_ASSOC] >>
    fs[closed_vlabs_def,vlabs_csg_def] >>
    conj_tac >- metis_tac[code_env_cd_append] >>
    conj_tac >- metis_tac[code_env_cd_append] >>
    conj_tac >- metis_tac[code_env_cd_append] >>
    conj_tac >- metis_tac[SUBSET_TRANS] >>
    match_mp_tac Cenv_bs_with_irr >>
    qexists_tac`bs with code := bc0 ++ c0` >> simp[] >>
    Cases_on`bc00 = bc0` >- (
      match_mp_tac Cenv_bs_append_code >>
      HINT_EXISTS_TAC >>
      simp[bc_state_component_equality] ) >>
    `bc0 ++ c0 = bc00` by metis_tac[] >>
    pop_assum SUBST1_TAC >>
    simp[] ) >>
  PairCases_on`res`>>fs[]>>
  strip_tac >>
  Cases_on`res3`>>fs[]>>rfs[]>-(
    rpt HINT_EXISTS_TAC >>
    simp[] >>
    qspecl_then[`s`,`env`,`Ce`,`(((Cres0,Cres1),Cres2),Cres3)`,`bc0++c0`]mp_tac Cevaluate_closed_vlabs >>
    simp[] >>
    discharge_hyps >- (
      fs[EVERY_MEM] >>
      fs[closed_vlabs_def] >>
      `ALL_DISTINCT (FILTER is_Label (bc0 ++ c0))` by (
        simp[FILTER_APPEND,ALL_DISTINCT_APPEND] >>
        fsrw_tac[DNF_ss][good_labels_def,MEM_FILTER,is_Label_rwt,MEM_MAP,MEM_GENLIST,between_def,EVERY_MEM] >>
        rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
      metis_tac[code_env_cd_append] ) >>
    simp[] >> strip_tac >>
    conj_tac >- (
      fs[closed_vlabs_def,SUBSET_DEF] >>
      fs[EVERY_MEM] >>
      rw[] >> res_tac >> TRY(metis_tac[]) >>
      match_mp_tac code_env_cd_append >>
      simp[FILTER_APPEND,ALL_DISTINCT_APPEND] >>
      fsrw_tac[DNF_ss][good_labels_def,MEM_FILTER,is_Label_rwt,MEM_MAP,MEM_GENLIST,between_def,EVERY_MEM] >>
      rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
    rw[] >>
    ntac 4 (pop_assum kall_tac) >>
    pop_assum mp_tac >>
    simp[code_for_push_def] >>
    simp_tac(srw_ss()++DNF_ss)[]>>
    simp[Abbr`bs0`] >>
    map_every qx_gen_tac [`rf`,`rd'`,`ck`,`gv`,`bv`] >>
    strip_tac >>
    map_every qexists_tac [`rf`,`rd'`,`ck`,`gv`,`bv`] >>
    simp[] >>
    simp[Once RTC_CASES1] >>
    disj2_tac >>
    HINT_EXISTS_TAC >>
    simp[] ) >>
  rw[] >>
  reverse BasicProvers.CASE_TAC >> fs[] >- (
    first_x_assum(qspec_then`TCNonTail`mp_tac) >>
    simp[Abbr`bs0`] >>
    metis_tac[RTC_SUBSET,RTC_TRANSITIVE,transitive_def] ) >>
  rpt gen_tac >> strip_tac >>
  rpt HINT_EXISTS_TAC >>
  fs[] >>
  qmatch_assum_abbrev_tac`Cevaluate s env Ce Cres` >>
  qspecl_then[`s`,`env`,`Ce`,`Cres`,`bc0++c0`]mp_tac Cevaluate_closed_vlabs >>
  simp[] >>
  discharge_hyps >- (
    fs[EVERY_MEM] >>
    fs[closed_vlabs_def] >>
    `ALL_DISTINCT (FILTER is_Label (bc0 ++ c0))` by (
      simp[FILTER_APPEND,ALL_DISTINCT_APPEND] >>
      fsrw_tac[DNF_ss][good_labels_def,MEM_FILTER,is_Label_rwt,MEM_MAP,MEM_GENLIST,between_def,EVERY_MEM] >>
      rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
    metis_tac[code_env_cd_append] ) >>
  rw[Abbr`Cres`] >>
  first_x_assum(qspec_then`TCNonTail`mp_tac) >>
  simp[Abbr`bs0`] >>
  disch_then(qspec_then`ig`mp_tac) >>
  simp[] >>
  simp[code_for_return_def] >>
  simp_tac(srw_ss()++DNF_ss)[]>>
  map_every qx_gen_tac [`bv`,`rf`,`rd'`,`gv`,`ck`] >>
  strip_tac >>
  map_every qexists_tac [`bv`,`rf`,`rd'`,`gv`,`ck`] >>
  simp[] >>
  simp[Once RTC_CASES1] >>
  disj2_tac >>
  HINT_EXISTS_TAC >>
  simp[] )

(* env_rs *)

val good_globals_def = Define`
  good_globals e (m:num) l g ⇔ l = m ∧ g = m ∧
  (∀n. n ∈ FRANGE (SND e) ∨
       n ∈ BIGUNION (IMAGE FRANGE (FRANGE (FST e))) ⇒
       n < m)`

val i2_Cv_def = Define`
  i2_Cv exh v Cv ⇔
    ∃vp.
      v_pat (v_to_pat (v_to_exh exh v)) vp ∧
      syneq (v_to_Cv vp) Cv`

val env_rs_def = Define`
  env_rs ((envM,envC,envE):all_env) ((cnt,s):v count_store) (genv,(tids,gtagenv),rd)
    (rs:compiler_state) (bs:bc_state)
  ⇔
    good_labels rs.rnext_label bs.code ∧
    good_globals rs.globals_env rs.next_global (LENGTH bs.globals) (LENGTH genv) ∧
    bs.stack = [] ∧
    ∃s1 s2 genv2 Cs Cg.
      to_i1_invariant
        genv (FST rs.globals_env) (SND rs.globals_env)
        envM envE (cnt,s) (cnt,s1) (set (MAP FST envM)) ∧
      to_i2_invariant
        tids envC rs.exh rs.contags_env gtagenv
        (cnt,s1) (cnt,s2) genv genv2 ∧
      LIST_REL (i2_Cv rs.exh) s2 Cs ∧
      LIST_REL (OPTREL (i2_Cv rs.exh)) genv2 Cg ∧
      closed_vlabs [] ((cnt,Cs),Cg) bs.code ∧
      Cenv_bs rd ((cnt,Cs),Cg) [] [] 0 bs`

val env_rs_empty = store_thm("env_rs_empty",
  ``∀envs s cs genv tids gtagenv rd grd bs ck.
    bs.stack = [] ∧ bs.globals = [] ∧ FILTER is_Label bs.code = [] ∧
    (∀n. bs.clock = SOME n ⇒ n = ck) ∧ envs = ([],init_envC,[]) ∧ s = (ck,[]) ∧
    grd = ([],(tids,gtagenv),rd) ∧
    rd.sm = [] ∧ rd.cls = FEMPTY ∧ cs = init_compiler_state ⇒
    env_rs envs s grd cs bs``,
  rpt gen_tac >>
  simp[env_rs_def,to_i1_invariant_def,to_i2_invariant_def] >>
  strip_tac >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  rw[init_compiler_state_def,get_tagenv_def,cenv_inv_def] >>
  rw[Once v_to_i1_cases] >> rw[Once v_to_i1_cases] >>
  rw[Once s_to_i1_cases] >> rw[Once s_to_i1'_cases] >> rw[Once v_to_i1_cases] >>
  rw[Once genv_to_i2_cases] >>
  simp[Once s_to_i2_cases] >> simp[Once s_to_i2'_cases] >> simp[Once v_to_i2_cases] >>
  simp[Cenv_bs_def,env_renv_def,s_refs_def,good_rd_def,FEVERY_ALL_FLOOKUP] >>
  simp[all_vlabs_csg_def,vlabs_csg_def,closed_vlabs_def] >>
  cheat)

(* TODO: move *)
val to_i1_invariant_change_clock = store_thm("to_i1_invariant_change_clock",
  ``to_i1_invariant genv mods tops menv env s s_i1 mod_names ∧
    SND s' = SND s ∧ SND s_i1' = SND s_i1 ∧ FST s' = FST s_i1'
    ⇒
    to_i1_invariant genv mods tops menv env s' s_i1' mod_names``,
  simp[to_i1_invariant_def] >>
  rw[Once s_to_i1_cases] >>
  rw[Once s_to_i1_cases] >>
  metis_tac[pair_CASES,PAIR_EQ,SND,FST])

(* TODO: move *)
val to_i2_invariant_change_clock = store_thm("to_i2_invariant_change_clock",
  ``to_i2_invariant tids envC exh tagenv_st gtagenv s s_i2 genv genv_i2 ∧
    SND s' = SND s ∧ SND s_i2' = SND s_i2 ∧ FST s' = FST s_i2'
    ⇒
    to_i2_invariant tids envC exh tagenv_st gtagenv s' s_i2' genv genv_i2``,
  simp[to_i2_invariant_def] >>
  rw[Once s_to_i2_cases] >>
  rw[Once s_to_i2_cases] >>
  metis_tac[pair_CASES,PAIR_EQ,SND,FST])

val env_rs_change_clock = store_thm("env_rs_change_clock",
   ``∀env cs grd rs bs cs' ck' bs' new_clock.
     env_rs env cs grd rs bs ∧ cs' = (ck',SND cs) ∧
     (bs' = bs with clock := new_clock) ∧
     (new_clock = NONE ∨ new_clock = SOME ck')
     ⇒
     env_rs env cs' grd rs bs'``,
  qx_gen_tac`p` >> PairCases_on`p` >>
  qx_gen_tac`q` >> PairCases_on`q` >>
  qx_gen_tac`r` >> PairCases_on`r` >>
  simp[env_rs_def] >>
  rpt gen_tac >>
  Q.PAT_ABBREV_TAC`d = (a ∨ b)` >>
  strip_tac >>
  map_every qexists_tac[`s1`] >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_tac >- (
    metis_tac[to_i1_invariant_change_clock,FST,SND] ) >>
  map_every qexists_tac[`s2`,`genv2`] >>
  conj_tac >- (
    metis_tac[to_i2_invariant_change_clock,FST,SND] ) >>
  simp[PULL_EXISTS] >>
  rpt HINT_EXISTS_TAC >>
  simp[] >>
  conj_tac >- (
    fs[all_vlabs_csg_def,vlabs_csg_def,closed_vlabs_def] >>
    metis_tac[] ) >>
  match_mp_tac Cenv_bs_change_store >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  simp[bc_state_component_equality] >>
  fs[Cenv_bs_def,s_refs_def,Abbr`d`,good_rd_def])

(*
val env_rs_change_store = store_thm("env_rs_change_store",
  ``∀env cs rs rd bs rd' cs' Cs' bs' ck' rf'.
    env_rs env cs rs rd bs ∧
    (IS_SOME ck' ⇒ ck' = SOME (FST cs')) ∧
    bs' = bs with <| refs := rf'; clock := ck'|> ∧
    LENGTH (SND cs) ≤ LENGTH (SND cs') ∧
    s_refs rd' (FST cs',Cs') bs' ∧
    LIST_REL syneq (vs_to_Cvs (MAP FST o_f rs.rmenv) (cmap rs.contab) (SND cs')) Cs' ∧
    DRESTRICT bs.refs (COMPL (set rd.sm)) ⊑ DRESTRICT rf' (COMPL (set rd'.sm)) ∧
    rd.sm ≼ rd'.sm ∧ rd.cls ⊑ rd'.cls ∧
    EVERY all_vlabs Cs' ∧
    (∀cd. cd ∈ vlabs_list Cs' ⇒ code_env_cd (MAP SND o_f rs.rmenv) bs.code cd)
    ⇒
    env_rs env cs' rs rd' bs'``,
  rw[] >>
  fs[env_rs_def,LET_THM] >> rfs[] >> fs[] >>
  rpt HINT_EXISTS_TAC >> simp[] >>
  qexists_tac`Cs'` >>
  fs[vs_to_Cvs_MAP] >>
  simp[CONJ_ASSOC] >>
  reverse conj_tac >- (
    match_mp_tac bytecodeProofTheory.Cenv_bs_change_store >>
    map_every qexists_tac[`rd`,`(FST cs,Cs)`,`bs`,`rf'`,`ck'`] >>
    simp[bytecodeTheory.bc_state_component_equality] ) >>
  fs[closed_Clocs_def,closed_vlabs_def] >>
  fs[EVERY2_EVERY] >>
  full_simp_tac pure_ss [SUBSET_DEF,IN_COUNT] >>
  metis_tac[LESS_LESS_EQ_TRANS])
*)

val env_rs_with_bs_irr = store_thm("env_rs_with_bs_irr",
  ``∀env cs grd rs bs bs'.
    env_rs env cs grd rs bs
    ∧ bs'.globals = bs.globals
    ∧ bs'.stack = bs.stack
    ∧ bs'.refs = bs.refs
    ∧ bs'.clock = bs.clock
    ∧ bs'.code = bs.code
    ∧ bs'.inst_length = bs.inst_length
    ⇒
    env_rs env cs grd rs bs'``,
  simp[FORALL_PROD] >> rw[env_rs_def] >>
  rpt(first_assum(match_exists_tac o concl) >> simp[]) >>
  match_mp_tac Cenv_bs_with_irr >>
  HINT_EXISTS_TAC >> rfs[])

val env_rs_append_code = store_thm("env_rs_append_code",
  ``∀env cs grd rs bs bs' rs' c nl.
    env_rs env cs grd rs bs ∧
    bs' = bs with code := bs.code ++ c ∧
    rs' = rs with rnext_label := nl ∧
    good_labels nl bs'.code
    ⇒
    env_rs env cs grd rs' bs'``,
  simp[FORALL_PROD] >>
  simp[env_rs_def] >>
  rpt gen_tac >> strip_tac  >>
  rpt(first_assum(match_exists_tac o concl) >> simp[]) >>
  conj_tac >- (
    fs[closed_vlabs_def] >> rw[]>>
    match_mp_tac code_env_cd_append >>
    fs[good_labels_def]) >>
  match_mp_tac Cenv_bs_append_code >>
  metis_tac[])

val env_rs_can_Print = store_thm("env_rs_can_Print",
  ``∀env cs grd rs bs n v.
    env_rs env cs grd rs bs ∧
    EL n bs.globals = SOME v ∧
    n ∈ (FRANGE (SND rs.globals_env) ∪
         BIGUNION (IMAGE FRANGE (FRANGE (FST rs.globals_env))))
    ⇒
    can_Print v``,
  simp_tac std_ss [FORALL_PROD] >>
  rpt gen_tac >>
  Q.PAT_ABBREV_TAC`ss:num set = x ∪ y` >>
  rw[env_rs_def,Cenv_bs_def,s_refs_def] >>
  rfs[EVERY2_EVERY] >>
  fs[EVERY_MEM,MEM_ZIP,PULL_EXISTS,optionTheory.OPTREL_def] >>
  fs[good_globals_def] >>
  `n < LENGTH bs.globals` by (
    fs[Abbr`ss`] >> res_tac >> fs[] >> metis_tac[] ) >>
  match_mp_tac (GEN_ALL Cv_bv_can_Print) >>
  metis_tac[optionTheory.NOT_SOME_NONE,optionTheory.SOME_11])

(* FV *)

val FV_def = tDefine "FV"`
  (FV (Raise e) = FV e) ∧
  (FV (Handle e pes) = FV e ∪ FV_pes pes) ∧
  (FV (Lit _) = {}) ∧
  (FV (Con _ ls) = FV_list ls) ∧
  (FV (Var id) = {id}) ∧
  (FV (Fun x e) = FV e DIFF {Short x}) ∧
  (FV (Uapp _ e) = FV e) ∧
  (FV (App _ e1 e2) = FV e1 ∪ FV e2) ∧
  (FV (Log _ e1 e2) = FV e1 ∪ FV e2) ∧
  (FV (If e1 e2 e3) = FV e1 ∪ FV e2 ∪ FV e3) ∧
  (FV (Mat e pes) = FV e ∪ FV_pes pes) ∧
  (FV (Let xo e b) = FV e ∪ (FV b DIFF (case xo of NONE => {} | SOME x => {Short x}))) ∧
  (FV (Letrec defs b) =
     let ds = set (MAP (Short o FST) defs) in
     FV_defs ds defs ∪ (FV b DIFF ds)) ∧
  (FV_list [] = {}) ∧
  (FV_list (e::es) = FV e ∪ FV_list es) ∧
  (FV_pes [] = {}) ∧
  (FV_pes ((p,e)::pes) =
     (FV e DIFF (IMAGE Short (set (pat_bindings p [])))) ∪ FV_pes pes) ∧
  (FV_defs _ [] = {}) ∧
  (FV_defs ds ((_,x,e)::defs) =
     (FV e DIFF ({Short x} ∪ ds)) ∪ FV_defs ds defs)`
(WF_REL_TAC `inv_image $< (λx. case x of
   | INL e => exp_size e
   | INR (INL es) => exp6_size es
   | INR (INR (INL pes)) => exp3_size pes
   | INR (INR (INR (_,defs))) => exp1_size defs)`)
val _ = export_rewrites["FV_def"]

val _ = Parse.overload_on("SFV",``λe. {x | Short x ∈ FV e}``)

val FV_dec_def = Define`
  (FV_dec (Dlet p e) = FV (Mat e [(p,Lit ARB)])) ∧
  (FV_dec (Dletrec defs) = FV (Letrec defs (Lit ARB))) ∧
  (FV_dec (Dtype _) = {}) ∧
  (FV_dec (Dexn _ _) = {})`
val _ = export_rewrites["FV_dec_def"]

val _ = Parse.overload_on("new_decs_vs",``λdecs. FLAT (REVERSE (MAP new_dec_vs decs))``)

val FV_decs_def = Define`
  (FV_decs [] = {}) ∧
  (FV_decs (d::ds) = FV_dec d ∪ ((FV_decs ds) DIFF (set (MAP Short (new_dec_vs d)))))`

val FV_top_def = Define`
  (FV_top (Tdec d) = FV_dec d) ∧
  (FV_top (Tmod mn _ ds) = FV_decs ds)`
val _ = export_rewrites["FV_top_def"]

(* compile_top *)

val global_dom_def = Define`
  global_dom (me,e) = IMAGE Short (FDOM e) ∪ { Long m x | ∃e. FLOOKUP me m = SOME e ∧ x ∈ FDOM e}`

val FILTER_F = store_thm("FILTER_F",
  ``∀ls. FILTER (λx. F) ls = []``,
  Induct >> simp[])
val _ = export_rewrites["FILTER_F"]

val compile_top_labels = store_thm("compile_top_labels",
  ``∀types rs top.
      FV_top top ⊆ global_dom rs.globals_env
      ⇒
      between_labels (SND(compile_top types rs top)) rs.rnext_label (FST(compile_top types rs top)).rnext_label ∧
      code_labels_ok (SND(compile_top types rs top))``,
   simp[compile_top_def,UNCURRY,pair_CASE_def] >>
   rpt gen_tac >> strip_tac >>
   specl_args_of_then``compile_Cexp``compile_Cexp_thm mp_tac >>
   discharge_hyps >- (
     simp[] >>
     qmatch_abbrev_tac`x = []` >>
     qsuff_tac`set x ⊆ {}` >- rw[] >>
     qunabbrev_tac`x` >>
     specl_args_of_then``exp_to_pat``(CONJUNCT1 free_vars_pat_exp_to_pat)mp_tac >>
     match_mp_tac(METIS_PROVE[]``(p ∧ (p ∧ q ⇒ r)) ⇒ ((p ⇒ q) ⇒ r)``) >>
     conj_tac >- cheat >>
     strip_tac >> rfs[] ) >>
   Q.PAT_ABBREV_TAC`Cexp = exp_to_Cexp Z` >>
   simp[] >> strip_tac >>
   Cases_on`types`>>simp[compile_print_top_def] >- (
     simp[GSYM REVERSE_APPEND] >>
     fs[between_labels_def,FILTER_REVERSE,ALL_DISTINCT_REVERSE,MAP_REVERSE,EVERY_REVERSE,EVERY_MAP,EVERY_FILTER] >>
     fs[FILTER_APPEND,ALL_DISTINCT_APPEND] >> metis_tac[] ) >>
   Cases_on`top`>>simp[compile_print_top_def,FOLDL_emit_thm] >- (
     reverse conj_tac >- (
       REWRITE_TAC[GSYM APPEND_ASSOC] >>
       match_mp_tac code_labels_ok_append >>
       simp[code_labels_ok_REVERSE] >>
       rpt(match_mp_tac code_labels_ok_cons >> simp[]) >>
       REWRITE_TAC[GSYM REVERSE_APPEND] >>
       simp[code_labels_ok_REVERSE] ) >>
     fs[between_labels_def,FILTER_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE,MAP_REVERSE,EVERY_REVERSE,EVERY_MAP,ALL_DISTINCT_APPEND,
        MEM_FILTER,is_Label_rwt,PULL_EXISTS,MEM_MAP,EVERY_FILTER] >>
     rw[] >> simp[FILTER_MAP,combinTheory.o_DEF] ) >>
   specl_args_of_then``compile_print_dec``(CONV_RULE SWAP_FORALL_CONV compile_print_dec_thm) mp_tac >>
   simp[] >> strip_tac >>
   simp[] >>
   reverse conj_tac >- (
     REWRITE_TAC[GSYM APPEND_ASSOC] >>
     match_mp_tac code_labels_ok_append >>
     simp[code_labels_ok_REVERSE] >>
     REWRITE_TAC[GSYM REVERSE_APPEND] >>
     simp[code_labels_ok_REVERSE] ) >>
   fs[between_labels_def,FILTER_APPEND,FILTER_REVERSE,ALL_DISTINCT_APPEND,ALL_DISTINCT_REVERSE,MAP_REVERSE,EVERY_REVERSE] >>
   fs[GSYM FILTER_EQ_NIL,combinTheory.o_DEF])

val new_top_vs_def = Define`
  (new_top_vs (Tdec dec) = new_dec_vs dec) ∧
  (new_top_vs (Tmod _ _ _) = [])`

val labels_tac =
  fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,ALL_DISTINCT_REVERSE,FILTER_REVERSE
                  ,good_labels_def,between_labels_def,MEM_FILTER,EVERY_MEM,between_def
                  ,MEM_MAP,is_Label_rwt] >>
  rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC

fun sorter [] l2 = l2
  | sorter (s::l1) l2 =
    let
      val (s,l2) = partition (equal s o fst o dest_var) l2
    in
      s @ (sorter l1 l2)
    end

(* TODO: move *)
val genv_to_i2_LENGTH_EQ = store_thm("genv_to_i2_LENGTH_EQ",
  ``∀x y z. genv_to_i2 x y z ⇒ LENGTH y = LENGTH z``,
  ho_match_mp_tac genv_to_i2_ind >> simp[])

val v_bv_def = Define`
  v_bv (genv,gtagenv,exh,pp) v bv ⇔
    ∃v1 v2 Cv.
    v_to_i1 genv v v1 ∧
    v_to_i2 gtagenv v1 v2 ∧
    i2_Cv exh v2 Cv ∧
    Cv_bv pp Cv bv`

val compile_top_thm = store_thm("compile_top_thm",
  ``∀ck env stm top res. evaluate_top ck env stm top res ⇒
     ∀rs types grd rs' bc bs bc0.
      env_rs env (FST stm) grd rs (bs with code := bc0) ∧
      (FST(FST(SND grd)) = FST (SND stm)) ∧
      (compile_top types rs top = (rs',bc)) ∧
      (IS_SOME types ⇒ set (new_top_vs top) ⊆ FDOM (THE types)) ∧
      (bs.code = bc0 ++ REVERSE bc) ∧
      (bs.pc = next_addr bs.inst_length bc0) ∧
      ck ∧ IS_SOME bs.clock
      ⇒
      case res of
      | ((s,tdecls,mdecls),envC,Rval(envM,envE)) =>
        ∃bs' grd'.
        bc_next^* bs bs' ∧
        bs'.pc = next_addr bs'.inst_length (bc0 ++ bc) ∧
        bs'.output = bs.output ++
          (case types of NONE => "" | SOME types =>
             (print_result types top envC (Rval(envM,envE)))) ∧
        bs'.stack = (Block (block_tag+none_tag) [])::bs.stack ∧
        env_rs (envM++FST env,merge_envC envC (FST(SND env)),envE ++ (SND(SND env)))
          s grd' rs' (bs' with stack := bs.stack)
      | ((s,tdecls,mdecls),envC,Rerr(Rraise err)) =>
        ∃bv bs' grd'.
        bc_next^*bs bs' ∧
        bs'.stack = (Block (block_tag+some_tag) [bv])::bs.stack ∧
        bs'.pc = 0 ∧
        bs'.output = bs.output ∧
        v_bv (FST grd', SND(FST(SND grd')), rs'.exh, mk_pp (SND(SND grd')) bs') err bv ∧
        env_rs env s grd' rs' (bs' with stack := bs.stack)
      | _ => T``,
  ho_match_mp_tac evaluate_top_ind >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >>
    simp[compile_top_def] >>
    Q.PAT_ABBREV_TAC`non = (none_tag,(X:tid_or_exn option))` >>
    Q.PAT_ABBREV_TAC`som = (some_tag,(X:tid_or_exn option))` >>
    strip_tac >>
    `∃m10 m20. rs.globals_env = (m10,m20)` by simp[GSYM EXISTS_PROD] >> fs[] >>
    qspecl_then[`m10`,`m20`,`Tdec d`]mp_tac top_to_i1_correct >>
    PairCases_on`grd`>>PairCases_on`env`>>PairCases_on`s1`>>fs[env_rs_def] >>
    REWRITE_TAC[Once CONJ_COMM] >>
    REWRITE_TAC[Once (GSYM CONJ_ASSOC)] >>
    REWRITE_TAC[Once (GSYM AND_IMP_INTRO)] >>
    disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
    `∃v m1 m2 p1. top_to_i1 rs.next_global m10 m20 (Tdec d) = (v,m1,m2,p1)` by simp[GSYM EXISTS_PROD] >> fs[] >>
    `rs.next_global = LENGTH grd0` by ( fs[good_globals_def] ) >> fs[] >>
    simp[Once evaluate_top_cases] >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    disch_then(mp_tac o CONJUNCT1) >>
    disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
    disch_then(qx_choosel_then[`s2_i1`,`new_genv`]strip_assume_tac) >>
    `∃c exh p. prompt_to_i2 rs.contags_env p1 = (c,exh,p)` by simp[GSYM EXISTS_PROD] >> fs[] >>
    first_assum (mp_tac o (MATCH_MP (
      CONV_RULE (
        ONCE_REWRITE_CONV[CONJ_ASSOC] THENC
        ONCE_REWRITE_CONV[CONJ_COMM] THENC
        ONCE_REWRITE_CONV[GSYM CONJ_ASSOC] THENC
        ONCE_REWRITE_CONV[GSYM AND_IMP_INTRO]) prompt_to_i2_correct))) >>
    REWRITE_TAC[Once EQ_SYM_EQ] >>
    REWRITE_TAC[Once (GSYM AND_IMP_INTRO)] >>
    disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
    REWRITE_TAC[Once (GSYM AND_IMP_INTRO)] >>
    disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
    simp[] >>
    disch_then(qx_choosel_then[`new_genv_i2`,`s2_i2`,`gtagenv2`]strip_assume_tac) >>
    `∃n e. prompt_to_i3 non som (LENGTH grd0) p = (n,e)` by simp[GSYM EXISTS_PROD] >> fs[] >>
    first_assum (mp_tac o (MATCH_MP (
      ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
        prompt_to_i3_correct))) >>
    simp[] >>
    `LENGTH genv2 = LENGTH grd0` by (
      fs[to_i2_invariant_def] >>
      imp_res_tac genv_to_i2_LENGTH_EQ >>
      fs[] ) >>
    simp[] >>
    simp[Once result_to_i3_cases] >>
    strip_tac >>
    first_assum (mp_tac o MATCH_MP (CONJUNCT1 exp_to_exh_correct)) >>
    simp[] >> strip_tac >>
    first_assum (mp_tac o MATCH_MP (CONJUNCT1 exp_to_pat_correct)) >>
    simp[result_to_exh_def] >>
    disch_then(qx_choosel_then[`res4`]strip_assume_tac) >>
    first_assum (mp_tac o MATCH_MP (CONJUNCT1 exp_to_Cexp_correct)) >>
    simp[] >>
    discharge_hyps_keep >- (
      simp[v_to_exh_def] >>
      specl_args_of_then``exp_to_pat``(CONJUNCT1 free_vars_pat_exp_to_pat)mp_tac >>
      cheat (* closed, free_vars, ... might need more in env_rs? *) ) >>
    disch_then(qx_choosel_then[`Cres0`]strip_assume_tac) >>
    `∀x. env_to_exh x [] = []` by simp[v_to_exh_def] >> fs[] >>
    qpat_assum`X = bc`mp_tac >>
    specl_args_of_then``compile_Cexp`` compile_Cexp_thm mp_tac >>
    simp[] >> strip_tac >>
    first_assum(mp_tac o MATCH_MP (CONJUNCT1 Cevaluate_syneq)) >>
    simp[] >>
    qmatch_assum_abbrev_tac`closed_vlabs [] Csg bc0` >>
    Q.PAT_ABBREV_TAC`Cexp = exp_to_Cexp Z` >>
    disch_then(qspecl_then[`$=`,`Csg`,`[]`,`Cexp`]mp_tac) >>
    discharge_hyps >- (
      simp[syneq_exp_refl] >>
      fs[Abbr`Csg`,csg_rel_unpair,map_count_store_genv_def,store_to_exh_def] >>
      simp[MAP_MAP_o,optionTheory.OPTION_MAP_COMPOSE,combinTheory.o_DEF] >>
      simp[EVERY2_MAP] >>
      conj_tac >- (
        match_mp_tac (MP_CANON (GEN_ALL EVERY2_mono)) >>
        HINT_EXISTS_TAC >>
        simp[i2_Cv_def] >>
        cheat (* the extra exh is in the way - not sure if it's harmless or not *) ) >>
      match_mp_tac (MP_CANON (GEN_ALL EVERY2_mono)) >>
      HINT_EXISTS_TAC >>
      simp[i2_Cv_def,optionTheory.OPTREL_def] >>
      Cases >> simp[PULL_EXISTS] >>
      cheat (* same problem *) ) >>
    strip_tac >>
    first_x_assum(fn th => first_assum (mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    ONCE_REWRITE_TAC[CONJ_COMM] >>
    ONCE_REWRITE_TAC[GSYM CONJ_ASSOC] >>
    ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO] >>
    disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
    match_mp_tac SWAP_IMP >> strip_tac >>
    simp[] >>
    cheat) >> cheat)

(*
val compile_top_divergence = store_thm("compile_top_divergence",
  ``∀menv cenv s env top rs rd ck types bc0 bs ss sf code. (∀res. ¬evaluate_top menv cenv s env top res) ∧
      closed_top menv cenv s env top
      ∧ (∀mn spec ds. top = Tmod mn spec ds ⇒
          ∀i. i < LENGTH ds ⇒
            (∀tds. (EL i ds = Dtype tds) ⇒ check_dup_ctors (SOME mn) (decs_to_cenv (SOME mn) (TAKE i ds) ++ cenv) tds) ∧
            (∀cn ts. (EL i ds = Dexn cn ts) ⇒ mk_id (SOME mn) cn ∉ set (MAP FST (decs_to_cenv (SOME mn) (TAKE i ds) ++ cenv)))) ∧
      env_rs menv cenv (ck,s) env rs (LENGTH bs.stack) rd (bs with code := bc0) ∧
      (compile_top types rs top = (ss,sf,code)) ∧
      bs.code = bc0 ++ REVERSE code ∧
      bs.pc = next_addr bs.inst_length bc0 ∧
      IS_SOME bs.clock ∧
      good_labels rs.rnext_label bc0
      ⇒
      ∃bs'. bc_next^* bs bs' ∧ bc_fetch bs' = SOME Tick ∧ bs'.clock = SOME 0 ∧ bs'.output = bs.output``,
  rw[closed_top_def] >>
  Cases_on`top`>- (
    fs[Once evaluate_top_cases] >>
    qmatch_assum_rename_tac`compile_top types rs (Tmod mn specs ds) = X`["X"] >>
    Cases_on`∃r. evaluate_decs (SOME mn) menv cenv s env ds r`>>fs[]>-(
      PairCases_on`r`>>fs[]>>
      Cases_on`r2`>>fs[]>>
      TRY(PairCases_on`a`)>>fs[FORALL_PROD]>>
      metis_tac[] ) >>
    qabbrev_tac`p = compile_decs_wrap (SOME mn) rs ds` >>
    PairCases_on`p` >>
    fs[compile_top_def,LET_THM] >>
    fs[FOLDL_emit_thm] >>
    qspecl_then[`SOME mn`,`menv`,`cenv`,`s`,`env`,`ds`,`rs`]mp_tac compile_decs_wrap_divergence >>
    simp[] >>
    qmatch_assum_abbrev_tac`pc ++ p4.out = code` >>
    disch_then(qspecl_then[`ck`,`bs with code := bc0 ++ REVERSE p4.out`,`bc0`]mp_tac) >>
    simp[] >>
    disch_then(qspecl_then[`rd`]mp_tac) >>
    simp[] >>
    discharge_hyps >- metis_tac[] >>
    disch_then(qx_choosel_then[`bs1`]strip_assume_tac) >>
    `bc_next^* bs (bs1 with code := bs.code)` by (
      match_mp_tac RTC_bc_next_append_code >>
      qmatch_assum_abbrev_tac`bc_next^* bs0 bs1` >>
      map_every qexists_tac[`bs0`,`bs1`] >>
      simp[bc_state_component_equality,Abbr`bs0`] >>
      BasicProvers.VAR_EQ_TAC >> simp[] >>
      imp_res_tac RTC_bc_next_preserves >> fs[] ) >>
    HINT_EXISTS_TAC >> simp[] >>
    fs[bc_fetch_def] >>
    BasicProvers.VAR_EQ_TAC >>
    imp_res_tac RTC_bc_next_preserves >> fs[] >>
    simp[REVERSE_APPEND] >>
    match_mp_tac bc_fetch_aux_append_code >>
    simp[] ) >>
  fs[Once evaluate_top_cases] >>
  Cases_on`∃r. evaluate_decs NONE menv cenv s env [d] r`>>fs[]>-(
    `∃res. r = (FST r,(case res of Rval (x,y) => x | Rerr _ => []),map_result SND res)` by (
      PairCases_on`r`>>simp[]>>
      Cases_on`r2` >- (
        qexists_tac`Rval (r1,a)` >> simp[] ) >>
      qexists_tac`Rerr e` >> simp[] >>
      Cases_on`d`>>fs[Once evaluate_decs_cases,libTheory.emp_def,libTheory.merge_def] >>
      fs[Once evaluate_decs_cases,libTheory.merge_def,libTheory.emp_def] >>
      fs[Once evaluate_dec_cases,libTheory.merge_def,libTheory.emp_def] >>
      fs[semanticPrimitivesTheory.combine_dec_result_def] ) >>
    `evaluate_dec NONE menv cenv s env d (FST r,res)` by metis_tac[evaluate_dec_decs] >>
    Cases_on`res`>>fs[] >>
    TRY(PairCases_on`a`)>>fs[FORALL_PROD]>>
    metis_tac[] ) >>
  qabbrev_tac`p = compile_decs_wrap NONE rs [d]` >>
  PairCases_on`p` >>
  fs[compile_top_def,LET_THM] >>
  qspecl_then[`NONE`,`menv`,`cenv`,`s`,`env`,`[d]`,`rs`]mp_tac compile_decs_wrap_divergence >>
  simp[] >>
  qspecl_then[`d`,`types`,`p4`]mp_tac compile_print_dec_thm >>
  simp[] >> strip_tac >>
  qmatch_assum_abbrev_tac`code = pc ++ p4.out` >>
  disch_then(qspecl_then[`ck`,`bs with code := bc0 ++ REVERSE p4.out`,`bc0`]mp_tac) >>
  simp[] >>
  disch_then(qspecl_then[`rd`]mp_tac) >>
  simp[FV_decs_def] >>
  discharge_hyps >- (
    simp[decs_to_cenv_def,decs_cns_def] >> rw[] >>
    fs[Once evaluate_dec_cases] >>
    spose_not_then strip_assume_tac >> fs[] >>
    fs[Once evaluate_decs_cases] >>
    fs[Once evaluate_dec_cases] >>
    metis_tac[ALOOKUP_NONE]) >>
  disch_then(qx_choosel_then[`bs1`]strip_assume_tac) >>
  `bc_next^* bs (bs1 with code := bs.code)` by (
    match_mp_tac RTC_bc_next_append_code >>
    qmatch_assum_abbrev_tac`bc_next^* bs0 bs1` >>
    map_every qexists_tac[`bs0`,`bs1`] >>
    simp[bc_state_component_equality,Abbr`bs0`] >>
    BasicProvers.VAR_EQ_TAC >> simp[] >>
    imp_res_tac RTC_bc_next_preserves >> fs[] ) >>
  HINT_EXISTS_TAC >> simp[] >>
  fs[bc_fetch_def] >>
  BasicProvers.VAR_EQ_TAC >>
  imp_res_tac RTC_bc_next_preserves >> fs[] >>
  simp[REVERSE_APPEND] >>
  match_mp_tac bc_fetch_aux_append_code >>
  simp[] )
*)

val _ = export_theory()

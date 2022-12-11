(*
  Formalization of the maximum common induced subgraph problem
*)
open preamble pbcTheory graph_basicTheory pbc_normaliseTheory;

val _ = new_theory "mcis";

(* Additional graph notions *)

(* Vertex a is connected to vertex b with respect to vertices vs and edges e
   iff a R* b where R* is the induced adjacency relation
*)
Definition is_connected_def:
  is_connected vs e a b ⇔
  (λx y. y ∈ vs ∧ is_edge e x y)꙳ a b
End

(* The vertex subset vs is connected if vertices are pairwise connected *)
Definition connected_subgraph_def:
  connected_subgraph vs e ⇔
  ∀a b. a ∈ vs ∧ b ∈ vs ⇒ is_connected vs e a b
End

Definition is_walk_def:
  (is_walk ep a b [] ⇔ a = b) ∧
  (is_walk ep a b (p::ps) ⇔ (is_edge ep a p ∧ is_walk ep p b ps))
End

(* Construct an explicit walk *)
Theorem is_connected_is_walk:
  ∀a b.
  is_connected vs e a b ⇒
  ∃walk.
    set walk ⊆ vs ∧ is_walk e a b walk
Proof
  simp[is_connected_def]>>
  ho_match_mp_tac RTC_INDUCT>>rw[]
  >-
    (qexists_tac`[]`>>simp[is_walk_def])>>
  qexists_tac`a'::walk`>>simp[is_walk_def]
QED

Theorem is_walk_is_connected:
  ∀walk a b.
  set walk ⊆ vs ∧ is_walk e a b walk ⇒
  is_connected vs e a b
Proof
  Induct>>rw[is_walk_def]
  >- simp[is_connected_def]>>
  fs[]>>
  first_x_assum drule>>
  simp[is_connected_def]>>
  strip_tac>>
  simp[Once RTC_CASES1]>>
  metis_tac[]
QED

(*
  Given graphs G_p := (vp,ep) , G_t := (vt,et)
  f is an injective partial map from v_p to v_t
  - dom f = vs (vs is the set of mapped vertices)
  - |vs| ≥ k (i.e., at least k vertices are mapped)
  - preserving adjacency and non-adjacency
*)
Definition injective_partial_map_def:
  injective_partial_map f vs k ((vp,ep):graph) ((vt,et):graph) ⇔
  vs ⊆ count vp ∧ CARD vs ≥ k ∧
  INJ f vs (count vt) ∧
  (∀a b. a ∈ vs ∧ b ∈ vs ∧ is_edge ep a b ⇒ is_edge et (f a) (f b)) ∧
  (∀a b. a ∈ vs ∧ b ∈ vs ∧ ¬(is_edge ep a b) ⇒ ¬ is_edge et (f a) (f b))
End

(* Encoding *)
Datatype:
  enc =
    Walk num num num (* Walk f g k indicates a walk of length 2^k from f to g *)
  | Aux num num num num (* Aux f g h k are auxiliaries used to encode Walk *)
  | Unmapped num (* x_{f,bot} *)
  | Mapped num num (* x_{f,g} *)
End

(* For each a in vp, either a is unassigned or a is assigned to exactly one vertex
  v in vt *)
Definition has_mapping_def:
  has_mapping a vt =
  (Equal,
    (1, Pos (Unmapped a)) ::
    GENLIST (λv. (1, Pos (Mapped a v))) vt,
    1): enc pbc
End

Definition all_has_mapping_def:
  all_has_mapping vp vt =
  GENLIST (λa. has_mapping a vt) vp
End

Definition one_one_def:
  one_one u vp =
  (GreaterEqual,
    (GENLIST (λb. (1, Neg (Mapped b u))) vp),
    (&vp-1)): enc pbc
End

Definition all_one_one_def:
  all_one_one vp vt =
  GENLIST (λu. one_one u vp) vt
End

Definition edge_map_def:
  edge_map (a,b) u et =
  if a = b then [] else
  [(GreaterEqual,
    (1,Neg (Mapped a u)) ::
    (1,Pos (Unmapped b)) ::
    MAP (λv. (1,Pos (Mapped b v))) (neighbours et u),
    1):enc pbc]
End

Definition not_edge_map_def:
  not_edge_map (a,b) u vt et =
  if a = b then []
  else
  [(GreaterEqual,
    (1,Neg (Mapped a u)) ::
    (1,Pos (Unmapped b)) ::
    MAP (λv. (1,Pos (Mapped b v))) (not_neighbours (vt,et) u),
    1):enc pbc]
End

Definition all_full_edge_map_def:
  all_full_edge_map (vp,ep) (vt,et) =
  FLAT (GENLIST (λu.
    FLAT (GENLIST (λa.
      (* Check that a,u have same self-loop *)
      if is_edge ep a a ⇎ is_edge et u u
      then [(GreaterEqual, [(1,Neg (Mapped a u))], 1):enc pbc]
      else
        FLAT (MAP (λb. edge_map (a,b) u et) (neighbours ep a)) ++
        FLAT (MAP (λb. not_edge_map (a,b) u vt et) (not_neighbours (vp,ep) a) )) vp)) vt)
End

Definition k_size_def:
  k_size vp k =
  (GreaterEqual,GENLIST (λb. (1, Neg (Unmapped b))) vp,&k):enc pbc
End

Definition encode_base_def:
  encode_base (vp,ep) (vt,et) k =
  k_size vp k ::
  all_has_mapping vp vt ++
  all_one_one vp vt ++
  all_full_edge_map (vp,ep) (vt,et)
End

Theorem b2i_geq_1[simp]:
  b2i b ≥ 1 ⇔ b
Proof
  Cases_on`b`>>fs[]
QED

Theorem b2i_eq_1[simp]:
  b2i b = 1 ⇔ b
Proof
  Cases_on`b`>>fs[]
QED

Theorem b2i_eq_0[simp]:
  b2i b = 0 ⇔ ¬b
Proof
  Cases_on`b`>>fs[]
QED

Theorem neg_b2i_eq_1[simp]:
  1 - b2i b = 1 ⇔ ¬b
Proof
  Cases_on`b`>>fs[]
QED

Theorem b2i_geq_zero[simp]:
  b2i b ≥ 0
Proof
  Cases_on`b`>>
  simp[]
QED

Theorem b2i_add_one_geq_one[simp]:
  1+ b2i b ≥ 1
Proof
  Cases_on`b`>>
  simp[]
QED

Theorem iSUM_zero:
  (∀x. MEM x ls ⇒ x ≥ 0) ⇒
  iSUM ls ≥ 0
Proof
  Induct_on`ls`>> rw[iSUM_def]>>
  fs[]>>
  first_x_assum(qspec_then`h` assume_tac)>>
  fs[]>>
  intLib.ARITH_TAC
QED

Theorem iSUM_geq:
  ∀ls.
  (∀x. MEM x ls ⇒ x ≥ 0) ∧
  (∃x. MEM x ls ∧ x ≥ n)
  ⇒
  iSUM ls ≥ n
Proof
  Induct>>rw[iSUM_def]
  >- (
    `iSUM ls ≥ 0` by
      (irule iSUM_zero>>
      metis_tac[])>>
    intLib.ARITH_TAC)>>
  gs[]>>
  last_x_assum mp_tac>>
  impl_tac >- metis_tac[]>>
  first_x_assum(qspec_then`h` assume_tac)>>
  fs[]>>
  intLib.ARITH_TAC
QED

Theorem b2i_iSUM_eq_0:
  (∀x. MEM x ls ⇒ ∃y. x = b2i y) ⇒
  (iSUM ls = 0 ⇔
  ∀j. j < LENGTH ls ⇒ EL j ls = 0)
Proof
  Induct_on`ls`>>rw[iSUM_def]>>fs[]>>
  first_assum(qspec_then`h` assume_tac)>>fs[]>>
  Cases_on`y`>>fs[]
  >- (
    `iSUM ls ≥ 0` by (
      match_mp_tac iSUM_zero>>
      rw[]>>res_tac>>
      rw[])>>
    rw[EQ_IMP_THM]
    >- (
      last_x_assum kall_tac>>
      intLib.COOPER_TAC)>>
    pop_assum(qspec_then`0` mp_tac)>>simp[])
  >>
  rw[EQ_IMP_THM]
  >-
    (Cases_on`j`>>fs[])>>
  first_x_assum (qspec_then`SUC j` mp_tac)>>fs[]
QED

Theorem iSUM_geq_1:
  iSUM ls ≥ 1 /\
  (∀x. MEM x ls ⇒ ∃y. x = b2i y) ⇒
    ∃i. i < LENGTH ls ∧ EL i ls  = 1
Proof
  Induct_on`ls`>>rw[iSUM_def]>>fs[]>>
  first_assum(qspec_then`h` assume_tac)>>fs[]>>
  Cases_on`y`>>fs[]>>
  simp[]
  >- (qexists_tac`0`>>rw[])>>
  qexists_tac`SUC i`>>rw[]
QED

Theorem iSUM_eq_1:
  (∀x. MEM x ls ⇒ ∃y. x = b2i y) ⇒
  (iSUM ls = 1 ⇔
  ∃i. i < LENGTH ls ∧ EL i ls  = 1 ∧
  ∀j. i ≠ j ∧ j < LENGTH ls ⇒ EL j ls = 0)
Proof
  Induct_on`ls`>>rw[iSUM_def]>>fs[]>>
  first_assum(qspec_then`h` assume_tac)>>fs[]>>
  Cases_on`y`>>fs[]>>
  simp[]
  >-(
    DEP_REWRITE_TAC[b2i_iSUM_eq_0]>>
    CONJ_TAC >- metis_tac[]>>
    rw[EQ_IMP_THM]
    >- (
      qexists_tac`0`>>rw[]>>
      Cases_on`j`>>fs[])>>
    `i = 0` by
      (CCONTR_TAC>>
      first_x_assum drule>>fs[])>>
    first_x_assum(qspec_then`SUC j` assume_tac)>>rfs[]>>
    Cases_on`i`>>fs[])
  >>
  rw[EQ_IMP_THM]
  >- (
    qexists_tac`SUC i`>>rw[]>>
    Cases_on`j`>>fs[])>>
  Cases_on`i`>>fs[]>>
  qexists_tac`n`>>rw[]>>
  first_x_assum(qspec_then`SUC j` assume_tac)>>fs[]
QED

Theorem iSUM_sub_b2i_geq_0:
  (∀x. MEM x ls ⇒ ∃y. x = 1 - b2i y) ⇒
  iSUM ls ≤ &(LENGTH ls)
Proof
  Induct_on`ls`>>fs[iSUM_def]>>rw[]>>
  first_assum(qspec_then`h` assume_tac)>>fs[]>>
  Cases_on`y`>>fs[ADD1]>>
  intLib.ARITH_TAC
QED

Theorem iSUM_sub_b2i_geq_0:
  (∀x. MEM x ls ⇒ ∃y. x = 1 - b2i y) ⇒
  (iSUM ls ≥ &(LENGTH ls) ⇔
   ∀i. i < LENGTH ls ⇒ EL i ls = 1)
Proof
  Induct_on`ls`>>
  fs[iSUM_def]>>rw[]>>
  first_assum(qspec_then`h` assume_tac)>>fs[]>>
  Cases_on`y`>>fs[]
  >- (
    `iSUM ls ≤ &(LENGTH ls)` by
      metis_tac[iSUM_sub_b2i_geq_0]>>
    rw[EQ_IMP_THM]
    >-
      (last_x_assum kall_tac>>intLib.ARITH_TAC)>>
    first_x_assum(qspec_then`0` assume_tac)>>fs[])>>
  simp[ADD1,GSYM integerTheory.INT_ADD,intLib.COOPER_PROVE``!n:int. 1 + n ≥ m + 1 ⇔ n ≥ m``]>>
  rw[EQ_IMP_THM]
  >-
    (Cases_on`i`>>fs[])>>
  first_x_assum(qspec_then`SUC i` assume_tac)>>fs[]
QED

Theorem iSUM_sub_b2i_geq:
  (∀x. MEM x ls ⇒ ∃y. x = 1 - b2i y) ⇒
  (iSUM ls ≥ &(LENGTH ls) − 1 ⇔
   ∀i. i < LENGTH ls ∧ EL i ls = 0 ⇒
   ∀j. i ≠ j ∧ j < LENGTH ls ⇒ EL j ls = 1)
Proof
  Induct_on`ls`>>fs[iSUM_def]>>rw[]>>
  simp[ADD1]>>
  first_assum(qspec_then`h` assume_tac)>>fs[]>>
  Cases_on`y`>>fs[]>>
  simp[GSYM integerTheory.INT_ADD,intLib.COOPER_PROVE``!n:int. n +1 -1 = n``]
  >- (
    DEP_REWRITE_TAC[iSUM_sub_b2i_geq_0] >>
    CONJ_TAC >- metis_tac[]>>
    rw[EQ_IMP_THM]
    >- (
      Cases_on`j`>>fs[]>>
      Cases_on`i`>>fs[ADD1]>>
      first_x_assum drule>>fs[])>>
    first_x_assum(qspec_then`0` assume_tac)>>gs[]>>
    first_x_assum(qspec_then`SUC i` assume_tac)>>gs[])>>
  simp[intLib.COOPER_PROVE``!n:int. 1 + n ≥ m ⇔ n ≥ m - 1``]>>
  rw[EQ_IMP_THM]
  >- (
    Cases_on`i`>>fs[ADD1]>>
    first_x_assum drule>>simp[]>>
    Cases_on`j`>>fs[])>>
  first_x_assum(qspec_then`SUC i` assume_tac)>>gs[]>>
  first_x_assum(qspec_then`SUC j` assume_tac)>>gs[]
QED

Theorem iSUM_GENLIST_const:
  ∀vt c.
  iSUM (GENLIST (λv. c) vt) = c * &vt
Proof
  Induct>>simp[iSUM_def,GENLIST_CONS,o_DEF]>>
  intLib.ARITH_TAC
QED

Theorem iSUM_MAP_const:
  ∀ls c. iSUM (MAP (λv. c) ls) = c * &(LENGTH ls)
Proof
  Induct>>simp[iSUM_def]>>
  intLib.ARITH_TAC
QED

Theorem iSUM_SNOC:
  ∀ls.
  iSUM (SNOC x ls) = x + iSUM ls
Proof
  Induct>>rw[iSUM_def]>>
  intLib.ARITH_TAC
QED

Theorem iSUM_GENLIST_geq_k:
  ∀vp vs k.
  vs ⊆ count vp ∧
  iSUM (GENLIST (λb. b2i (b ∈ vs)) vp) ≥ &k ⇒
  CARD vs ≥ k
Proof
  Induct>>rw[iSUM_def]
  >- intLib.ARITH_TAC>>
  fs[GENLIST,SUBSET_DEF]>>
  reverse (Cases_on`vp ∈ vs`>>fs[iSUM_SNOC])
  >- (
    first_x_assum match_mp_tac>>simp[]>>
    rw[]>>
    first_x_assum drule>>fs[prim_recTheory.LESS_THM]>>
    metis_tac[])>>
  first_x_assum(qspecl_then[`vs DIFF{vp}`,`k-1`] mp_tac)>>
  impl_tac>- (
    rw[]
    >- (
      first_x_assum drule>>fs[prim_recTheory.LESS_THM]>>
      metis_tac[]) >>
    Cases_on`k`>>fs[]
    >- (
      Cases_on`vp`>>simp[iSUM_def]>>
      match_mp_tac iSUM_geq>>simp[MEM_GENLIST]>>rw[]>>
      simp[PULL_EXISTS]>>
      qexists_tac`n`>>simp[])>>
    fs[ADD1,intLib.COOPER_PROVE``!n:int. 1 + n ≥ &(k+1) ⇔ n ≥ &k``]>>
    qmatch_asmsub_abbrev_tac`iSUM ls1`>>
    qmatch_goalsub_abbrev_tac`iSUM ls2`>>
    `ls1 = ls2` by
      (unabbrev_all_tac>>simp[LIST_EQ])>>
    fs[])>>
  DEP_REWRITE_TAC[CARD_DIFF]>>
  `vs ∩ {vp} = {vp}` by
    (simp[EXTENSION]>>metis_tac[])>>
  simp[]>>
  `FINITE vs` by (
    match_mp_tac SUBSET_FINITE_I>>
    qexists_tac`count (SUC vp)`>>
    fs[SUBSET_DEF])>>
  Cases_on`vs`>>fs[]
QED

Theorem iSUM_GENLIST_geq_k_rev:
  ∀vp vs k.
  vs ⊆ count vp ∧
  CARD vs ≥ k ⇒
  iSUM (GENLIST (λb. b2i (b ∈ vs)) vp) ≥ &k
Proof
  Induct>>rw[iSUM_def]>>fs[]
  >- intLib.ARITH_TAC>>
  fs[GENLIST,SUBSET_DEF]>>
  reverse (Cases_on`vp ∈ vs`>>fs[iSUM_SNOC])
  >- (
    first_x_assum match_mp_tac>>simp[]>>
    rw[]>>
    first_x_assum drule>>fs[prim_recTheory.LESS_THM]>>
    metis_tac[])>>
  first_x_assum(qspecl_then[`vs DIFF{vp}`,`k-1`] mp_tac)>>
  impl_tac>- (
    rw[]
    >- (
      first_x_assum drule>>fs[prim_recTheory.LESS_THM]>>
      metis_tac[]) >>
    Cases_on`k`>>fs[]>>
    DEP_REWRITE_TAC[CARD_DIFF]>>
    `vs ∩ {vp} = {vp}` by
      (simp[EXTENSION]>>metis_tac[])>>
    simp[]>>
    `FINITE vs` by (
      match_mp_tac SUBSET_FINITE_I>>
      qexists_tac`count (SUC vp)`>>
      fs[SUBSET_DEF])>>
    Cases_on`vs`>>fs[])>>
  Cases_on`k`
  >- (
    simp[]>>strip_tac>>
    match_mp_tac (intLib.COOPER_PROVE``!n:int. n ≥ 0 ⇒ 1 + n ≥ 0``)>>
    Cases_on`vp`>>simp[iSUM_def]>>
    match_mp_tac iSUM_geq>>simp[MEM_GENLIST]>>rw[]>>
    simp[PULL_EXISTS]>>
    qexists_tac`n`>>simp[])>>
  simp[ADD1]>>
  fs[ADD1,intLib.COOPER_PROVE``!n:int. 1 + n ≥ &(k+1) ⇔ n ≥ &k``]>>
  qmatch_goalsub_abbrev_tac`iSUM ls1 ≥ _`>>
  strip_tac>>
  qmatch_goalsub_abbrev_tac`iSUM ls2 ≥ _`>>
  `ls1 = ls2` by
    (unabbrev_all_tac>>simp[LIST_EQ])>>
  fs[]
QED

Theorem neg_b2i:
  1 - b2i p = b2i (~ p)
Proof
  Cases_on`p`>>simp[]
QED

Theorem MEM_if:
  MEM x (if P then A else B) ⇔
  if P then MEM x A else MEM x B
Proof
  rw[]
QED

Theorem encode_base_correct:
  good_graph (vp,ep) ∧
  good_graph (vt,et) ∧
  encode_base (vp,ep) (vt,et) k = constraints ⇒
  (
    (∃f vs.
      injective_partial_map f vs k (vp,ep) (vt,et)) ⇔
    satisfiable (set constraints)
  )
Proof
  rw[EQ_IMP_THM]
  >- (
    fs[injective_partial_map_def]>>
    simp[satisfiable_def]>>
    qexists_tac`λenc.
      case enc of
        Unmapped a => a ∉ vs
      | Mapped a u => a ∈ vs ∧ f a = u
      | _ => ARB` >>
    rw[encode_base_def]
    >- (
      rename1`k_size`>>
      simp[k_size_def,satisfies_pbc_def,MAP_GENLIST, o_DEF,eval_lin_term_def]>>
      simp[neg_b2i]>>
      metis_tac[iSUM_GENLIST_geq_k_rev])
    >- (
      rename1`all_has_mapping`>>
      simp[all_has_mapping_def,satisfies_def,MEM_GENLIST,has_mapping_def]>>
      rw[]>>
      simp[satisfies_pbc_def,MAP_GENLIST,o_DEF,eval_lin_term_def]>>
      simp[iSUM_def]>>
      Cases_on`a ∈ vs`>>simp[]
      >- ( (* a ∈ vs *)
        DEP_REWRITE_TAC[iSUM_eq_1]>>
        CONJ_TAC>-
          (simp[MEM_GENLIST]>>metis_tac[])>>
        qexists_tac`f a`>>
        CONJ_ASM1_TAC>>fs[EL_GENLIST,INJ_DEF]) >>
      simp[iSUM_GENLIST_const])
    >- (
      rename1`all_one_one`>>
      simp[all_one_one_def,satisfies_def,MEM_GENLIST,one_one_def]>>
      rw[]>>
      simp[satisfies_pbc_def,MAP_GENLIST,o_DEF,eval_lin_term_def]>>
      fs[INJ_DEF]>>
      qmatch_goalsub_abbrev_tac`iSUM ls`>>
      `vp = LENGTH ls` by
        simp[Abbr`ls`]>>
      simp[]>>
      DEP_REWRITE_TAC[iSUM_sub_b2i_geq]>>
      simp[Abbr`ls`]>>
      CONJ_TAC>- (
        simp[MEM_GENLIST]>>
        metis_tac[])>>
      rw[]>>
      gs[EL_GENLIST]>>
      metis_tac[])
    >- (
      rename1`all_full_edge_map`>>
      simp[all_full_edge_map_def,satisfies_def,MEM_GENLIST,MEM_FLAT]>>
      rw[]>>
      gvs[MEM_FLAT,MEM_GENLIST,MEM_MAP]>>
      pop_assum mp_tac>>
      qmatch_goalsub_abbrev_tac`if P then _ else _`>>
      IF_CASES_TAC
      >- (
        rw[Abbr`P`]>>
        simp[satisfies_pbc_def,iSUM_def,eval_lin_term_def]>>
        Cases_on`a ∈ vs`>>simp[iSUM_def]>>
        `f a ≠ u` by metis_tac[MEM_neighbours]>>
        simp[])>>
      simp[MEM_FLAT,MEM_MAP,PULL_EXISTS,MEM_if]>>
      rw[]
      >- (
        (* edge_map constraint *)
        gvs[edge_map_def,MEM_if,MEM_neighbours]>>
        simp[satisfies_pbc_def,MAP_MAP_o,o_DEF,eval_lin_term_def]>>
        `b < vp` by
          (fs[good_graph_def,is_edge_thm]>>
          metis_tac[])>>
        simp[]>>
        reverse (Cases_on`b ∈ vs`)>>fs[]
        >- (
          simp[iSUM_def,iSUM_MAP_const]>>
          Cases_on`a ∈ vs ∧ f a = u`>>simp[])>>
        reverse (Cases_on`f a = u`>>rw[]>>simp[iSUM_def])
        >- (
          simp[intLib.COOPER_PROVE``!n:int. 1 + n ≥ 1 ⇔ n ≥ 0``]>>
          match_mp_tac iSUM_zero>>
          simp[MEM_MAP,MEM_neighbours]>>
          rw[]>>
          simp[])>>
        Cases_on`a ∈ vs`>>fs[]
        >- (
          match_mp_tac iSUM_geq>>
          rw[]
          >-
            (fs[MEM_MAP]>>pairarg_tac>>simp[])>>
          simp[MEM_MAP,MEM_FILTER,LAMBDA_PROD,PULL_EXISTS,EXISTS_PROD,MEM_neighbours]>>
          qexists_tac`f b`>>simp[]>>
          fs[INJ_DEF])>>
        simp[intLib.COOPER_PROVE``!n:int. 1 + n ≥ 1 ⇔ n ≥ 0``]>>
        match_mp_tac iSUM_zero>>
        simp[MEM_MAP,MEM_neighbours]>>
        rw[]>>
        simp[])
      >- (
        (* not_edge_map constraint *)
        gvs[not_edge_map_def,MEM_if,MEM_not_neighbours]>>
        simp[satisfies_pbc_def,MAP_MAP_o,o_DEF,eval_lin_term_def]>>
        reverse (Cases_on`b ∈ vs`)>>fs[]
        >- (
          simp[iSUM_def,iSUM_MAP_const]>>
          Cases_on`a ∈ vs ∧ f a = u`>>simp[])>>
        reverse (Cases_on`f a = u`>>rw[]>>simp[iSUM_def])
        >- (
          simp[intLib.COOPER_PROVE``!n:int. 1 + n ≥ 1 ⇔ n ≥ 0``]>>
          match_mp_tac iSUM_zero>>
          simp[MEM_MAP,MEM_not_neighbours]>>
          rw[]>>
          simp[])>>
        Cases_on`a ∈ vs`>>fs[]
        >- (
          match_mp_tac iSUM_geq>>
          rw[]
          >-
            (fs[MEM_MAP]>>pairarg_tac>>simp[])>>
          simp[MEM_MAP,MEM_FILTER,LAMBDA_PROD,PULL_EXISTS,EXISTS_PROD,MEM_not_neighbours]>>
          fs[INJ_DEF])>>
        simp[intLib.COOPER_PROVE``!n:int. 1 + n ≥ 1 ⇔ n ≥ 0``]>>
        match_mp_tac iSUM_zero>>
        simp[MEM_MAP,MEM_not_neighbours]>>
        rw[]>>
        simp[])))>>
  fs[satisfiable_def,injective_partial_map_def]>>
  qexists_tac`λn. @m. m < vt ∧ w (Mapped n m)`>>
  qabbrev_tac`dom = {n | n < vp ∧ ¬ w (Unmapped n)}`>>
  qexists_tac `dom`>>
  simp[]>>
  CONJ_TAC>-
    simp[Abbr`dom`,SUBSET_DEF]>>
  fs[satisfies_def,encode_base_def,SF DNF_ss]>>
  CONJ_TAC>- (
    fs[k_size_def,satisfies_pbc_def,MAP_GENLIST,o_DEF,neg_b2i,eval_lin_term_def]>>
    match_mp_tac iSUM_GENLIST_geq_k>>
    qexists_tac`vp`>>fs[Abbr`dom`,SUBSET_DEF]>>
    qmatch_asmsub_abbrev_tac`iSUM ls1`>>
    qmatch_goalsub_abbrev_tac`iSUM ls2`>>
    `ls1 = ls2` by
      (unabbrev_all_tac>>simp[LIST_EQ])>>
    fs[])>>
  `∀n. n < vp ∧ ¬w (Unmapped n) ⇒
   ∃m. m < vt ∧ w (Mapped n m) ∧
   ∀m'. m' < vt ∧ w (Mapped n m') ⇔ m = m'` by (
     fs[all_has_mapping_def,MEM_GENLIST,has_mapping_def,PULL_EXISTS]>>
     rw[]>>
     first_x_assum drule>>
     simp[satisfies_pbc_def,MAP_GENLIST,o_DEF,eval_lin_term_def]>>
     simp[iSUM_def]>>
     DEP_REWRITE_TAC[iSUM_eq_1]>>
     CONJ_TAC>-
       (simp[MEM_GENLIST]>>metis_tac[])>>
     rw[]>>gs[EL_GENLIST]>>
     asm_exists_tac>>fs[]>>
     CCONTR_TAC>>gs[]>>
     Cases_on`i=m'`>>gs[]>>
     first_x_assum drule>>
     fs[])>>
  rw[]
  >- (
    fs[Abbr`dom`]>>
    rw[INJ_DEF]
    >- (
      first_x_assum drule>>strip_tac>>
      rfs[])>>
    fs[all_one_one_def,MEM_GENLIST,PULL_EXISTS,one_one_def]>>
    res_tac>>
    gvs[]>>
    last_x_assum drule>>
    simp[satisfies_pbc_def,MAP_GENLIST,o_DEF,eval_lin_term_def]>>
    qmatch_goalsub_abbrev_tac`iSUM ls`>>
    `vp = LENGTH ls` by
      simp[Abbr`ls`]>>
    simp[]>>
    DEP_REWRITE_TAC[iSUM_sub_b2i_geq]>>
    simp[Abbr`ls`]>>
    CONJ_TAC>- (
      simp[MEM_GENLIST]>>
      metis_tac[])>>
    rw[]>>
    first_x_assum drule>>
    simp[EL_GENLIST]>>
    disch_then(qspec_then`n` mp_tac)>>
    simp[])
  >- (
    fs[Abbr`dom`,good_graph_def]>>
    first_assum(qspec_then`a` mp_tac)>>
    first_x_assum(qspec_then`b` drule)>>
    simp[]>> rw[]>>
    gvs[]>>
    fs[all_full_edge_map_def,satisfies_def,MEM_GENLIST,MEM_FLAT,edge_map_def,PULL_EXISTS,MEM_MAP,FORALL_PROD]>>
    `is_edge ep b a` by
      fs[is_edge_thm]>>
    first_x_assum (drule_at (Pos (el 2)))>>
    qpat_x_assum`m < _` assume_tac>>
    disch_then drule>>
    qmatch_goalsub_abbrev_tac`if P then _ else _`>>
    IF_CASES_TAC
    >- (
      fs[Abbr`P`]>>
      simp[satisfies_pbc_def,iSUM_def,eval_lin_term_def])>>
    simp[MEM_FLAT,MEM_MAP,MEM_neighbours,SF DNF_ss,MEM_if]>>
    Cases_on` b = a` >-
      metis_tac[]>>
    strip_tac>> pop_assum kall_tac>>
    pop_assum drule>>
    simp[satisfies_pbc_def,iSUM_def,MAP_MAP_o,o_DEF,LAMBDA_PROD,MEM_neighbours,eval_lin_term_def]>>
    strip_tac>>
    gs[]>>
    drule iSUM_geq_1>>
    simp[MEM_MAP,PULL_EXISTS,MEM_FILTER,FORALL_PROD]>>
    impl_tac >- metis_tac[]>>
    strip_tac>>
    gs[EL_MAP]>>
    qmatch_asmsub_abbrev_tac`Mapped _ ee`>>
    `m' = ee` by (
      unabbrev_all_tac>>
      metis_tac[MEM_EL,MEM_neighbours,is_edge_thm])>>
    rw[]>>
    `MEM ee (neighbours et m)` by
      metis_tac[EL_MEM,Abbr`ee`]>>
    fs[MEM_neighbours]>>
    metis_tac[is_edge_thm])
  >- (
    fs[Abbr`dom`,good_graph_def]>>
    first_assum(qspec_then`a` mp_tac)>>
    first_x_assum(qspec_then`b` drule)>>
    simp[]>> rw[]>>
    gvs[]>>
    fs[all_full_edge_map_def,satisfies_def,MEM_FLAT,MEM_GENLIST,PULL_EXISTS,MEM_MAP,MEM_not_neighbours,not_edge_map_def]>>
    first_x_assum (drule_at (Pos (el 1)))>>
    qpat_x_assum`a < vp` assume_tac>>
    disch_then drule>>simp[]>>
    qmatch_goalsub_abbrev_tac`if P then _ else _`>>
    IF_CASES_TAC
    >- (
      fs[Abbr`P`]>>
      simp[satisfies_pbc_def,iSUM_def,eval_lin_term_def])>>
    simp[MEM_FLAT,MEM_MAP,MEM_not_neighbours,SF DNF_ss,MEM_if]>>
    Cases_on` b = a` >-
      metis_tac[]>>
    strip_tac>>
    pop_assum (drule_at (Pos (el 2)))>>
    simp[satisfies_pbc_def,iSUM_def,MAP_MAP_o,o_DEF,LAMBDA_PROD,eval_lin_term_def]>>
    strip_tac>>
    drule iSUM_geq_1>>
    simp[MEM_MAP,PULL_EXISTS,MEM_FILTER,FORALL_PROD]>>
    impl_tac >- metis_tac[]>>
    strip_tac>>
    gs[EL_MAP]>>
    qmatch_asmsub_abbrev_tac`Mapped b ee`>>
    `m = ee` by (
      unabbrev_all_tac>>
      metis_tac[MEM_EL,MEM_not_neighbours])>>
    rw[]>>
    `MEM ee (not_neighbours (vt,et) m')` by
      metis_tac[EL_MEM,Abbr`ee`]>>
    fs[MEM_not_neighbours])
QED

Theorem satisfies_pbc_geq_1:
  satisfies_pbc w (GreaterEqual,xs, 1) ∧
  EVERY ($= 1) (MAP FST xs) ⇒
  ∃x. MEM x (MAP SND xs)  ∧ eval_lit w x = 1
Proof
  rw[satisfies_pbc_def,eval_lin_term_def]>>
  drule iSUM_geq_1>>
  impl_tac>- (
    fs[EVERY_MEM,MEM_MAP,PULL_EXISTS,EXISTS_PROD]>>
    strip_tac>>Cases>>simp[]>>
    strip_tac>>first_x_assum drule>>simp[]
    >- metis_tac[]>>
    rw[]>>
    qexists_tac`(¬ (w a))`>>
    Cases_on`w a`>>simp[])>>
  rw[]>>
  rfs[EL_MAP]>>
  qexists_tac `SND (EL i xs)`>>fs[MEM_MAP]>>
  Cases_on`EL i xs`>>rfs[EVERY_MEM,MEM_MAP]
  >- metis_tac[EL_MEM,SND]>>
  fs[PULL_EXISTS]>>
  first_x_assum(qspec_then`EL i xs` mp_tac)>>fs[]>>
  metis_tac[MEM_EL]
QED

(* Encode variable x <-> y_1 ∧ y_2 ...., where y_i are literals *)
Definition iff_and_def:
  iff_and x ys =
    (GreaterEqual,(1, Pos x)::MAP (λy.(1, negate y)) ys,1):'a pbc ::
    MAP (λy.
      (GreaterEqual, [(1, Neg x); (1,y)], 1)) ys
End

Theorem eval_lit_negate:
  eval_lit w (negate x) = 1 - eval_lit w x
Proof
  Cases_on`x`>>simp[]
QED

Theorem iff_and:
  satisfies w (set (iff_and x ys)) ⇒
  (w x ⇔ EVERY (λy. eval_lit w y = 1) ys)
Proof
  rw[iff_and_def]>>
  fs[satisfies_pbc_def,satisfies_def,MEM_MAP,PULL_EXISTS,eval_lin_term_def]>>
  rw[EQ_IMP_THM]
  >- (
    rw[EVERY_MEM]>>first_x_assum drule>>
    Cases_on`y`>>Cases_on`w a`>>simp[iSUM_def])>>
  drule iSUM_geq_1>>
  impl_tac>- (
    rw[MEM_MAP]>- metis_tac[]>>
    Cases_on`y'`>>simp[]
    >- (
      qexists_tac`(¬ (w a))`>>
      Cases_on`w a`>>simp[])>>
    metis_tac[])>>
  rw[]>>Cases_on`i`>>
  gs[MAP_MAP_o,EL_MAP]>>
  fs[EVERY_EL,eval_lit_negate]>>
  first_x_assum drule>>
  rw[]>>gvs[]
QED

(* Encode variable x <-> y_1 ∨ y_2 ...., where y_i are literals *)
Definition iff_or_def:
  iff_or x ys =
    (GreaterEqual, (1, Neg x)::MAP (λy.(1, y)) ys, 1):'a pbc ::
    MAP (λy.
      (GreaterEqual, [(1, Pos x); (1, negate y)], 1)) ys
End

Theorem iff_or:
  satisfies w (set (iff_or x ys)) ⇒
  (w x ⇔ EXISTS (λy. eval_lit w y = 1) ys)
Proof
  rw[iff_or_def]>>
  fs[satisfies_pbc_def,satisfies_def,MEM_MAP,PULL_EXISTS,eval_lin_term_def]>>
  rw[EQ_IMP_THM]
  >- (
    drule iSUM_geq_1>>
    impl_tac>- (
      rw[] >- (qexists_tac`F`>>simp[])>>
      gvs[MEM_MAP]>>
      Cases_on`y'`>>simp[]
      >- metis_tac[]>>
      qexists_tac`¬ (w a)`>>
      Cases_on`w a`>>simp[])>>
    rw[]>>Cases_on`i`>>gs[]>>
    gs[MAP_MAP_o,EL_MAP]>>
    simp[EXISTS_MEM,MEM_EL]>>
    metis_tac[EL_MEM])>>
  fs[EXISTS_MEM]>>
  first_x_assum drule>>simp[iSUM_def,eval_lit_negate]>>
  Cases_on`w x`>>simp[]
QED

Theorem iff_or_satisfies:
  (w x ⇔ EXISTS (λy. eval_lit w y = 1) ys) ⇒
  satisfies w (set (iff_or x ys))
Proof
  rw[iff_or_def]>>
  fs[satisfies_pbc_def,satisfies_def,MEM_MAP,PULL_EXISTS,eval_lin_term_def]>>
  rw[]
  >- (
    Cases_on`w x`>>gs[iSUM_def]
    >- (
      fs[EXISTS_MEM]>>
      match_mp_tac iSUM_geq>>simp[MEM_MAP,PULL_EXISTS]>>
      first_x_assum (irule_at Any)>>rw[]>>
      Cases_on`y'`>>Cases_on`w a`>>simp[])>>
    qmatch_goalsub_abbrev_tac`b2i A`>>
    `~A` by simp[Abbr`A`,NOT_EXISTS]>>
    simp[intLib.COOPER_PROVE``!n:int. 1 + n ≥ 1 ⇔ n ≥ 0``]>>
    match_mp_tac iSUM_zero>>
    simp[MEM_MAP]>>
    rw[]>>
    simp[]>>
    Cases_on`y'`>>Cases_on`w a`>>simp[])>>
  Cases_on`w x`>>gs[iSUM_def]
  >-
    (Cases_on`y`>>Cases_on`w a`>>simp[])>>
  fs[EVERY_MEM]>>
  first_x_assum drule>>
  Cases_on`y`>>Cases_on`w a`>>simp[]>>
  qmatch_goalsub_abbrev_tac`b2i A`>>Cases_on`A`>>simp[]
QED

(* encoding for the base case f-g *)
Definition walk_base_def:
  walk_base ep f g =
  if is_edge ep f g then
    (* x_{f,g}^1 <-> !x_f,bot ∧ !x_g,bot *)
    iff_and (Walk f g 0) [Neg (Unmapped f); Neg (Unmapped g)]
  else
    [(GreaterEqual, [(1,Neg (Walk f g 0))], 1): enc pbc]
End

Definition walk_aux_def:
  walk_aux f g h k =
    if f = h ∨ g = h then [] (* Ignore trivial cases *)
    else
    (* x_{f,h,g}^k <-> x_{h,g}^{k-1} *)
    if g < h then
      (* f < g < h *)
      iff_and (Aux f h g k) [Pos (Walk f h (k-1)) ; Pos (Walk g h (k-1))]
    else if h < f then
      (* h < f < g *)
      iff_and (Aux f h g k) [Pos (Walk h f (k-1)) ; Pos (Walk h g (k-1))]
    else
      (* f < h < g *)
      iff_and (Aux f h g k) [Pos (Walk f h (k-1)) ; Pos (Walk h g (k-1))]
End

Definition walk_ind_def:
  walk_ind f g k vp =
  iff_or (Walk f g k)
    (Pos (Walk f g (k-1)) ::
    FLAT (GENLIST (λh.
      if f = h ∨ g = h then [] else [Pos (Aux f h g k)]) vp))
End

(* x_{f,g}^k <-> x_{f,g}^{k-1} ∨ x_{f,h,g}^k  *)
Definition walk_k_def:
  (walk_k (vp,ep) 0 =
    FLAT (GENLIST (λf.
      FLAT (GENLIST (λg.
        if f < g then
          walk_base ep f g
        else []) vp)) vp)) ∧
  (walk_k (vp,ep) k =
    FLAT (GENLIST (λf.
      FLAT (GENLIST (λg.
        if f < g then
          FLAT (GENLIST (λh.
            walk_aux f g h k) vp) ++
          walk_ind f g k vp
        else [])
      vp)) vp)  ++
    walk_k (vp,ep) (k-1)
  )
End

Theorem is_walk_append:
  ∀walk a b c.
  is_walk ep a b walk ∧
  is_walk ep b c walk' ⇒
  is_walk ep a c (walk++walk')
Proof
  Induct>>
  rw[is_walk_def]>>
  metis_tac[]
QED

Theorem is_walk_SNOC:
  ∀walk a b c.
  is_walk e a b walk ∧
  is_edge e b c ⇒
  is_walk e a c (SNOC c walk)
Proof
  Induct>>rw[is_walk_def]>>
  first_x_assum match_mp_tac>>
  metis_tac[]
QED

Theorem good_graph_is_walk_REVERSE:
  ∀walk a b.
  good_graph (v,e) ∧
  is_walk e a b walk ⇒
  is_walk e b a (TL (REVERSE (a::walk)))
Proof
  Induct>>rw[is_walk_def]>>
  fs[]>>
  first_x_assum drule>>
  strip_tac>>
  drule is_walk_SNOC>>
  `is_edge e h a` by
    (fs[good_graph_def,is_edge_def]>>
    Cases_on`lookup a e`>>fs[])>>
  disch_then drule>>
  simp[SNOC_APPEND]>>
  Cases_on`REVERSE walk`>>simp[]
QED

Theorem is_walk_TAKE:
  ∀walk i a b.
  i < LENGTH walk ∧
  is_walk ep a b walk ⇒
  is_walk ep a (EL i walk) (TAKE (i+1) walk)
Proof
  Induct>>rw[] >>
  Cases_on`i`>>
  fs[is_walk_def,ADD1]>>
  first_x_assum match_mp_tac>>
  metis_tac[]
QED

Theorem is_walk_DROP:
  ∀walk i a b.
  i < LENGTH walk ∧
  is_walk ep a b walk ⇒
  is_walk ep (EL i walk) b (DROP (i+1) walk)
Proof
  Induct>>rw[] >>
  Cases_on`i`>>fs[is_walk_def]>>
  simp[ADD1]>>first_x_assum match_mp_tac>>
  metis_tac[]
QED

Theorem LENGTH_TL_SNOC[simp]:
  LENGTH (TL (REVERSE (h::walk))) = LENGTH walk
Proof
  DEP_REWRITE_TAC [LENGTH_TL]>>fs[]
QED

Definition is_path_def:
  is_path ep a b path ⇔
  is_walk ep a b path ∧
  ¬MEM a path ∧ ALL_DISTINCT path
End

Theorem is_walk_is_path:
  ∀a b ep.
  is_walk ep a b walk ⇒
  ∃path.
    set path ⊆ set walk ∧
    LENGTH path <= LENGTH walk ∧
    is_path ep a b path
Proof
  completeInduct_on`LENGTH walk`>>fs[PULL_FORALL,AND_IMP_INTRO]>>
  rw[]>>
  Cases_on`MEM a walk`
  >- (
    fs[MEM_EL]>>
    drule is_walk_DROP>>
    disch_then drule>>
    strip_tac>>
    first_x_assum (drule_at Any)>>
    simp[]>> strip_tac>>
    gs[SUBSET_DEF,MEM_DROP,PULL_EXISTS]>>
    `LENGTH path ≤ LENGTH walk` by fs[]>>
    metis_tac[MEM_EL])>>
  Cases_on`ALL_DISTINCT walk`
  >- (
    qexists_tac`walk`>>simp[]>>
    metis_tac[is_path_def,SUBSET_DEF])>>
  fs[EL_ALL_DISTINCT_EL_EQ,EQ_IMP_THM]>>
  wlog_tac`n1 < n2`[`n1`,`n2`]
  >- (
    first_x_assum match_mp_tac>>
    `n2 < n1` by fs[]>>
    metis_tac[])>>
  qpat_x_assum`n1 < LENGTH _` assume_tac>>
  drule is_walk_TAKE>>
  disch_then drule>>
  qpat_x_assum`n2 < _` assume_tac>>
  drule is_walk_DROP>>
  disch_then drule>>
  rw[]>>
  imp_res_tac is_walk_append >>
  ntac 4 (pop_assum kall_tac)>>
  first_x_assum (drule_at Any)>>
  simp[]>>
  strip_tac>>
  gs[SUBSET_DEF,PULL_EXISTS,MEM_DROP]>>
  `LENGTH path ≤ LENGTH walk` by fs[]>>
  metis_tac[MEM_TAKE,MEM_EL]
QED

Theorem is_walk_LAST:
  ∀walk f g.
  is_walk e f g walk ∧
  LENGTH walk > 0 ⇒ LAST walk = g
Proof
 Induct>>rw[is_walk_def]>>
 Cases_on`walk`>>fs[is_walk_def]>>
 first_x_assum drule>>
 simp[]
QED

Theorem satisfies_walk_k:
  ∀k f g.
  good_graph (vp,ep) ∧
  satisfies w (set (walk_k (vp,ep) k)) ∧
  f < g ∧ f < vp ∧ g < vp ⇒
  (w (Walk f g k) ⇔
    ¬ (w (Unmapped f)) ∧ ¬ (w (Unmapped g)) ∧
    ∃walk.
      EVERY (λp. p < vp ∧ ¬ (w (Unmapped p))) walk ∧
      is_walk ep f g walk ∧ LENGTH walk ≤ 2**k)
Proof
  Induct>>rw[]>>fs[walk_k_def,satisfies_def]
  >- (
    (* walk_base *)
    fs[MEM_FLAT,MEM_GENLIST,PULL_EXISTS,is_walk_def]>>
    pop_assum mp_tac>>
    first_x_assum drule>>
    rw[]>>
    first_x_assum drule>>
    simp[walk_base_def]>>rw[]
    >- (
      drule (SIMP_RULE std_ss [satisfies_def] iff_and)>>
      simp[]>>
      rw[]>>
      rw[EQ_IMP_THM]>>fs[]>>
      qexists_tac`[g]`>>simp[is_walk_def])
    >- (
      fs[satisfies_pbc_def,eval_lin_term_def]>>
      Cases_on`w (Walk f g 0)` >> fs[iSUM_def]>>
      CCONTR_TAC>>fs[]>>
      Cases_on`walk`>>fs[is_walk_def]>>Cases_on`t`>>fs[is_walk_def]) )>>
  fs[SF DNF_ss]>>
  fs[MEM_FLAT,MEM_GENLIST,PULL_EXISTS]>>
  pop_assum mp_tac>>
  first_x_assum drule>>
  rw[]>>
  first_x_assum drule>>
  simp[SF DNF_ss,MEM_FLAT,MEM_GENLIST,PULL_EXISTS]>>
  rw[]>>
  fs[walk_ind_def]>>
  drule (SIMP_RULE std_ss [satisfies_def] iff_or)>>
  pop_assum kall_tac>>
  rw[]>>
  pop_assum kall_tac>>
  simp[EXISTS_GENLIST]>>
  rw[EQ_IMP_THM]
  >- (
    (* there is already a walk of length 2**k *)
    simp[]>>
    asm_exists_tac>>simp[]>>
    fs[ADD1]>>
    `2 ** k ≤ 2 ** (k+1)` by fs[]>>
    simp[])
  >- (
    (* there is a walk via some h *)
    gvs[EXISTS_MEM,MEM_FLAT,MEM_GENLIST]>>
    Cases_on` f=h ∨ g=h` >>gvs[]>>
    first_x_assum drule>>
    strip_tac>>fs[walk_aux_def]>>
    rfs[]>>
    every_case_tac>>fs[]
    >- (
      (* h < f < g *)
      drule (SIMP_RULE std_ss [satisfies_def] iff_and)>>
      pop_assum kall_tac>>
      rw[]>>simp[]>>
      qpat_x_assum`is_walk ep h f walk` assume_tac>>
      drule good_graph_is_walk_REVERSE>>
      disch_then drule>> strip_tac>>
      drule is_walk_append>>
      qpat_x_assum`is_walk ep h g _` assume_tac>>
      disch_then drule>>
      strip_tac>>
      first_x_assum (irule_at Any)>>
      simp[EXP]>>
      fs[EVERY_MEM]>>
      rw[]>>drule MEM_TL>>fs[]>>
      metis_tac[MEM_TL,MEM_REVERSE])
    >- (
      (* f < g < h *)
      drule (SIMP_RULE std_ss [satisfies_def] iff_and)>>
      rw[]>>simp[]>>
      qpat_x_assum`is_walk ep g h _` assume_tac>>
      drule good_graph_is_walk_REVERSE>>
      disch_then drule>> strip_tac>>
      qpat_x_assum`is_walk ep f _ _` assume_tac>>
      drule is_walk_append>>
      disch_then drule>>
      strip_tac>>
      first_x_assum (irule_at Any)>>
      simp[EXP]>>
      fs[EVERY_MEM]>>
      `g < vp` by fs[]>>
      rw[]>>drule MEM_TL>>fs[]>>
      metis_tac[MEM_TL,MEM_REVERSE])
    >> (
      (* f < h < g *)
      `f < h ∧ h < g` by fs[]>>
      drule (SIMP_RULE std_ss [satisfies_def] iff_and)>>
      rw[]>>simp[]>>
      qpat_x_assum`is_walk ep f _ _` assume_tac>>
      drule is_walk_append>>
      disch_then drule>>
      disch_then (irule_at Any)>>
      simp[EXP]))>>
  (* converse *)
  drule is_walk_is_path>>
  strip_tac>>fs[is_path_def]>>
  `EVERY (λp. p < vp ∧ ¬w (Unmapped p)) path` by
    fs[EVERY_MEM,SUBSET_DEF]>>
  Cases_on`LENGTH path <= 2 ** k`
  >-
    metis_tac[]>>
  DISJ2_TAC>>
  simp[EXISTS_MEM,MEM_FLAT,MEM_GENLIST,PULL_EXISTS,MEM_if]>>
  qabbrev_tac`h = EL (2**k-1) path`>>
  qexists_tac`h`>>
  `MEM h path` by
    (fs[Abbr`h`]>>
    match_mp_tac EL_MEM>>
    fs[])>>
  fs[EVERY_MEM]>>
  CONJ_ASM1_TAC >- metis_tac[]>>
  CONJ_ASM1_TAC >- (
    drule is_walk_LAST>>fs[]>>
    drule ALL_DISTINCT_EL_IMP>>
    disch_then(qspecl_then[`2**k-1`,`LENGTH path -1`] mp_tac)>>simp[]>>
    `2 ** k -1 ≠ LENGTH path -1` by
      (`0 < 2**k` by metis_tac[bitTheory.ZERO_LT_TWOEXP]>>
      simp[bitTheory.ZERO_LT_TWOEXP])>>
    simp[]>>
    `LENGTH path - 1 = PRE (LENGTH path)` by fs[]>>
    `path ≠ []` by (Cases_on`path`>>fs[])>>
    metis_tac[LAST_EL])>>
  `h < f ∧ f < g ∨
   f < h ∧ h < g ∨
   f < g ∧ g < h` by fs[]
  >- ( (* h < f ∧ f < g *)
    first_assum(qspecl_then[`h`,`f`] mp_tac)>>
    first_x_assum(qspecl_then[`h`,`g`] mp_tac)>>
    rw[]>>fs[walk_aux_def]>>
    `h < vp` by fs[]>>
    last_x_assum drule>>simp[]>>
    strip_tac>>
    drule (SIMP_RULE std_ss [satisfies_def] iff_and)>>
    pop_assum kall_tac>>
    rw[]>>simp[]
    >- (
      `is_walk ep f h (TAKE (2 ** k -1 + 1) path)` by
        (simp[Abbr`h`]>>match_mp_tac is_walk_TAKE>>
        fs[]>>metis_tac[])>>
      drule good_graph_is_walk_REVERSE>>
      disch_then drule>>
      disch_then (irule_at Any)>>fs[]>>
      `0 < 2**k` by metis_tac[bitTheory.ZERO_LT_TWOEXP]>>
      simp[]>>
      rw[]>>drule MEM_TL>>fs[]>>
      metis_tac[MEM_TL,MEM_REVERSE,MEM_TAKE])>>
    qexists_tac`DROP (2**k) path`>>
    CONJ_TAC>-
      metis_tac[MEM_DROP_IMP]>>
    fs[EXP]>>
    `2 ** k - 1 < LENGTH path` by fs[]>>
    drule is_walk_DROP>>
    simp[]>>
    metis_tac[])
  >- ( (* f < h ∧ h < g *)
    first_assum(qspecl_then[`f`,`h`] mp_tac)>>
    first_x_assum(qspecl_then[`h`,`g`] mp_tac)>>
    rw[]>>fs[walk_aux_def]>>
    `h < vp` by fs[]>>
    last_x_assum drule>>simp[]>>
    strip_tac>>
    drule (SIMP_RULE std_ss [satisfies_def] iff_and)>>
    pop_assum kall_tac>>
    rw[]>>simp[]
    >- (
      `is_walk ep f h (TAKE (2 ** k -1 + 1) path)` by
        (simp[Abbr`h`]>>match_mp_tac is_walk_TAKE>>
        fs[]>>metis_tac[])>>
      pop_assum (irule_at Any)>>fs[]>>
      `0 < 2**k` by metis_tac[bitTheory.ZERO_LT_TWOEXP]>>
      simp[]>>
      metis_tac[MEM_TAKE])>>
    qexists_tac`DROP (2**k) path`>>
    CONJ_TAC>-
      metis_tac[MEM_DROP_IMP]>>
    fs[EXP]>>
    `2 ** k - 1 < LENGTH path` by fs[]>>
    drule is_walk_DROP>>
    simp[]>>
    metis_tac[])
  >> (* f < g < h *)
    first_assum(qspecl_then[`f`,`h`] mp_tac)>>
    first_x_assum(qspecl_then[`g`,`h`] mp_tac)>>
    rw[]>>fs[walk_aux_def]>>
    `h < vp` by fs[]>>
    last_x_assum drule>>simp[]>>
    strip_tac>>
    drule (SIMP_RULE std_ss [satisfies_def] iff_and)>>
    pop_assum kall_tac>>
    rw[]>>simp[]
    >- (
      `is_walk ep f h (TAKE (2 ** k -1 + 1) path)` by
        (simp[Abbr`h`]>>match_mp_tac is_walk_TAKE>>
        fs[]>>metis_tac[])>>
      pop_assum (irule_at Any)>>fs[]>>
      `0 < 2**k` by metis_tac[bitTheory.ZERO_LT_TWOEXP]>>
      simp[]>>
      metis_tac[MEM_TAKE])>>
    `2 ** k - 1 < LENGTH path` by fs[]>>
    drule is_walk_DROP>>
    disch_then drule>>
    `0 < 2**k` by metis_tac[bitTheory.ZERO_LT_TWOEXP]>>
    simp[]>>strip_tac>>
    drule good_graph_is_walk_REVERSE>>
    disch_then drule>>
    disch_then (irule_at Any)>>fs[]>>
    fs[EXP]>>
    rw[]>>drule MEM_TL>>fs[]>>
    metis_tac[MEM_DROP_IMP]
QED

Definition encode_connected_def:
  encode_connected (vp,ep) =
  if vp = 0 then []
  else
  let k = LOG 2 (vp*2-1) in
  walk_k (vp,ep) k ++
  FLAT (GENLIST (λf.
    FLAT (GENLIST (λg.
      if f < g then
        [(GreaterEqual, [(1, Pos(Unmapped f));(1, Pos(Unmapped g));(1, Pos(Walk f g k))], 1)]
      else []) vp)) vp)
End

Definition encode_def:
  encode (vp,ep) (vt,et) k =
  encode_base (vp,ep) (vt,et) k ++
  encode_connected (vp,ep)
End

Theorem MAP_if:
  MAP f (if P then A else B) = if P then MAP f A else MAP f B
Proof
  rw[]
QED

Theorem walk_k_free:
  ∀k c.
  MEM c (walk_k (v,e) k) ∧
  (∀f. w' (Unmapped f) = w (Unmapped f)) ∧
  (∀l f g.
    w' (Walk f g l) = if l <= k then w (Walk f g l) else w' (Walk f g l)) ∧
  (∀l f g h.
    w' (Aux f h g l) = if l <= k then w (Aux f h g l) else w' (Aux f h g l)) ⇒
  satisfies_pbc w c ⇒ satisfies_pbc w' c
Proof
  Induct>>rw[walk_k_def]>>every_case_tac>>fs[]>>
  gvs[MEM_FLAT,MEM_GENLIST]
  >- (
    fs[walk_base_def]>>every_case_tac>>
    gvs[iff_and_def,satisfies_pbc_def,eval_lin_term_def]>>
    first_x_assum(qspec_then`0` kall_tac)>>
    first_x_assum(qspec_then`0` assume_tac)>>
    fs[])
  >- (
    every_case_tac>>gvs[MEM_FLAT,MEM_GENLIST]
    >- (
      gvs[walk_aux_def,iff_and_def,satisfies_pbc_def,eval_lin_term_def]>>
      first_x_assum(qspec_then`SUC k` mp_tac)>>
      first_x_assum(qspec_then`k` mp_tac)>>
      every_case_tac>>
      gvs[satisfies_pbc_def,eval_lin_term_def])>>
    first_x_assum(qspec_then`SUC k` mp_tac)>>
    first_assum(qspec_then`SUC k` mp_tac)>>
    first_x_assum(qspec_then`k` mp_tac)>>
    gvs[walk_ind_def,iff_or_def,satisfies_pbc_def,eval_lin_term_def]>>
    gvs[MEM_FLAT,MAP_MAP_o,o_DEF,MAP_GENLIST,MEM_GENLIST,satisfies_pbc_def,MAP_FLAT,MAP_if,eval_lin_term_def]>>
    every_case_tac>>gvs[satisfies_pbc_def,eval_lin_term_def])>>
  fs[AND_IMP_INTRO]>>
  first_x_assum match_mp_tac>>fs[]>>
  rw[]
  >-
    (last_x_assum(qspecl_then[`l`,`f`,`g`] assume_tac)>>rfs[])>>
  last_x_assum(qspecl_then[`l`,`f`,`g`,`h`] assume_tac)>>rfs[]
QED

Theorem mk_satisfies_walk_k:
  ∀k. ∃w'.
  satisfies w' (set (walk_k (v,e) k)) ∧
  ∀x. case x of
    Unmapped f => w x = w' x
  | Mapped f g => w x = w' x
  | Walk f g l => k < l ⇒ w x = w' x
  | Aux f h g l => k < l ⇒ w x = w' x
Proof
  Induct>>rw[walk_k_def,satisfies_def]
  >- (
    qexists_tac`λn.
        case n of
        Walk f g k =>
          if k = 0 then
            if is_edge e f g then ¬ (w (Unmapped f)) ∧ ¬ (w (Unmapped g))
            else F
          else w n
      | _ => w n`>>
    rw[]
    >- (
      gvs[MEM_FLAT,MEM_GENLIST,walk_base_def]>>
      every_case_tac>>fs[]>>rw[]
      >- (
        gvs[iff_and_def,satisfies_pbc_def,iSUM_def,eval_lin_term_def]>>
        Cases_on`w (Unmapped f)`>>
        Cases_on`w (Unmapped g)`>>simp[])
      >>
      simp[satisfies_pbc_def,iSUM_def,eval_lin_term_def])>>
    every_case_tac>>simp[])>>
  qexists_tac`λn.
        case n of
        Walk f g l =>
          if l = SUC k then
            w' (Walk f g k) ∨
            ∃h. f ≠ h ∧ g ≠ h ∧
              (h < v ∧ f < h ∧ h < g ∧ w' (Walk f h k) ∧ w' (Walk h g k) ∨
              h < v ∧ h < f ∧ h < g ∧ w' (Walk h f k) ∧ w' (Walk h g k) ∨
              h < v ∧ f < h ∧ g < h ∧ w' (Walk f h k) ∧ w' (Walk g h k))
          else w' n
      | Aux f h g l =>
          if l = SUC k then
            (f < h ∧ h < g ∧ w' (Walk f h k) ∧ w' (Walk h g k)) ∨
            (h < f ∧ h < g ∧ w' (Walk h f k) ∧ w' (Walk h g k)) ∨
            (f < h ∧ g < h ∧ w' (Walk f h k) ∧ w' (Walk g h k))
          else w' n
      | _ => w' n`>>
  rw[]
  >- (
    ntac 2 (last_x_assum kall_tac)>>
    gvs[MEM_FLAT,MEM_GENLIST]>>every_case_tac>>gvs[MEM_FLAT,MEM_GENLIST]
    >- (
      gvs[walk_aux_def]>>
      every_case_tac>>
      gvs[iff_and_def,satisfies_pbc_def,iSUM_def,eval_lin_term_def]>>
      rpt(qmatch_goalsub_abbrev_tac`b2i A`>>Cases_on`A`>>fs[]))>>
    gvs[walk_ind_def]>>
    qpat_x_assum `MEM _ _` mp_tac>>
    match_mp_tac (SIMP_RULE std_ss [satisfies_def] iff_or_satisfies)>>simp[]>>
    simp[EXISTS_MEM,MEM_GENLIST,PULL_EXISTS,MEM_FLAT,MEM_if]>>
    metis_tac[])
  >- (
    first_x_assum drule>>
    match_mp_tac walk_k_free>>simp[]>>
    asm_exists_tac>>rw[]>>fs[])
  >- (
    pop_assum(qspec_then`x` assume_tac)>>
    every_case_tac>>simp[])
QED

Theorem mk_satisfies_walk_k_alt:
  ∀k. ∃w'.
  satisfies w' (set (walk_k (v,e) k)) ∧
  (∀f. w' (Unmapped f) = w (Unmapped f)) ∧
  (∀f g. w' (Mapped f g) = w (Mapped f g))
Proof
  rw[]>>assume_tac (mk_satisfies_walk_k |> SPEC_ALL)>>fs[]>>
  asm_exists_tac>>
  rw[]
  >-
    (first_x_assum(qspec_then`Unmapped f` assume_tac)>>fs[])>>
  first_x_assum(qspec_then`Mapped f g` assume_tac)>>fs[]
QED

Theorem ALL_DISTINCT_LENGTH_bound:
  set ls ⊆ count n ∧
  ALL_DISTINCT ls ⇒
  LENGTH ls <= n
Proof
  rw[]>>drule ALL_DISTINCT_CARD_LIST_TO_SET>>
  strip_tac>>
  `FINITE (count n)` by fs[]>>
  drule CARD_SUBSET>>
  disch_then drule>>simp[]
QED

Theorem encode_correct:
  good_graph (vp,ep) ∧
  good_graph (vt,et) ∧
  encode (vp,ep) (vt,et) k = constraints ⇒
  (
    (∃f vs.
      injective_partial_map f vs k (vp,ep) (vt,et) ∧
      connected_subgraph vs ep) ⇔
    satisfiable (set constraints)
  )
Proof
  rw[EQ_IMP_THM]
  >- (
    fs[injective_partial_map_def]>>
    simp[satisfiable_def]>>
    rw[encode_def,encode_base_def]>>
    qabbrev_tac`w = λenc.
      case enc of
        Unmapped a => a ∉ vs
      | Mapped a u => a ∈ vs ∧ f a = u
      | _ => ARB`>>
    qspecl_then [`w`,`vp`,`ep`,`LOG 2 (2 * vp − 1)`] assume_tac (GEN_ALL mk_satisfies_walk_k_alt)>>
    fs[Abbr`w`]>>
    qexists_tac`w'`>>simp[]>>
    rw[]
    >- (
      rename1`k_size`>>
      simp[k_size_def,satisfies_pbc_def,MAP_GENLIST, o_DEF,eval_lin_term_def]>>
      simp[neg_b2i]>>
      metis_tac[iSUM_GENLIST_geq_k_rev])
    >- (
      rename1`all_has_mapping`>>
      simp[all_has_mapping_def,satisfies_def,MEM_GENLIST,has_mapping_def]>>
      rw[]>>
      simp[satisfies_pbc_def,MAP_GENLIST,o_DEF,eval_lin_term_def]>>
      simp[iSUM_def]>>
      Cases_on`a ∈ vs`>>simp[]
      >- ( (* a ∈ vs *)
        DEP_REWRITE_TAC[iSUM_eq_1]>>
        CONJ_TAC>-
          (simp[MEM_GENLIST]>>metis_tac[])>>
        qexists_tac`f a`>>
        CONJ_ASM1_TAC>>fs[EL_GENLIST,INJ_DEF]) >>
      simp[iSUM_GENLIST_const])
    >- (
      rename1`all_one_one`>>
      simp[all_one_one_def,satisfies_def,MEM_GENLIST,one_one_def]>>
      rw[]>>
      simp[satisfies_pbc_def,MAP_GENLIST,o_DEF,eval_lin_term_def]>>
      fs[INJ_DEF]>>
      qmatch_goalsub_abbrev_tac`iSUM ls`>>
      `vp = LENGTH ls` by
        simp[Abbr`ls`]>>
      simp[]>>
      DEP_REWRITE_TAC[iSUM_sub_b2i_geq]>>
      simp[Abbr`ls`]>>
      CONJ_TAC>- (
        simp[MEM_GENLIST]>>
        metis_tac[])>>
      rw[]>>
      gs[EL_GENLIST]>>
      metis_tac[])
    >- (
      rename1`all_full_edge_map`>>
      simp[all_full_edge_map_def,satisfies_def,MEM_GENLIST,MEM_FLAT]>>
      rw[]>>
      gvs[MEM_FLAT,MEM_GENLIST,MEM_MAP]>>
      pop_assum mp_tac>>
      qmatch_goalsub_abbrev_tac`if P then _ else _`>>
      IF_CASES_TAC
      >- (
        rw[Abbr`P`]>>
        simp[satisfies_pbc_def,iSUM_def,eval_lin_term_def]>>
        Cases_on`a ∈ vs`>>simp[iSUM_def]>>
        `f a ≠ u` by metis_tac[MEM_neighbours]>>
        simp[])>>
      simp[MEM_FLAT,MEM_MAP,PULL_EXISTS,MEM_if]>>
      rw[]
      >- (
        (* edge_map constraint *)
        gvs[edge_map_def,MEM_if,MEM_neighbours]>>
        simp[satisfies_pbc_def,MAP_MAP_o,o_DEF,eval_lin_term_def]>>
        `b < vp` by
          (fs[good_graph_def,is_edge_thm]>>
          metis_tac[])>>
        simp[]>>
        reverse (Cases_on`b ∈ vs`)>>fs[]
        >- (
          simp[iSUM_def,iSUM_MAP_const]>>
          Cases_on`a ∈ vs ∧ f a = u`>>simp[])>>
        reverse (Cases_on`f a = u`>>rw[]>>simp[iSUM_def])
        >- (
          simp[intLib.COOPER_PROVE``!n:int. 1 + n ≥ 1 ⇔ n ≥ 0``]>>
          match_mp_tac iSUM_zero>>
          simp[MEM_MAP,MEM_neighbours]>>
          rw[]>>
          simp[])>>
        Cases_on`a ∈ vs`>>fs[]
        >- (
          match_mp_tac iSUM_geq>>
          rw[]
          >-
            (fs[MEM_MAP]>>pairarg_tac>>simp[])>>
          simp[MEM_MAP,MEM_FILTER,LAMBDA_PROD,PULL_EXISTS,EXISTS_PROD,MEM_neighbours]>>
          qexists_tac`f b`>>simp[]>>
          fs[INJ_DEF])>>
        simp[intLib.COOPER_PROVE``!n:int. 1 + n ≥ 1 ⇔ n ≥ 0``]>>
        match_mp_tac iSUM_zero>>
        simp[MEM_MAP,MEM_neighbours]>>
        rw[]>>
        simp[])
      >- (
        (* not_edge_map constraint *)
        gvs[not_edge_map_def,MEM_if,MEM_not_neighbours]>>
        simp[satisfies_pbc_def,MAP_MAP_o,o_DEF,eval_lin_term_def]>>
        reverse (Cases_on`b ∈ vs`)>>fs[]
        >- (
          simp[iSUM_def,iSUM_MAP_const]>>
          Cases_on`a ∈ vs ∧ f a = u`>>simp[])>>
        reverse (Cases_on`f a = u`>>rw[]>>simp[iSUM_def])
        >- (
          simp[intLib.COOPER_PROVE``!n:int. 1 + n ≥ 1 ⇔ n ≥ 0``]>>
          match_mp_tac iSUM_zero>>
          simp[MEM_MAP,MEM_not_neighbours]>>
          rw[]>>
          simp[])>>
        Cases_on`a ∈ vs`>>fs[]
        >- (
          match_mp_tac iSUM_geq>>
          rw[]
          >-
            (fs[MEM_MAP]>>pairarg_tac>>simp[])>>
          simp[MEM_MAP,MEM_FILTER,LAMBDA_PROD,PULL_EXISTS,EXISTS_PROD,MEM_not_neighbours]>>
          fs[INJ_DEF])>>
        simp[intLib.COOPER_PROVE``!n:int. 1 + n ≥ 1 ⇔ n ≥ 0``]>>
        match_mp_tac iSUM_zero>>
        simp[MEM_MAP,MEM_not_neighbours]>>
        rw[]>>
        simp[]))
    >- (
      (* connectedness *)
      rw[encode_connected_def]>>
      simp[satisfies_def,MEM_FLAT,MEM_GENLIST,PULL_EXISTS,satisfies_pbc_def,eval_lin_term_def]>>
      rw[]>>
      simp[satisfies_pbc_def,eval_lin_term_def]>>
      reverse (Cases_on`f' ∈ vs`)>>simp[iSUM_def]
      >- (
        qmatch_goalsub_abbrev_tac`b2i A + b2i B`>>
        Cases_on`A`>>Cases_on`B`>>simp[])>>
      reverse (Cases_on`g ∈ vs`)>>simp[iSUM_def]>>
      (drule_at (Pos (el 2))) satisfies_walk_k>>
      disch_then(qspecl_then[`f'`,`g`] assume_tac)>>gs[]>>
      fs[connected_subgraph_def]>>
      pop_assum kall_tac>>
      qpat_x_assum`∀a b. _ ⇒ is_connected _ _ _ _` (qspecl_then[`f'`,`g`] assume_tac)>>
      rfs[]>>
      drule is_connected_is_walk>>strip_tac>>
      gs[]>>
      drule is_walk_is_path>>strip_tac>>
      fs[is_path_def]>>
      qexists_tac`path`>>simp[]>>rw[]
      >- (
        fs[SUBSET_DEF,EVERY_MEM])>>
      `LENGTH (f'::path) <= vp` by
        (match_mp_tac ALL_DISTINCT_LENGTH_bound>>
        fs[]>>metis_tac[SUBSET_TRANS])>>
      `LENGTH path < vp` by fs[]>>
      `vp ≤ 2 ** LOG 2 (2 * vp − 1)` by
        (qspecl_then[`2`,`(2 * vp − 1)`] mp_tac logrootTheory.LOG>>
        simp[]>>rw[]>>
        fs[EXP])>>
      simp[]))>>
  fs[satisfiable_def,injective_partial_map_def]>>
  qexists_tac`λn. @m. m < vt ∧ w (Mapped n m)`>>
  qabbrev_tac`dom = {n | n < vp ∧ ¬ w (Unmapped n)}`>>
  qexists_tac `dom`>>
  simp[]>>
  reverse CONJ_TAC >- (
    fs[satisfies_def,encode_def,encode_connected_def]>>
    Cases_on`vp=0`>>fs[]
    >-
      rw[connected_subgraph_def,Abbr`dom`]>>
    fs[SF DNF_ss,MEM_FLAT,MEM_GENLIST,PULL_EXISTS,satisfies_pbc_def,eval_lin_term_def]>>
    rw[connected_subgraph_def,Abbr`dom`]>>
    match_mp_tac is_walk_is_connected>>
    qpat_x_assum`good_graph (vp,ep)` assume_tac>>
    wlog_tac`a < b`[`a`,`b`]
    >- (
      `a=b ∨ b < a` by fs[]
      >-
        (qexists_tac`[]`>>simp[is_walk_def])>>
      first_x_assum drule>>rw[]>>
      drule good_graph_is_walk_REVERSE>>
      disch_then drule>>
      disch_then (irule_at Any)>>
      fs[SUBSET_DEF]>>
      rw[]>>drule MEM_TL>>fs[]>>
      metis_tac[])>>
    qpat_x_assum`b < vp` mp_tac>>
    first_x_assum drule>>
    strip_tac>>
    strip_tac>>
    first_x_assum drule>>
    simp[satisfies_pbc_def,iSUM_def,eval_lin_term_def]>>strip_tac>>
    drule (SIMP_RULE std_ss [satisfies_def] satisfies_walk_k)>>
    disch_then drule>>
    disch_then(qspecl_then[`a`,`b`] assume_tac)>>
    gs[]>>
    qexists_tac`walk`>>fs[SUBSET_DEF,EVERY_MEM])>>
  CONJ_TAC>-
    simp[Abbr`dom`,SUBSET_DEF]>>
  fs[satisfies_def,encode_def,encode_base_def,SF DNF_ss]>>
  CONJ_TAC>- (
    fs[k_size_def,satisfies_pbc_def,MAP_GENLIST,o_DEF,neg_b2i,eval_lin_term_def]>>
    match_mp_tac iSUM_GENLIST_geq_k>>
    qexists_tac`vp`>>fs[Abbr`dom`,SUBSET_DEF]>>
    qmatch_asmsub_abbrev_tac`iSUM ls1`>>
    qmatch_goalsub_abbrev_tac`iSUM ls2`>>
    `ls1 = ls2` by
      (unabbrev_all_tac>>simp[LIST_EQ])>>
    fs[])>>
  `∀n. n < vp ∧ ¬w (Unmapped n) ⇒
   ∃m. m < vt ∧ w (Mapped n m) ∧
   ∀m'. m' < vt ∧ w (Mapped n m') ⇔ m = m'` by (
     fs[all_has_mapping_def,MEM_GENLIST,has_mapping_def,PULL_EXISTS]>>
     rw[]>>
     first_x_assum drule>>
     simp[satisfies_pbc_def,MAP_GENLIST,o_DEF,eval_lin_term_def]>>
     simp[iSUM_def]>>
     DEP_REWRITE_TAC[iSUM_eq_1]>>
     CONJ_TAC>-
       (simp[MEM_GENLIST]>>metis_tac[])>>
     rw[]>>gs[EL_GENLIST]>>
     asm_exists_tac>>fs[]>>
     CCONTR_TAC>>gs[]>>
     Cases_on`i=m'`>>gs[]>>
     first_x_assum drule>>
     fs[])>>
  rw[]
  >- (
    fs[Abbr`dom`]>>
    rw[INJ_DEF]
    >- (
      first_x_assum drule>>strip_tac>>
      rfs[])>>
    fs[all_one_one_def,MEM_GENLIST,PULL_EXISTS,one_one_def]>>
    res_tac>>
    gvs[]>>
    last_x_assum drule>>
    simp[satisfies_pbc_def,MAP_GENLIST,o_DEF,eval_lin_term_def]>>
    qmatch_goalsub_abbrev_tac`iSUM ls`>>
    `vp = LENGTH ls` by
      simp[Abbr`ls`]>>
    simp[]>>
    DEP_REWRITE_TAC[iSUM_sub_b2i_geq]>>
    simp[Abbr`ls`]>>
    CONJ_TAC>- (
      simp[MEM_GENLIST]>>
      metis_tac[])>>
    rw[]>>
    first_x_assum drule>>
    simp[EL_GENLIST]>>
    disch_then(qspec_then`n` mp_tac)>>
    simp[])
  >- (
    fs[Abbr`dom`,good_graph_def]>>
    first_assum(qspec_then`a` mp_tac)>>
    first_x_assum(qspec_then`b` drule)>>
    simp[]>> rw[]>>
    gvs[]>>
    fs[all_full_edge_map_def,satisfies_def,MEM_GENLIST,MEM_FLAT,edge_map_def,PULL_EXISTS,MEM_MAP,FORALL_PROD]>>
    `is_edge ep b a` by
      fs[is_edge_thm]>>
    first_x_assum (drule_at (Pos (el 2)))>>
    qpat_x_assum`m < _` assume_tac>>
    disch_then drule>>
    qmatch_goalsub_abbrev_tac`if P then _ else _`>>
    IF_CASES_TAC
    >- (
      fs[Abbr`P`]>>
      simp[satisfies_pbc_def,iSUM_def,eval_lin_term_def])>>
    simp[MEM_FLAT,MEM_MAP,MEM_neighbours,SF DNF_ss,MEM_if]>>
    Cases_on` b = a` >-
      metis_tac[]>>
    strip_tac>> pop_assum kall_tac>>
    pop_assum drule>>
    simp[satisfies_pbc_def,iSUM_def,MAP_MAP_o,o_DEF,LAMBDA_PROD,MEM_neighbours,eval_lin_term_def]>>
    strip_tac>>
    gs[]>>
    drule iSUM_geq_1>>
    simp[MEM_MAP,PULL_EXISTS,MEM_FILTER,FORALL_PROD]>>
    impl_tac >- metis_tac[]>>
    strip_tac>>
    gs[EL_MAP]>>
    qmatch_asmsub_abbrev_tac`Mapped _ ee`>>
    `m' = ee` by (
      unabbrev_all_tac>>
      metis_tac[MEM_EL,MEM_neighbours,is_edge_thm])>>
    rw[]>>
    `MEM ee (neighbours et m)` by
      metis_tac[EL_MEM,Abbr`ee`]>>
    fs[MEM_neighbours]>>
    metis_tac[is_edge_thm])
  >- (
    fs[Abbr`dom`,good_graph_def]>>
    first_assum(qspec_then`a` mp_tac)>>
    first_x_assum(qspec_then`b` drule)>>
    simp[]>> rw[]>>
    gvs[]>>
    fs[all_full_edge_map_def,satisfies_def,MEM_FLAT,MEM_GENLIST,PULL_EXISTS,MEM_MAP,MEM_not_neighbours,not_edge_map_def]>>
    first_x_assum (drule_at (Pos (el 1)))>>
    qpat_x_assum`a < vp` assume_tac>>
    disch_then drule>>simp[]>>
    qmatch_goalsub_abbrev_tac`if P then _ else _`>>
    IF_CASES_TAC
    >- (
      fs[Abbr`P`]>>
      simp[satisfies_pbc_def,iSUM_def,eval_lin_term_def])>>
    simp[MEM_FLAT,MEM_MAP,MEM_not_neighbours,SF DNF_ss,MEM_if]>>
    Cases_on` b = a` >-
      metis_tac[]>>
    strip_tac>>
    pop_assum (drule_at (Pos (el 2)))>>
    simp[satisfies_pbc_def,iSUM_def,MAP_MAP_o,o_DEF,LAMBDA_PROD,eval_lin_term_def]>>
    strip_tac>>
    drule iSUM_geq_1>>
    simp[MEM_MAP,PULL_EXISTS,MEM_FILTER,FORALL_PROD]>>
    impl_tac >- metis_tac[]>>
    strip_tac>>
    gs[EL_MAP]>>
    qmatch_asmsub_abbrev_tac`Mapped b ee`>>
    `m = ee` by (
      unabbrev_all_tac>>
      metis_tac[MEM_EL,MEM_not_neighbours])>>
    rw[]>>
    `MEM ee (not_neighbours (vt,et) m')` by
      metis_tac[EL_MEM,Abbr`ee`]>>
    fs[MEM_not_neighbours])
QED

val pattern = ``(5, fromAList [(0,[1;3;4]); (1,[0;3;4]);  (2,[3]); (3,[0;1;2]); (4,[0;1])]):graph``
val target = ``(5, fromAList [(0,[1;3;4]); (1,[0;3;4]);  (2,[3]); (3,[0;1;2]); (4,[0;1])]):graph``

Definition enc_string_def:
  (enc_string (Walk f g k) =
    concat [strlit"xconn";toString k;strlit"_";toString f;strlit"_";toString g]) ∧
  (enc_string (Aux f h g k) =
    concat [strlit"xconn_";toString k;strlit"_";toString f;strlit"_";toString g;strlit"_via_";toString h]) ∧
  (enc_string (Unmapped f) =
    concat [strlit"x";toString f;strlit"_null"]) ∧
  (enc_string (Mapped f g) =
    concat [strlit"x";toString f;strlit"_";toString g])
End

Theorem enc_string_INJ:
  INJ enc_string UNIV UNIV
Proof
  rw[INJ_DEF]
  \\ Cases_on`x` \\ Cases_on`y`
  \\ fs[enc_string_def]
  \\ fs [mlstringTheory.concat_def]
  \\ every_case_tac \\ gvs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ TRY (imp_res_tac mlintTheory.num_to_str_imp_cons \\ gvs [] \\ NO_TAC)
  \\ rpt (drule mlintTheory.num_to_str_APPEND_11 \\ simp []
          \\ disch_then drule_all \\ strip_tac \\ gvs []
          \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND])
  \\ rpt (qpat_x_assum ‘_ = strlit _’ (assume_tac o GSYM))
  \\ fs [mlintTheory.num_to_str_11]
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ drule mlintTheory.num_to_str_APPEND_11 \\ simp []
  \\ rpt $ irule_at Any (METIS_PROVE [] “x = y ⇒ f x = f y”) \\ fs []
  \\ rw [] \\ strip_tac \\ gvs []
  \\ imp_res_tac mlintTheory.num_to_str_imp_cons \\ gvs []
QED

Theorem enc_string_goodString:
  goodString (enc_string e)
Proof
  Induct_on ‘e’
  \\ gvs [enc_string_def,mlstringTheory.concat_def,goodString_eq_EVERY_goodChar]
  \\ gvs [goodChar_toString]
  \\ EVAL_TAC
QED

Definition full_encode_def:
  full_encode gp gt k =
  MAP (map_pbc enc_string) (encode gp gt k)
End

Theorem full_encode_correct:
  good_graph gp ∧
  good_graph gt ∧
  full_encode gp gt k = constraints ⇒
  (
    (∃f vs.
      injective_partial_map f vs k gp gt ∧
      connected_subgraph vs (SND gp)) ⇔
    satisfiable (set constraints)
  )
Proof
  rw[full_encode_def]>>
  simp[LIST_TO_SET_MAP]>>
  DEP_REWRITE_TAC[satisfiable_INJ_iff]>>
  rw[]
  >- (
    assume_tac enc_string_INJ>>
    drule INJ_SUBSET>>
    disch_then match_mp_tac>>
    simp[])>>
  metis_tac[encode_correct,PAIR]
QED

Theorem pbf_vars_full_encode:
  pbf_vars (set (full_encode gp gt k)) ⊆ goodString
Proof
  rw[SUBSET_DEF,full_encode_def,LIST_TO_SET_MAP,pbf_vars_IMAGE]>>
  simp[IN_DEF]>>
  metis_tac[enc_string_goodString,PAIR]
QED

val _ = export_theory();

(*
  Implement and prove correct monadic version of encoder
*)
open preamble state_transformerTheory
open ml_monadBaseLib ml_monadBaseTheory
open asmTheory lab_to_targetTheory monadic_encTheory

val _ = new_theory "monadic_enc64"
val _ = monadsyntax.temp_add_monadsyntax()

Overload monad_bind[local] = ``st_ex_bind``
Overload monad_unitbind[local] = ``\x y. st_ex_bind x (\z. y)``
Overload monad_ignore_bind[local] = ``\x y. st_ex_bind x (\z. y)``
Overload return[local] = ``st_ex_return``

(* Data type for the exceptions *)
Datatype:
  state_exn_64 = Fail string | Subscript
End

val sub_exn = ``Subscript``;
val update_exn = ``Subscript``;

fun accessor_thm (a,b,c,d,e,f) = LIST_CONJ [b,c,d,e,f]

(* 64 BIT IMPLEMENTATION *)

(* The state is just an array *)
Datatype:
  enc_state_64 = <|
       hash_tab_64 : ((64 asm # word8 list) list) list
     |>
End

(* Monadic functions to handle the exceptions *)
val exn_functions = define_monad_exception_functions ``:state_exn_64`` ``:enc_state_64``;
Overload failwith[local] = ``raise_Fail``

val accessors = define_monad_access_funs ``:enc_state_64``;

val hash_tab_64_accessors = el 1 accessors;
val (hash_tab_64,get_hash_tab_64_def,set_hash_tab_64_def) = hash_tab_64_accessors;

(* Fixed-size array manipulators *)
val arr_manip = define_MFarray_manip_funs
  [hash_tab_64_accessors] sub_exn update_exn;

val hash_tab_64_manip = el 1 arr_manip;

Theorem hash_tab_64_accessor =
  accessor_thm hash_tab_64_manip

Definition lookup_ins_table_64_def:
  lookup_ins_table_64 enc n a =
  let v = hash_asm n a MOD n in
  do
    ls <- hash_tab_64_sub v;
    case ALOOKUP ls a of
      NONE =>
      do
        encode <- return (enc a);
        update_hash_tab_64 v ((a,encode)::ls);
        return encode
      od
    | SOME res =>
      return res
  od
End

Definition enc_line_hash_64_def:
  (enc_line_hash_64 enc skip_len n (Label n1 n2 n3) =
    return (Label n1 n2 skip_len)) ∧
  (enc_line_hash_64 enc skip_len n (Asm a _ _) =
    do
      bs <- lookup_ins_table_64 enc n (cbw_to_asm a);
      return (Asm a bs (LENGTH bs))
    od) ∧
  (enc_line_hash_64 enc skip_len n (LabAsm l _ _ _) =
     do
       bs <- lookup_ins_table_64 enc n (lab_inst 0w l);
       return (LabAsm l 0w bs (LENGTH bs))
     od)
End

Definition enc_line_hash_64_ls_def:
  (enc_line_hash_64_ls enc skip_len n [] = return []) ∧
  (enc_line_hash_64_ls enc skip_len n (x::xs) =
  do
    fx <- enc_line_hash_64 enc skip_len n x;
    fxs <- enc_line_hash_64_ls enc skip_len n xs;
    return (fx::fxs)
  od)
End

Definition enc_sec_hash_64_ls_def:
  (enc_sec_hash_64_ls enc skip_len n [] = return []) ∧
  (enc_sec_hash_64_ls enc skip_len n (x::xs) =
  case x of Section k ys =>
  do
    ls <- enc_line_hash_64_ls enc skip_len n ys;
    rest <- enc_sec_hash_64_ls enc skip_len n xs;
    return (Section k ls::rest)
  od)
End

Definition enc_sec_hash_64_ls_full_def:
  enc_sec_hash_64_ls_full enc n xs =
  enc_sec_hash_64_ls enc (LENGTH (enc (Inst Skip))) n xs
End

(* As we are using fixed-size array, we need to define a different record type for the initialization *)
val array_fields_names = ["hash_tab_64"];
val run_ienc_state_64_def = define_run ``:enc_state_64``
                                      array_fields_names
                                      "ienc_state_64";

Definition enc_secs_64_aux_def:
  enc_secs_64_aux enc n xs =
    run_ienc_state_64 (enc_sec_hash_64_ls_full enc n xs) <| hash_tab_64 := (n, []) |>
End

Definition enc_secs_64_def:
  enc_secs_64 enc n xs =
    case enc_secs_64_aux enc (if n = 0 then 1 else n) xs of
      M_success xs => xs
    | M_failure _ => []
End

val msimps = [st_ex_bind_def,st_ex_return_def];

Theorem Msub_eqn[simp]:
    ∀e n ls v.
  Msub e n ls =
  if n < LENGTH ls then M_success (EL n ls)
                   else M_failure e
Proof
  ho_match_mp_tac Msub_ind>>rw[]>>
  simp[Once Msub_def]>>
  Cases_on`ls`>>fs[]>>
  IF_CASES_TAC>>fs[]>>
  Cases_on`n`>>fs[]
QED

Theorem hash_tab_64_sub_eqn[simp]:
    hash_tab_64_sub n s =
  if n < LENGTH s.hash_tab_64 then
    (M_success (EL n s.hash_tab_64),s)
  else
    (M_failure (Subscript),s)
Proof
  rw[fetch "-" "hash_tab_64_sub_def"]>>
  fs[Marray_sub_def]
QED

Theorem Mupdate_eqn[simp]:
    ∀e x n ls.
  Mupdate e x n ls =
  if n < LENGTH ls then
    M_success (LUPDATE x n ls)
  else
    M_failure e
Proof
  ho_match_mp_tac Mupdate_ind>>rw[]>>
  simp[Once Mupdate_def]>>
  Cases_on`ls`>>fs[]>>
  IF_CASES_TAC>>fs[LUPDATE_def]>>
  Cases_on`n`>>fs[LUPDATE_def]
QED

Theorem update_hash_tab_64_eqn[simp]:
    update_hash_tab_64 n t s =
  if n < LENGTH s.hash_tab_64 then
     (M_success (),s with hash_tab_64 := LUPDATE t n s.hash_tab_64)
  else
     (M_failure (Subscript),s)
Proof
  rw[fetch "-" "update_hash_tab_64_def"]>>
  fs[Marray_update_def]
QED

Definition good_table_64_def:
  good_table_64 enc n s ⇔
  EVERY (λls. EVERY (λ(x,y). enc x = y) ls) s.hash_tab_64 ∧
  LENGTH s.hash_tab_64 = n
End

Triviality lookup_ins_table_64_correct:
  good_table_64 enc n s ∧
  0 < n ⇒
  ∃s'.
  lookup_ins_table_64 enc n aa s = (M_success (enc aa), s') ∧
  good_table_64 enc n s'
Proof
  rw[]>>fs[lookup_ins_table_64_def]>>
  simp msimps>>
  reverse IF_CASES_TAC
  >- (
    fs[good_table_64_def]>>
    rfs[])>>
  simp[]>>
  TOP_CASE_TAC
  >- (
    fs[good_table_64_def]>>
    match_mp_tac IMP_EVERY_LUPDATE>>fs[]>>
    old_drule EL_MEM>>
    metis_tac[EVERY_MEM])
  >>
  fs[good_table_64_def]>>
  old_drule EL_MEM>>
  old_drule ALOOKUP_MEM>>
  fs[EVERY_MEM]>>
  rw[]>> first_x_assum old_drule>>
  disch_then old_drule>>
  fs[]
QED

Triviality enc_line_hash_64_correct:
  ∀line.
  good_table_64 enc n s ∧ 0 < n ⇒
  ∃s'.
  enc_line_hash_64 enc skip_len n line s =
  (M_success (enc_line enc skip_len line),s') ∧
  good_table_64 enc n s'
Proof
  Cases>>fs[enc_line_hash_64_def,enc_line_def]>>
  fs msimps>>
  qmatch_goalsub_abbrev_tac`lookup_ins_table_64 _ _ aa`>>
  rw[]>>
  old_drule lookup_ins_table_64_correct>>rw[]>>simp[]
QED

Triviality enc_line_hash_64_ls_correct:
  ∀xs s.
  good_table_64 enc n s ∧ 0 < n ⇒
  ∃s'.
  enc_line_hash_64_ls enc skip_len n xs s =
  (M_success (MAP (enc_line enc skip_len) xs), s') ∧
  good_table_64 enc n s'
Proof
  Induct>>fs[enc_line_hash_64_ls_def]>>
  fs msimps>>
  rw[]>> simp[]>>
  old_drule enc_line_hash_64_correct>>
  disch_then (qspec_then `h` assume_tac)>>rfs[]>>
  first_x_assum old_drule>>
  rw[]>>simp[]
QED

Triviality enc_sec_hash_64_ls_correct:
  ∀xs s.
  good_table_64 enc n s ∧ 0 < n ⇒
  ∃s'.
  enc_sec_hash_64_ls enc skip_len n xs s =
  (M_success (MAP (enc_sec enc skip_len) xs), s') ∧
  good_table_64 enc n s'
Proof
  Induct>>fs[enc_sec_hash_64_ls_def]>>
  fs msimps>>
  rw[]>> simp[]>>
  TOP_CASE_TAC>>simp[]>>
  old_drule enc_line_hash_64_ls_correct>>
  simp[]>>
  disch_then(qspec_then`l` assume_tac)>>fs[]>>
  first_x_assum old_drule>>rw[]>>
  simp[enc_sec_def]
QED

Theorem enc_secs_64_correct:
  enc_secs_64 enc n xs =
  (enc_sec_list enc xs)
Proof
  fs[enc_secs_64_def,enc_secs_64_aux_def]>>
  fs[fetch "-" "run_ienc_state_64_def",run_def]>>
  simp[enc_sec_hash_64_ls_full_def]>>
  qmatch_goalsub_abbrev_tac `_ enc sl nn xs s`>>
  qspecl_then [`sl`,`nn`,`enc`,`xs`,`s`] mp_tac (GEN_ALL enc_sec_hash_64_ls_correct)>>
  impl_tac>-
    (unabbrev_all_tac>>fs[good_table_64_def,EVERY_REPLICATE])>>
  rw[]>>
  fs[enc_sec_list_def]
QED

val _ = export_theory();

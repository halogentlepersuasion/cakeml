(*
  Correctness proof for stack_remove
*)
open preamble
     stack_removeTheory
     stackLangTheory
     stackSemTheory
     stackPropsTheory
     set_sepTheory
     semanticsPropsTheory
     helperLib
local open dep_rewrite blastLib (*labPropsTheory*) in end

val _ = new_theory"stack_removeProof";

val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = diminish_srw_ss ["ABBREV"]
val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]
val _ = set_trace "BasicProvers.var_eq_old" 1

val word_shift_def = backend_commonTheory.word_shift_def
Overload num_stubs[local] = ``stack_num_stubs``
val drule = old_drule

(* TODO: move *)

Theorem word_list_exists_thm:
   (word_list_exists a 0 = emp) /\
    (word_list_exists a (SUC n) =
     SEP_EXISTS w. one (a,w) * word_list_exists (a + bytes_in_word) n)
Proof
  full_simp_tac(srw_ss())[word_list_exists_def,LENGTH_NIL,FUN_EQ_THM,ADD1,
          SEP_EXISTS_THM,cond_STAR,word_list_def,SEP_CLAUSES]
  \\ srw_tac[][] \\ eq_tac \\ srw_tac[][]
  THEN1
   (Cases_on `xs` \\ full_simp_tac(srw_ss())[ADD1]
    \\ full_simp_tac(srw_ss())[word_list_def]
    \\ qexists_tac `h` \\ full_simp_tac(srw_ss())[]
    \\ qexists_tac `t` \\ full_simp_tac(srw_ss())[SEP_CLAUSES])
  \\ qexists_tac `w::xs`
  \\ full_simp_tac(srw_ss())[word_list_def,ADD1,STAR_ASSOC,cond_STAR]
QED

Theorem word_list_exists_ADD:
   !m n a.
      word_list_exists a (m + n) =
      word_list_exists a m *
      word_list_exists (a + bytes_in_word * n2w m) n
Proof
  Induct \\ full_simp_tac(srw_ss())[word_list_exists_thm,SEP_CLAUSES,ADD_CLAUSES]
  \\ full_simp_tac(srw_ss())[STAR_ASSOC,ADD1,GSYM word_add_n2w,
       WORD_LEFT_ADD_DISTRIB]
QED

Theorem word_list_APPEND:
   !xs ys a.
      word_list a (xs ++ ys) =
      word_list a xs * word_list (a + bytes_in_word * n2w (LENGTH xs)) ys
Proof
  Induct \\ full_simp_tac(srw_ss())[word_list_def,SEP_CLAUSES,STAR_ASSOC,ADD1,GSYM word_add_n2w]
  \\ full_simp_tac(srw_ss())[WORD_LEFT_ADD_DISTRIB]
QED

Theorem LESS_LENGTH_IMP_APPEND:
   !xs n. n < LENGTH xs ==> ?ys zs. xs = ys ++ zs /\ LENGTH ys = n
Proof
  Induct \\ full_simp_tac(srw_ss())[] \\ Cases_on `n` \\ full_simp_tac(srw_ss())[LENGTH_NIL]
  \\ srw_tac[][] \\ res_tac \\ srw_tac[][]
  \\ pop_assum (fn th => simp [Once th])
  \\ qexists_tac `h::ys` \\ full_simp_tac(srw_ss())[]
QED

Theorem call_FFI_LENGTH:
   (call_FFI s i conf xs = FFI_return n ys) ==> (LENGTH ys = LENGTH xs)
Proof
  srw_tac[][ffiTheory.call_FFI_def]
  \\ every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][]
QED

Theorem with_same_clock[simp]:
   x with clock := x.clock = x
Proof
  srw_tac[][state_component_equality]
QED

Theorem set_var_set_var[simp]:
   set_var x y (set_var x z w) = set_var x y w
Proof
  EVAL_TAC \\ srw_tac[][state_component_equality]
QED

Theorem get_var_set_var_same[simp]:
   get_var x (set_var x y z) = SOME y
Proof
  EVAL_TAC
QED

Theorem get_var_set_var:
   get_var x (set_var x' y z) = if x = x' then SOME y else get_var x z
Proof
  EVAL_TAC \\ srw_tac[][]
QED

Theorem bytes_in_word_word_shift:
   good_dimindex(:'a) ∧ w2n (bytes_in_word:'a word) * w2n n < dimword(:'a) ⇒
   (bytes_in_word:'a word * n) >>> word_shift (:'a) = n
Proof
  EVAL_TAC \\ srw_tac[][] \\ pop_assum mp_tac
  \\ blastLib.BBLAST_TAC \\ simp[]
  \\ blastLib.BBLAST_TAC \\ srw_tac[][]
  \\ match_mp_tac lsl_lsr
  \\ simp[]
  \\ Cases_on`n`\\full_simp_tac(srw_ss())[word_lsl_n2w]
  \\ full_simp_tac(srw_ss())[dimword_def]
QED

Theorem word_offset_eq:
   word_offset n = bytes_in_word * n2w n
Proof
  full_simp_tac(srw_ss())[word_offset_def,word_mul_n2w,bytes_in_word_def]
QED

Definition memory_def:
  memory m dm = \s. s = fun2set (m, dm)
End

Definition word_list_rev_def:
  (word_list_rev a [] = emp) /\
  (word_list_rev a (x::xs) =
     one (a - bytes_in_word, x) * word_list_rev (a - bytes_in_word) xs)
End

Definition word_store_def:
  word_store base store =
    word_list_rev base
      (MAP (\name. case FLOOKUP store name of
                   | NONE => Word 0w | SOME x => x) store_list)
End

Definition code_rel_def:
  code_rel jump off k code1 code2 <=>
    (!n prog.
      lookup n code1 = SOME prog ==>
      reg_bound prog k /\
      lookup n code2 = SOME (comp jump off k prog)) ∧
    domain code2 = domain code1 ∪ {0;1;2}
End (* exact characterization for Install *)

Definition is_SOME_Word_def:
  (is_SOME_Word (SOME (Word w)) = T) /\
  (is_SOME_Word _ = F)
End

Definition the_SOME_Word_def:
  (the_SOME_Word (SOME (Word w)) = w)
End

Definition state_rel_def:
  state_rel jump off k (s1:('a,'c,'ffi) stackSem$state) s2 <=>
    s1.use_stack /\ s1.use_store /\
    ~s2.use_stack /\ ~s2.use_store /\
    ~s2.use_alloc /\ ~s1.use_alloc /\
    s2.be = s1.be /\
    s2.gc_fun = s1.gc_fun /\
    s2.clock = s1.clock /\
    s2.ffi = s1.ffi /\
    s2.ffi_save_regs = s1.ffi_save_regs /\
    s2.fp_regs = s1.fp_regs /\
    s2.code_buffer = s1.code_buffer /\
    s2.sh_mdomain = s1.sh_mdomain ∧
    s1.compile = (λc p. s2.compile c (MAP (prog_comp jump off k) p)) /\
    (* s2.data_buffer = empty_buffer /\ *)
    s2.compile_oracle = (λn. (I ## MAP (prog_comp jump off k) ## I (*K []*)) (s1.compile_oracle n)) /\
    (∀n i p. MEM (i,p) (FST(SND(s1.compile_oracle n ))) ⇒ reg_bound p k ∧ num_stubs ≤ i+1) ∧
    good_dimindex (:'a) /\
    (!n.
       n < k ==>
       FLOOKUP s2.regs n = FLOOKUP s1.regs n) /\
    code_rel jump off k s1.code s2.code /\
    lookup stack_err_lab s2.code = SOME (halt_inst 2w) /\
    FLOOKUP s2.regs (k+2) = FLOOKUP s1.store CurrHeap /\
    {k;k+1;k+2} SUBSET s2.ffi_save_regs /\
    is_SOME_Word (FLOOKUP s1.store BitmapBase) /\
    s1.stack_space <= LENGTH s1.stack /\
    let bp = (the_SOME_Word (FLOOKUP s1.store BitmapBase) << word_shift (:'a)) in
    let all_bitmaps = s1.bitmaps ++ s1.data_buffer.buffer in
      s1.data_buffer.position = bp + bytes_in_word * n2w (LENGTH s1.bitmaps) /\
    case FLOOKUP s2.regs (k+1) of
    | SOME (Word base) =>
      dimindex (:'a) DIV 8 * max_stack_alloc <= w2n base /\
      w2n base + w2n (bytes_in_word:'a word) * LENGTH s1.stack < dimword (:'a) /\
      FLOOKUP s2.regs k =
        SOME (Word (base + bytes_in_word * n2w s1.stack_space)) /\
      (memory s1.memory s1.mdomain *
       word_list bp (MAP Word all_bitmaps) *
       word_list_exists (bp + bytes_in_word * n2w(LENGTH all_bitmaps)) s1.data_buffer.space_left *
       word_store base s1.store *
       word_list base s1.stack)
        (fun2set (s2.memory,s2.mdomain))
    | _ => F
End

Triviality state_rel_get_var:
  state_rel jump off k s t /\ n < k ==> (get_var n s = get_var n t)
Proof
  full_simp_tac(srw_ss())[state_rel_def,get_var_def]
QED

Triviality state_rel_IMP:
  state_rel jump off k s t1 ==>
    state_rel jump off k (dec_clock s) (dec_clock t1)
Proof
  srw_tac[][] \\ full_simp_tac(srw_ss())[state_rel_def,dec_clock_def,empty_env_def] \\ rev_full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ res_tac \\ full_simp_tac(srw_ss())[]
QED

Triviality state_rel_with_clock:
  state_rel jump off k s t1 ==>
    state_rel jump off k (s with clock := c) (t1 with clock := c)
Proof
  srw_tac[][] \\ full_simp_tac(srw_ss())[state_rel_def,dec_clock_def,empty_env_def] \\ rev_full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ res_tac \\ full_simp_tac(srw_ss())[]
QED

Theorem state_rel_const:
   state_rel jump off k s t ⇒
   t.code_buffer = s.code_buffer ∧
   t.sh_mdomain = s.sh_mdomain ∧
   ¬t.use_stack ∧ s.use_stack ∧ t.ffi = s.ffi ∧
   t.compile_oracle = (λn. (I ## MAP (prog_comp jump off k) ## I (*K []*)) (s.compile_oracle n)) ∧
   s.compile = (λc p. t.compile c (MAP (prog_comp jump off k) p))
Proof
  fs[state_rel_def]
QED

Triviality find_code_lemma:
  state_rel jump off k s t1 /\
    (case dest of INL v2 => T | INR i => i < k) /\
    find_code dest s.regs s.code = SOME x ==>
    find_code dest t1.regs t1.code = SOME (comp jump off k x) /\ reg_bound x k
Proof
  CASE_TAC \\ full_simp_tac(srw_ss())[find_code_def,state_rel_def,code_rel_def]
  \\ strip_tac \\ res_tac
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[] \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[] \\ res_tac
QED

Triviality find_code_lemma2:
  state_rel jump off k s t1 /\
    (case dest of INL v2 => T | INR i => i < k) /\
    find_code dest (s.regs \\ x1) s.code = SOME x ==>
    find_code dest (t1.regs \\ x1) t1.code = SOME (comp jump off k x) /\ reg_bound x k
Proof
  CASE_TAC \\ full_simp_tac(srw_ss())[find_code_def,state_rel_def,code_rel_def]
  \\ strip_tac \\ res_tac
  \\ fs[DOMSUB_FLOOKUP_THM]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[] \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[] \\ res_tac
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[] \\ res_tac
QED

Theorem state_rel_set_var[simp]:
   state_rel jump off k s t1 /\ v < k ==>
    state_rel jump off k (set_var v x s) (set_var v x t1)
Proof
  fs[state_rel_def,set_var_def]>> strip_tac>> simp[] >>
  fs[FLOOKUP_UPDATE]>>
  metis_tac[]
QED

Triviality word_store_CurrHeap:
  word_store base (s.store |+ (CurrHeap,x)) = word_store base s.store
Proof
  full_simp_tac(srw_ss())[word_store_def,store_list_def,FLOOKUP_UPDATE]
QED

Triviality memory_fun2set_IMP_read:
  (memory m d * p) (fun2set (m1,d1)) /\ a IN d ==>
    a IN d1 /\ m1 a = m a
Proof
  simp [Once STAR_def,set_sepTheory.SPLIT_EQ,memory_def]
  \\ full_simp_tac(srw_ss())[fun2set_def,SUBSET_DEF,PULL_EXISTS]
QED

Triviality state_rel_read:
  state_rel jump off k s t /\ a IN s.mdomain ==>
    a IN t.mdomain /\ (t.memory a = s.memory a)
Proof
  full_simp_tac(srw_ss())[state_rel_def] \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ strip_tac
  \\ full_simp_tac(srw_ss())[GSYM STAR_ASSOC] \\ metis_tac [memory_fun2set_IMP_read]
QED

Triviality mem_load_32_IMP:
  state_rel jump off k s t /\
    mem_load_32 s.memory s.mdomain s.be a = SOME x ==>
    mem_load_32 t.memory t.mdomain t.be a = SOME x
Proof
   full_simp_tac(srw_ss())[wordSemTheory.mem_load_32_def] \\ srw_tac[][]
  \\ `s.be = t.be` by full_simp_tac(srw_ss())[state_rel_def]
  \\ ntac 5 (FULL_CASE_TAC >> fs[]) >> gvs[]
  \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ imp_res_tac state_rel_read
  \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
QED

Triviality mem_load_byte_aux_IMP:
  state_rel jump off k s t /\
    mem_load_byte_aux s.memory s.mdomain s.be a = SOME x ==>
    mem_load_byte_aux t.memory t.mdomain t.be a = SOME x
Proof
  full_simp_tac(srw_ss())[wordSemTheory.mem_load_byte_aux_def] \\ srw_tac[][]
  \\ `s.be = t.be` by full_simp_tac(srw_ss())[state_rel_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ imp_res_tac state_rel_read
  \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
QED

Triviality read_bytearray_IMP_read_bytearray:
  !n a k s t x.
      state_rel jump off k s t /\
      read_bytearray a n (mem_load_byte_aux s.memory s.mdomain s.be) = SOME x ==>
      read_bytearray a n (mem_load_byte_aux t.memory t.mdomain t.be) = SOME x
Proof
  Induct \\ full_simp_tac(srw_ss())[read_bytearray_def]
  \\ srw_tac[][] \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ res_tac \\ srw_tac[][]
  \\ imp_res_tac mem_load_byte_aux_IMP \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
QED

Triviality write_bytearray_IGNORE_non_aligned:
  !new_bytes a.
      (!x. b <> byte_align x) ==>
      write_bytearray a new_bytes m d be b = m b
Proof
  Induct \\ full_simp_tac(srw_ss())[wordSemTheory.write_bytearray_def] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[wordSemTheory.mem_store_byte_aux_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
QED

Triviality write_bytearray_IGNORE:
  !new_bytes a x xx.
      d1 SUBSET d /\
      read_bytearray a (LENGTH new_bytes) (mem_load_byte_aux m1 d1 be) = SOME x /\ xx ∉ d1 ==>
      write_bytearray a new_bytes m d be xx = m xx
Proof
  Induct_on `new_bytes`
  \\ full_simp_tac(srw_ss())[wordSemTheory.write_bytearray_def,read_bytearray_def]
  \\ full_simp_tac(srw_ss())[wordSemTheory.mem_load_byte_aux_def]
  \\ full_simp_tac(srw_ss())[wordSemTheory.mem_store_byte_aux_def]
  \\ rpt gen_tac \\ every_case_tac
  \\ srw_tac[][] \\ res_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
QED

Triviality write_bytearray_EQ:
  !new_bytes a m1 m y x.
      d1 SUBSET d /\ (!a. a IN d1 ==> m1 a = m a /\ a IN d) /\
      read_bytearray a (LENGTH new_bytes) (mem_load_byte_aux m1 d1 be) = SOME y /\ m1 x = m x ==>
      write_bytearray a new_bytes m1 d1 be x =
      write_bytearray a new_bytes m d be x
Proof
  Induct_on `new_bytes`
  \\ full_simp_tac(srw_ss())[wordSemTheory.write_bytearray_def,read_bytearray_def]
  \\ rpt gen_tac \\ ntac 2 BasicProvers.TOP_CASE_TAC \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ res_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[wordSemTheory.mem_store_byte_aux_def]
  \\ full_simp_tac(srw_ss())[wordSemTheory.mem_load_byte_aux_def]
  \\ Cases_on `m1 (byte_align a)` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ `byte_align a IN d` by full_simp_tac(srw_ss())[SUBSET_DEF] \\ full_simp_tac(srw_ss())[]
  \\ qpat_x_assum `xx ==> yy` mp_tac \\ impl_tac THEN1 (metis_tac [])
  \\ srw_tac[][]
  \\ `write_bytearray (a + 1w) new_bytes m1 d1 be (byte_align a) =
      write_bytearray (a + 1w) new_bytes m d be (byte_align a)` by
    (first_x_assum match_mp_tac \\ full_simp_tac(srw_ss())[] \\ res_tac \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[] \\ every_case_tac \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM] \\ srw_tac[][]
QED

Triviality write_bytearray_lemma:
  !new_bytes a m1 d1 be x p m d.
      (memory m1 d1 * p) (fun2set (m,d)) /\
      read_bytearray a (LENGTH new_bytes) (mem_load_byte_aux m1 d1 be) = SOME x ==>
      (memory (write_bytearray a new_bytes m1 d1 be) d1 * p)
        (fun2set (write_bytearray a new_bytes m d be,d))
Proof
  simp [STAR_def,set_sepTheory.SPLIT_EQ,memory_def]
  \\ full_simp_tac(srw_ss())[fun2set_def,SUBSET_DEF,PULL_EXISTS] \\ srw_tac[][]
  \\ `d1 SUBSET d` by full_simp_tac(srw_ss())[SUBSET_DEF]
  THEN1 (res_tac \\ full_simp_tac(srw_ss())[] \\ imp_res_tac write_bytearray_EQ \\ full_simp_tac(srw_ss())[])
  \\ qpat_x_assum `p xx` mp_tac
  \\ match_mp_tac (METIS_PROVE [] ``(x=y)==>x==>y``) \\ AP_TERM_TAC
  \\ full_simp_tac(srw_ss())[EXTENSION] \\ srw_tac[][] \\ EQ_TAC \\ srw_tac[][]
  \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ res_tac \\ full_simp_tac(srw_ss())[]
  \\ pop_assum mp_tac \\ full_simp_tac(srw_ss())[]
  \\ rename1 `xx IN d`
  \\ Cases_on `xx IN d1` \\ res_tac \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac write_bytearray_IGNORE \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac write_bytearray_EQ \\ rev_full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[] \\ metis_tac []
QED

Theorem state_rel_get_var_k:
   state_rel jump off k s t ⇒
   ∃c:α word.
   get_var (k+1) t = SOME (Word c) ∧
   dimindex (:α) DIV 8 * max_stack_alloc ≤ w2n c ∧
   w2n c + w2n (bytes_in_word:'a word) * LENGTH s.stack < dimword (:'a) ∧
   get_var k t = SOME (Word (c + bytes_in_word * n2w s.stack_space)) ∧
   (memory s.memory s.mdomain *
     word_list
       (the_SOME_Word (FLOOKUP s.store BitmapBase) ≪ word_shift (:α))
       (MAP Word s.bitmaps ++ MAP Word s.data_buffer.buffer) *
     word_list_exists
       (the_SOME_Word (FLOOKUP s.store BitmapBase) ≪ word_shift (:α) +
        bytes_in_word *
        n2w (LENGTH s.data_buffer.buffer + LENGTH s.bitmaps))
       s.data_buffer.space_left * word_store c s.store *
     word_list c s.stack) (fun2set (t.memory,t.mdomain))
Proof
  rw[state_rel_def]
  \\ pop_assum mp_tac
  \\ CASE_TAC \\ fs[]
  \\ CASE_TAC \\ fs[]
  \\ simp[get_var_def]
QED

Theorem evaluate_single_stack_alloc:
   state_rel jump off k s t1 ∧
   ((r,s2) = if s.stack_space < n
    then (SOME (Halt (Word 2w)),empty_env s)
    else (NONE, s with stack_space := s.stack_space - n)) ∧
   n ≠ 0 ∧ n ≤ max_stack_alloc
   ⇒
   ∃ck t2.
     evaluate (single_stack_alloc jump k n,t1 with clock := t1.clock + ck) = (r,t2) ∧
     if s.stack_space < n then t2.ffi = s2.ffi else state_rel jump off k s2 t2
Proof
  simp[single_stack_alloc_def] \\
  Cases_on`jump` \\
  simp [evaluate_def,inst_def,assign_def,word_exp_def,
       wordLangTheory.word_op_def,GSYM get_var_def]
  \\ strip_tac
  \\ imp_res_tac state_rel_get_var_k
  \\ simp[get_var_imm_def,get_var_def]
  \\ full_simp_tac(srw_ss())[get_var_def,set_var_def,FLOOKUP_UPDATE]
  \\ simp[]
  \\ simp[labSemTheory.word_cmp_def,asmTheory.word_cmp_def]
  \\ qpat_abbrev_tac`cc = c + _ + _`
  \\ `cc <+ c ⇔ s.stack_space < n`
  by (
    simp[Abbr`cc`,word_offset_def,bytes_in_word_def,word_mul_n2w,word_add_n2w]
    \\ Cases_on`c` \\ full_simp_tac(srw_ss())[]
    \\ qpat_abbrev_tac`d = _ DIV 8`
    \\ REWRITE_TAC[
         wordsLib.WORD_DECIDE ``w + -1w * v + t = w + t - v``,
         word_add_n2w]
    \\ REWRITE_TAC[addressTheory.word_arith_lemma2]
    \\ qmatch_assum_rename_tac`m < dimword _`
    \\ IF_CASES_TAC \\ simp_tac bool_ss []
    >- (
      `m < (n - s.stack_space) * d` by decide_tac
      \\ reverse (Cases_on `s.stack_space < n`)
      >- (
        `n - s.stack_space = 0` by decide_tac
        \\ `m < 0 * d` by metis_tac[] \\ full_simp_tac(srw_ss())[] )
      \\ simp[]
      \\ `m + d * s.stack_space ≤ d * n` by decide_tac
      \\ asm_simp_tac std_ss [n2w_sub]
      \\ REWRITE_TAC[WORD_NEG_SUB]
      \\ asm_simp_tac std_ss [GSYM n2w_sub]
      \\ REWRITE_TAC[GSYM word_add_n2w]
      \\ REWRITE_TAC[GSYM WORD_SUB_SUB]
      \\ `d * s.stack_space ≤ d * n` by decide_tac
      \\ asm_simp_tac std_ss [GSYM n2w_sub]
      \\ REWRITE_TAC[GSYM LEFT_SUB_DISTRIB]
      \\ ONCE_REWRITE_TAC[MULT_COMM]
      \\ qmatch_abbrev_tac`n2w m - n2w a <+ _`
      \\ `d ≠ 0` by ( strip_tac \\ full_simp_tac(srw_ss())[Abbr`d`,Abbr`a`] )
      \\ `0 < m` by (full_simp_tac(srw_ss())[max_stack_alloc_def,Abbr`d`] \\ decide_tac)
      \\ `d * max_stack_alloc < d * (n - s.stack_space)` by decide_tac
      \\ `max_stack_alloc < n - s.stack_space` by metis_tac[LT_MULT_LCANCEL]
      \\ decide_tac)
    \\ `(n - s.stack_space) * d ≤ m` by decide_tac
    \\ qmatch_assum_abbrev_tac`a * d ≤ m`
    \\ simp[WORD_LO]
    \\ Cases_on`s.stack_space < n`
    >- (
      `s.stack_space ≤ n` by decide_tac
      \\ `s.stack_space * d ≤ n * d` by metis_tac[LESS_MONO_MULT]
      \\ asm_simp_tac std_ss [GSYM SUB_SUB]
      \\ REWRITE_TAC[GSYM RIGHT_SUB_DISTRIB]
      \\ simp[]
      \\ `d ≠ 0` by (strip_tac \\ full_simp_tac(srw_ss())[Abbr`d`,state_rel_def,good_dimindex_def] \\ rev_full_simp_tac(srw_ss())[])
      \\ conj_asm1_tac >- simp[]
      \\ full_simp_tac(srw_ss())[max_stack_alloc_def]
      \\ simp[] )
    \\ simp[]
    \\ simp[NOT_LESS]
    \\ `n ≤ s.stack_space` by decide_tac
    \\ simp[]
    \\ `d * n ≤ d * s.stack_space` by metis_tac[LESS_MONO_MULT,MULT_COMM]
    \\ asm_simp_tac std_ss [LESS_EQ_ADD_SUB]
    \\ REWRITE_TAC[GSYM LEFT_SUB_DISTRIB]
    \\ `m + d * (s.stack_space - n) < dimword (:'a)` suffices_by (simp [])
    \\ full_simp_tac(srw_ss())[LEFT_SUB_DISTRIB]
    \\ full_simp_tac(srw_ss())[state_rel_def,bytes_in_word_def]
    \\ `d < dimword (:α)` by (UNABBREV_ALL_TAC
           \\ full_simp_tac(srw_ss())[good_dimindex_def,dimword_def]) \\ full_simp_tac(srw_ss())[]
    \\ qpat_x_assum `s.stack_space <= LENGTH s.stack` assume_tac
    \\ drule LESS_EQUAL_ADD \\ strip_tac \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[LEFT_ADD_DISTRIB] \\ decide_tac)
  \\ simp[]
  >- (* jump = true *)
    (BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    >- (
      srw_tac[][find_code_def]
      \\ qhdtm_x_assum`state_rel`mp_tac
      \\ simp[Once state_rel_def]
      \\ strip_tac
      \\ simp[halt_inst_def,evaluate_def,inst_def,assign_def,word_exp_def,set_var_def,dec_clock_def,get_var_def,FLOOKUP_UPDATE]
      \\ qexists_tac`1`
      \\ simp[] )
    \\ rveq
    \\ full_simp_tac(srw_ss())[state_rel_def]
    \\ simp[FLOOKUP_UPDATE]
    \\ conj_tac >- metis_tac[]
    \\ simp[Abbr`cc`]
    \\ simp[word_offset_def,bytes_in_word_def,word_mul_n2w,word_add_n2w]
    \\ ONCE_REWRITE_TAC[WORD_SUB_INTRO]
    \\ ONCE_REWRITE_TAC[GSYM WORD_ADD_SUB_SYM]
    \\ REWRITE_TAC[WORD_MULT_CLAUSES]
    \\ REWRITE_TAC[WORD_ADD_SUB_ASSOC]
    \\ dep_rewrite.DEP_REWRITE_TAC[GSYM n2w_sub]
    \\ simp[]
    \\ fs[bytes_in_word_def,word_mul_n2w]
    \\ metis_tac[])
  >> (* jump = false *)
    (BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    >- (simp[evaluate_def,halt_inst_def,inst_def,assign_def,word_exp_def]>>
      fs[state_rel_def])
    \\ rveq
    \\ full_simp_tac(srw_ss())[state_rel_def]
    \\ simp[FLOOKUP_UPDATE]
    \\ conj_tac >- metis_tac[]
    \\ simp[Abbr`cc`]
    \\ simp[word_offset_def,bytes_in_word_def,word_mul_n2w,word_add_n2w]
    \\ ONCE_REWRITE_TAC[WORD_SUB_INTRO]
    \\ ONCE_REWRITE_TAC[GSYM WORD_ADD_SUB_SYM]
    \\ REWRITE_TAC[WORD_MULT_CLAUSES]
    \\ REWRITE_TAC[WORD_ADD_SUB_ASSOC]
    \\ dep_rewrite.DEP_REWRITE_TAC[GSYM n2w_sub]
    \\ simp[]
    \\ fs[bytes_in_word_def,word_mul_n2w]
    \\ metis_tac[])
QED

Theorem evaluate_stack_alloc:
   ∀jump k n r s s2 t1.
   evaluate (StackAlloc n,s) = (r,s2) ∧ r ≠ SOME Error ∧
   state_rel jump off k s t1
   ⇒
   ∃ck t2.
     evaluate (stack_alloc jump k n,t1 with clock := ck + t1.clock) = (r,t2) ∧
     if ∀w. r ≠ SOME (Halt w) then state_rel jump off k s2 t2 else t2.ffi = s2.ffi
Proof
  ho_match_mp_tac stack_alloc_ind
  \\ srw_tac[][stackSemTheory.evaluate_def]
  \\ simp[Once stack_alloc_def]
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]
  >- (
    srw_tac[][evaluate_def]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[]
    \\ srw_tac[][] \\ full_simp_tac(srw_ss())[state_rel_def]
    \\ metis_tac[])
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]
  >- (
    drule evaluate_single_stack_alloc
    \\ impl_tac
    >- ( srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[state_rel_def] )
    \\ simp[]
    \\ strip_tac
    \\ asm_exists_tac
    \\ every_case_tac \\ full_simp_tac(srw_ss())[]
    \\ rveq \\ full_simp_tac(srw_ss())[])
  \\ simp[evaluate_def]
  \\ drule (GEN_ALL evaluate_single_stack_alloc)
  \\ disch_then(qspec_then`max_stack_alloc`mp_tac o CONV_RULE(RESORT_FORALL_CONV(sort_vars["n"])))
  \\ simp[]
  \\ `max_stack_alloc ≠ 0` by EVAL_TAC
  \\ simp[]
  \\ srw_tac[][]
  >- (
    qexists_tac`ck`\\simp[]
    \\ `s.stack_space < n` by decide_tac
    \\ full_simp_tac(srw_ss())[]
    \\ `s.use_stack` by full_simp_tac(srw_ss())[state_rel_def]
    \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] )
  \\ `s.use_stack` by full_simp_tac(srw_ss())[state_rel_def]
  \\ full_simp_tac(srw_ss())[]
  \\ qabbrev_tac`s' =
        if s.stack_space < n then empty_env (s with stack_space := s.stack_space - max_stack_alloc)
        else s with stack_space := s.stack_space - n`
  \\ `∃ck'. ∃t2'.
        evaluate (stack_alloc jump k (n - max_stack_alloc), t2 with clock := ck' + t2.clock) =
          (r,t2') ∧
        if ∀w. r ≠ SOME (Halt w) then
          state_rel jump off k s' t2'
       else t2'.ffi = s'.ffi`
  by (
    first_x_assum match_mp_tac
    \\ simp[]
    \\ ONCE_REWRITE_TAC[CONJ_COMM]
    \\ asm_exists_tac
    \\ simp[]
    \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[Abbr`s'`] )
  \\ qhdtm_x_assum`evaluate`mp_tac
  \\ drule (GEN_ALL evaluate_add_clock)
  \\ disch_then(qspec_then`ck'`mp_tac)
  \\ simp[] \\ ntac 2 strip_tac
  \\ qexists_tac`ck+ck'`\\simp[]
  \\ qhdtm_x_assum`COND`mp_tac
  \\ simp[Abbr`s'`]
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]
  \\ rveq \\ simp[]
QED

Theorem state_rel_mem_load_imp:
   state_rel jump off k s t ∧
   mem_load x s = SOME w ⇒
   mem_load x t = SOME w
Proof
  srw_tac[][state_rel_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[]
  \\ fs[mem_load_def]
  \\ drule fun2set_STAR_IMP \\ strip_tac
  \\ drule fun2set_STAR_IMP \\ strip_tac
  \\ drule fun2set_STAR_IMP \\ strip_tac
  \\ drule fun2set_STAR_IMP \\ strip_tac
  \\ full_simp_tac(srw_ss())[memory_def]
  \\ full_simp_tac(srw_ss())[fun2set_def,EXTENSION,PULL_EXISTS,EXISTS_PROD,FORALL_PROD]
  \\ metis_tac[]
QED

Theorem state_rel_word_exp:
   ∀s e w.
   state_rel jump off k s t ∧
   reg_bound_exp e k ∧
   word_exp s e = SOME w ⇒
   word_exp t e = SOME w
Proof
  ho_match_mp_tac word_exp_ind
  \\ rpt conj_tac
  \\ simp[word_exp_def]
  \\ rw[]
  \\ imp_res_tac state_rel_mem_load_imp
  \\ fs[state_rel_def]
  >-
    (qpat_x_assum`_ = SOME w`mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ rw[]>>fs[]>>
    res_tac \\ simp[])
  >- (
    full_simp_tac(srw_ss())[EVERY_MEM,MEM_MAP,PULL_EXISTS,IS_SOME_EXISTS]
    \\ metis_tac[] )
  >- (
    first_x_assum(CHANGED_TAC o SUBST1_TAC o GSYM)
    \\ AP_TERM_TAC
    \\ simp[MAP_EQ_f,MAP_MAP_o]
    \\ full_simp_tac(srw_ss())[EVERY_MEM,MEM_MAP,PULL_EXISTS,IS_SOME_EXISTS]
    \\ metis_tac[])
  >-
    (qpat_x_assum`_ = SOME w`mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[] \\
    res_tac \\ simp[])
QED

Theorem memory_write:
   x IN sd /\ x IN dm /\
  (memory sm sd * p) (fun2set (m,dm)) ==>
  (memory ((x =+ y) sm) sd * p) (fun2set ((x =+ y) m,dm))
Proof
  srw_tac[][STAR_def,memory_def]
  \\ qexists_tac`v` \\ simp[]
  \\ full_simp_tac(srw_ss())[SPLIT_def]
  \\ full_simp_tac(srw_ss())[EXTENSION,IN_DISJOINT,IN_fun2set,FORALL_PROD]
  \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
  \\ metis_tac[]
QED

Theorem state_rel_mem_store:
   state_rel jump off k s t ∧
   mem_store x y s = SOME s' ∧
   mem_store x y t = SOME t' ⇒
   state_rel jump off k s' t'
Proof
  fs[mem_store_def] \\ srw_tac[][]
  \\ fs[state_rel_def]
  \\ conj_tac >- metis_tac[]
  \\ conj_tac >- metis_tac[]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[GSYM STAR_ASSOC]
  \\ match_mp_tac memory_write
  \\ full_simp_tac(srw_ss())[]
QED

Theorem state_rel_mem_store_32:
   state_rel jump off k s t ∧ mem_store_32 s.memory s.mdomain s.be a b = SOME z ⇒
   ∃y. mem_store_32 t.memory t.mdomain t.be a b = SOME y ∧
       state_rel jump off k (s with memory := z) (t with memory := y)
Proof
  fs[state_rel_def,wordSemTheory.mem_store_32_def] >>
  rpt strip_tac
  \\ ntac 3 (pop_assum mp_tac)
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  \\ strip_tac
  \\ strip_tac
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  \\ strip_tac
  \\ fs[GSYM STAR_ASSOC]
  \\ drule (GEN_ALL memory_fun2set_IMP_read)
  \\ disch_then drule
  \\ strip_tac \\ simp[]
  \\ rveq
  \\ simp[CONJ_ASSOC]
  \\ (conj_tac >- metis_tac[])
  \\ match_mp_tac memory_write
  \\ simp[]
QED

Theorem state_rel_mem_store_byte_aux:
   state_rel jump off k s t ∧ mem_store_byte_aux s.memory s.mdomain s.be a b = SOME z ⇒
   ∃y. mem_store_byte_aux t.memory t.mdomain t.be a b = SOME y ∧
       state_rel jump off k (s with memory := z) (t with memory := y)
Proof
  rw[state_rel_def,wordSemTheory.mem_store_byte_aux_def]
  \\ ntac 2 (pop_assum mp_tac)
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  \\ strip_tac
  \\ BasicProvers.TOP_CASE_TAC \\ fs[]
  \\ strip_tac
  \\ fs[GSYM STAR_ASSOC]
  \\ drule (GEN_ALL memory_fun2set_IMP_read)
  \\ disch_then drule
  \\ strip_tac \\ simp[]
  \\ rveq
  \\ simp[CONJ_ASSOC]
  \\ conj_tac >- metis_tac[]
  \\ match_mp_tac memory_write
  \\ simp[]
QED

Triviality state_rel_get_fp_var:
  state_rel jump off k s t ⇒
  get_fp_var n s = get_fp_var n t
Proof
  fs[state_rel_def,get_fp_var_def]
QED

Triviality state_rel_set_fp_var:
  state_rel jump off k s t ⇒
  state_rel jump off k (set_fp_var n v s) (set_fp_var n v t)
Proof
  rw[state_rel_def,set_fp_var_def]>>rfs[]>>
  res_tac >> fs[]
QED

Theorem state_rel_inst:
   state_rel jump off k s t ∧
   reg_bound_inst i k ∧
   inst i s = SOME s'
   ⇒
   ∃t'.
     inst i t = SOME t' ∧
     state_rel jump off k s' t'
Proof
  simp[inst_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ full_simp_tac(srw_ss())[]
  \\ strip_tac
  \\ rveq \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[assign_def]
  >- (
    pop_assum mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ strip_tac
    \\ imp_res_tac state_rel_word_exp
    \\ first_x_assum(qspec_then`Const c`mp_tac)
    \\ simp_tac(srw_ss())[]
    \\ disch_then drule
    \\ simp_tac(srw_ss())[]
    \\ rveq \\ simp[])
  >- (
    reverse BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[] >>
    TRY
      (qmatch_goalsub_rename_tac`get_vars _ _`>>
      fs[get_vars_def]
      \\ every_case_tac \\ fs[]
      \\ imp_res_tac state_rel_get_var \\ fs[]
      \\ rw[] \\ fs[] )
    >- (
      drule state_rel_word_exp
      \\ qpat_x_assum`_ = SOME _`mp_tac
      \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
      \\ strip_tac
      \\ ONCE_REWRITE_TAC[CONJ_COMM]
      \\ disch_then drule
      \\ srw_tac[][] )
    \\ qpat_abbrev_tac`c ⇔ _ ∧ _`
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    >- (
      imp_res_tac state_rel_get_var
      \\ full_simp_tac(srw_ss())[get_var_def]
      \\ BasicProvers.CASE_TAC \\ full_simp_tac(srw_ss())[]
      \\ srw_tac[][] )
    \\ pop_assum mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ strip_tac
    \\ drule state_rel_word_exp
    \\ ONCE_REWRITE_TAC[CONJ_COMM]
    \\ disch_then drule
    \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ srw_tac[][] )
  >- (
     BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ pop_assum mp_tac
  \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ drule state_rel_word_exp
  \\ ONCE_REWRITE_TAC[CONJ_COMM]
  \\ disch_then drule
  \\ simp[]
  \\ imp_res_tac mem_load_byte_aux_IMP \\ fs[]
  \\ imp_res_tac mem_load_32_IMP \\ fs[]
  >> TRY (
    imp_res_tac state_rel_mem_load_imp
    \\ simp[] \\ srw_tac[][] \\ srw_tac[][] \\ NO_TAC)
  \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ TRY BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac state_rel_get_var
  \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  >- (
    qmatch_assum_rename_tac`mem_store x y s = SOME s'`>>
    `∃t'. mem_store x y t = SOME t'`
    by (
      fs[mem_store_def]
      \\ fs[state_rel_def]
      \\ every_case_tac \\ fs[]
      \\ fs[GSYM STAR_ASSOC]
      \\ drule (GEN_ALL memory_fun2set_IMP_read)
      \\ metis_tac[])
    \\ simp[]
    \\ imp_res_tac state_rel_mem_store)
  >- (drule (GEN_ALL state_rel_mem_store_byte_aux)
     \\ disch_then drule
     \\ strip_tac \\ simp[])
  \\ drule (GEN_ALL state_rel_mem_store_32)
  \\ disch_then drule
  \\ strip_tac \\ simp[])
  >>
    BasicProvers.TOP_CASE_TAC \\ fs[case_eq_thms] \\
    imp_res_tac state_rel_get_fp_var>>fs[]>>
    imp_res_tac state_rel_get_var >> fs[]>>
    rw[]>>fs[state_rel_set_var,state_rel_set_fp_var]>>
    rfs[]>>
    rw[]>>fs[state_rel_set_var,state_rel_set_fp_var]
QED

Theorem stack_write:
   ∀stack base p m d a v.
   (word_list base stack * p) (fun2set (m,d)) ∧ a < LENGTH stack ⇒
   (word_list base (LUPDATE v a stack) * p) (fun2set ((base + bytes_in_word * (n2w a) =+ v) m,d))
Proof
  Induct \\ simp[word_list_def] \\ srw_tac[][]
  \\ Cases_on`a`\\full_simp_tac(srw_ss())[LUPDATE_def]
  \\ full_simp_tac(srw_ss())[word_list_def] >- SEP_W_TAC
  \\ SEP_F_TAC
  \\ disch_then drule
  \\ simp[ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ srw_tac[star_ss][]
QED

Theorem state_rel_stack_store:
   state_rel jump off k s t ∧ st = s.stack ∧
   FLOOKUP t.regs k = SOME (Word b) ∧
   s.stack_space + n < LENGTH st ∧
   b + bytes_in_word * n2w n = a
   ⇒
   state_rel jump off k (s with stack := LUPDATE x (n + s.stack_space) st)
     (t with memory := (a =+ x) t.memory)
Proof
  simp[state_rel_def]
  \\ strip_tac
  \\ conj_tac >- metis_tac[]
  \\ conj_tac >- metis_tac[]
  \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ rveq
  \\ REWRITE_TAC[GSYM WORD_LEFT_ADD_DISTRIB,GSYM WORD_ADD_ASSOC,word_add_n2w]
  \\ REWRITE_TAC[Once STAR_COMM]
  \\ REWRITE_TAC[Once ADD_COMM]
  \\ match_mp_tac stack_write
  \\ fsrw_tac[star_ss][AC ADD_COMM ADD_ASSOC]
QED

Theorem lsl_word_shift:
   good_dimindex (:'a) ==>
    w ≪ word_shift (:α) = w * bytes_in_word:'a word
Proof
  srw_tac[][WORD_MUL_LSL,word_shift_def,bytes_in_word_def,
      good_dimindex_def]
QED

Triviality get_labels_stack_free:
  !k n. get_labels (stack_free k n) = {}
Proof
  recInduct stack_free_ind \\ rw []
  \\ once_rewrite_tac [stack_free_def] \\ rw []
  \\ fs [get_labels_def,single_stack_free_def]
QED

Triviality get_labels_stack_alloc:
  !jump k n. get_labels (stack_alloc jump k n) = {}
Proof
  recInduct stack_alloc_ind \\ rw []
  \\ once_rewrite_tac [stack_alloc_def] \\ rw []
  \\ fs [get_labels_def,single_stack_alloc_def]
  \\ IF_CASES_TAC \\ fs[get_labels_def,halt_inst_def]
QED

Triviality get_labels_upshift:
  !n n0. get_labels (upshift n n0) = {}
Proof
  recInduct upshift_ind \\ rw []
  \\ once_rewrite_tac [upshift_def] \\ rw []
  \\ fs [get_labels_def]
QED

Triviality get_labels_downshift:
  !n n0. get_labels (downshift n n0) = {}
Proof
  recInduct downshift_ind \\ rw []
  \\ once_rewrite_tac [downshift_def] \\ rw []
  \\ fs [get_labels_def]
QED

Theorem get_labels_comp:
   !jump off k e. get_labels (comp jump off k e) = get_labels e
Proof
  recInduct comp_ind \\ rw [] \\ Cases_on `p`
  \\ once_rewrite_tac [comp_def] \\ fs [get_labels_def,copy_loop_def,copy_each_def] \\ rw []
  \\ fs [get_labels_def,list_Seq_def]
  \\ every_case_tac
  \\ fs [get_labels_stack_alloc,get_labels_stack_free,stack_store_def,stack_load_def,get_labels_def]
  \\ metis_tac[get_labels_upshift,get_labels_downshift]
QED

Theorem code_rel_loc_check:
   code_rel jump off k c1 c2 /\ loc_check c1 (l1,l2) ==> loc_check c2 (l1,l2)
Proof
  fs [loc_check_def,code_rel_def,domain_lookup,PULL_EXISTS] \\ rw []
  \\ res_tac \\ fs [] \\ disj2_tac
  \\ asm_exists_tac \\ fs [get_labels_comp]
QED

Theorem evaluate_single_stack_free:
   state_rel jump off k s t1 ∧
   ((r,s2) = (NONE, s with stack_space := s.stack_space + n)) ∧
   ¬(LENGTH s.stack < s.stack_space + n) ∧
   n ≠ 0 ∧ n ≤ max_stack_alloc
   ⇒
   ∃ck t2.
     evaluate (single_stack_free k n,t1 with clock := t1.clock + ck) = (r,t2) ∧ state_rel jump off k s2 t2
Proof
  simp[single_stack_free_def,evaluate_def,inst_def,assign_def,word_exp_def,
       wordLangTheory.word_op_def,GSYM get_var_def]
  \\ strip_tac
  \\ imp_res_tac state_rel_get_var_k
  \\ simp[]
  \\ full_simp_tac(srw_ss())[get_var_def,set_var_def,FLOOKUP_UPDATE]
  \\ simp[]
  \\ simp[labSemTheory.word_cmp_def,asmTheory.word_cmp_def]
  \\ full_simp_tac(srw_ss())[state_rel_def]
  \\ simp[FLOOKUP_UPDATE]
  \\ rw[] >> TRY (metis_tac[])
  \\ simp[word_offset_def,bytes_in_word_def,word_mul_n2w,word_add_n2w]
  \\ simp[RIGHT_ADD_DISTRIB,GSYM word_add_n2w]
QED

Theorem evaluate_stack_free:
   ∀k n r s s2 t1.
   evaluate (StackFree n,s) = (r,s2) ∧ r ≠ SOME Error ∧
   state_rel jump off k s t1
   ⇒
   ∃ck t2.
     evaluate (stack_free k n,t1 with clock := ck + t1.clock) = (r,t2) ∧
     state_rel jump off k s2 t2
Proof
  ho_match_mp_tac stack_free_ind
  \\ srw_tac[][stackSemTheory.evaluate_def]
  \\ simp[Once stack_free_def]
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]
  >- (
    srw_tac[][evaluate_def]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[]
    \\ srw_tac[][] \\ full_simp_tac(srw_ss())[state_rel_def]
    \\ metis_tac[])
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]
  >- (
    every_case_tac>>fs[]>>
    drule evaluate_single_stack_free>> rw[])
  \\ simp[evaluate_def]
  \\ drule (GEN_ALL evaluate_single_stack_free)
  \\ disch_then(qspec_then`max_stack_alloc`mp_tac o CONV_RULE(RESORT_FORALL_CONV(sort_vars["n"])))
  \\ simp[]>>
  qpat_assum`A=(r,s2)` mp_tac>>
  IF_CASES_TAC>>fs[]>>
  qpat_assum`A=(r,s2)` mp_tac>>
  IF_CASES_TAC>>fs[]>>
  impl_keep_tac >- EVAL_TAC>>
  strip_tac>>
  qabbrev_tac`s' = s with stack_space := max_stack_alloc + s.stack_space`>>
  `∃ck'. ∃t2'. evaluate (stack_free k (n - max_stack_alloc), t2 with clock := ck' + t2.clock) = (r,t2') ∧ state_rel jump off k s2 t2'`
  by (
    first_x_assum match_mp_tac >>
    qexists_tac`s'` >> simp[Abbr`s'`]>>rw[])
  \\ qhdtm_x_assum`evaluate`mp_tac
  \\ drule (GEN_ALL evaluate_add_clock)
  \\ disch_then(qspec_then`ck'`mp_tac)
  \\ rveq \\ fs[]
  \\ ntac 2 strip_tac
  \\ qexists_tac`ck+ck'`\\simp[]
QED

Triviality evaluate_upshift:
  ∀r n st w.
  FLOOKUP st.regs r = SOME (Word w) ⇒
  evaluate(upshift r n,st) = (NONE, st with regs := st.regs |+ (r,Word (w + word_offset n)))
Proof
  ho_match_mp_tac upshift_ind>>rw[]>>
  simp[Once upshift_def]>>IF_CASES_TAC>>
  simp[evaluate_def,inst_def,assign_def,word_exp_def,wordLangTheory.word_op_def,set_var_def]>>
  qpat_abbrev_tac`st' = st with regs := _`>>fs[]>>
  first_x_assum(qspecl_then[`st'`,`w+word_offset max_stack_alloc`] mp_tac)>>
  fs[Abbr`st'`,set_var_def,FLOOKUP_UPDATE]>>rw[]>>
  simp[evaluate_def,inst_def,assign_def,word_exp_def,FLOOKUP_UPDATE,wordLangTheory.word_op_def,set_var_def]>>
  simp[state_component_equality,FUPD11_SAME_KEY_AND_BASE,word_offset_def]>>
  FULL_SIMP_TAC std_ss [Once (GSYM WORD_ADD_ASSOC),word_add_n2w]>>
  FULL_SIMP_TAC std_ss [GSYM RIGHT_ADD_DISTRIB]>>
  simp[]
QED

Triviality evaluate_downshift:
  ∀r n st w.
  FLOOKUP st.regs r = SOME (Word w) ⇒
  evaluate(downshift r n,st) = (NONE, st with regs := st.regs |+ (r,Word (w - word_offset n)))
Proof
  ho_match_mp_tac downshift_ind>>rw[]>>
  simp[Once downshift_def]>>IF_CASES_TAC>>
  simp[evaluate_def,inst_def,assign_def,word_exp_def,wordLangTheory.word_op_def,set_var_def]>>
  qpat_abbrev_tac`st' = st with regs := _`>>fs[]>>
  first_x_assum(qspecl_then[`st'`,`w - 1w * word_offset max_stack_alloc`] mp_tac)>>
  fs[Abbr`st'`,set_var_def,FLOOKUP_UPDATE]>>rw[]>>
  simp[evaluate_def,inst_def,assign_def,word_exp_def,FLOOKUP_UPDATE,wordLangTheory.word_op_def,set_var_def]>>
  simp[state_component_equality,FUPD11_SAME_KEY_AND_BASE,word_offset_def]>>
  FULL_SIMP_TAC std_ss [Once (GSYM WORD_ADD_ASSOC),word_add_n2w]>>
  simp[]>>
  FULL_SIMP_TAC std_ss [GSYM WORD_LEFT_ADD_DISTRIB]>>
  FULL_SIMP_TAC std_ss [Once (GSYM WORD_ADD_ASSOC),word_add_n2w]>>
  FULL_SIMP_TAC std_ss [GSYM RIGHT_ADD_DISTRIB]>>
  simp[]
QED

val name_cases = prove(
  ``!name. name <> CurrHeap ==> MEM name store_list``,
  Cases_on `name` \\ fs [store_list_def]
  \\ CCONTR_TAC \\ fs [] \\ Cases_on `c`
  \\ full_simp_tac std_ss [n2w_11,EVAL ``dimword (:5)``]
  \\ ntac 16 (Cases_on `n` \\ full_simp_tac std_ss [ADD1]
              \\ Cases_on `n'` \\ full_simp_tac std_ss [ADD1,GSYM ADD_ASSOC])
  \\ pop_assum mp_tac \\ rpt (pop_assum kall_tac) \\ decide_tac);

(* Significantly faster than SEP_R_TAC *)
Triviality mem_load_lemma:
  MEM name store_list ∧
  FLOOKUP (s:('a,'c,'b)stackSem$state).store name = SOME x ∧
  (memory s.memory s.mdomain *
        word_list
          (the_SOME_Word (FLOOKUP s.store BitmapBase) ≪ word_shift (:α))
          (MAP Word s.bitmaps ++ MAP Word s.data_buffer.buffer) *
        word_list_exists
          (the_SOME_Word (FLOOKUP s.store BitmapBase) ≪
           word_shift (:α) +
           bytes_in_word *
           n2w (LENGTH s.data_buffer.buffer + LENGTH s.bitmaps))
          s.data_buffer.space_left * word_store c s.store *
        word_list c s.stack) (fun2set (t1.memory,(t1:('a,'c,'b) stackSem$state).mdomain)) ⇒
  mem_load (c+store_offset name) t1 = SOME x
Proof
  strip_tac >>
  drule fun2set_STAR_IMP>>
  pop_assum kall_tac >> strip_tac >> pop_assum kall_tac >>
  drule fun2set_STAR_IMP>>
  simp[Once CONJ_COMM]>>
  pop_assum kall_tac >> strip_tac >>  pop_assum kall_tac>>
  ntac 2 (pop_assum mp_tac)>>
  simp[store_offset_def,store_pos_def,word_offset_def,word_offset_def,INDEX_FIND_def
    ,word_store_def,GSYM word_mul_n2w, store_list_def
    ,word_list_rev_def,bytes_in_word_def] \\ rfs[] \\
  strip_tac>>
  (* ntac 47 *) rpt (
  IF_CASES_TAC>>simp[Once one_fun2set]>>
  qmatch_abbrev_tac `P ∧ Q ∧ R ⇒ _`>>
  strip_tac
  >-
    simp[Abbr`P`,Abbr`Q`,mem_load_def]
  >>
  qpat_x_assum`P` kall_tac>> qpat_x_assum`Q` kall_tac>>
  qpat_x_assum`Abbrev (P ⇔ _)` kall_tac>>
  qpat_x_assum`Abbrev (Q ⇔ _)` kall_tac>>
  fs[Abbr`R`]>>
  pop_assum mp_tac)>>
  fs[store_list_def]
QED

(* basically the same thing, but without the read assumption *)
Triviality mem_load_lemma2:
  MEM name store_list ∧
  (memory s.memory s.mdomain *
        word_list
          (the_SOME_Word (FLOOKUP s.store BitmapBase) ≪ word_shift (:α))
          (MAP Word s.bitmaps ++ MAP Word s.data_buffer.buffer) *
        word_list_exists
          (the_SOME_Word (FLOOKUP s.store BitmapBase) ≪
           word_shift (:α) +
           bytes_in_word *
           n2w (LENGTH s.data_buffer.buffer + LENGTH s.bitmaps))
          s.data_buffer.space_left * word_store c s.store *
        word_list c s.stack) (fun2set (t1.memory,(t1:('a,'c,'b) stackSem$state).mdomain)) ⇒
  c+store_offset name ∈ t1.mdomain
Proof
  strip_tac >>
  drule fun2set_STAR_IMP>>
  pop_assum kall_tac >> strip_tac >> pop_assum kall_tac >>
  drule fun2set_STAR_IMP>>
  simp[Once CONJ_COMM]>>
  pop_assum kall_tac >> strip_tac >>  pop_assum kall_tac>>
  pop_assum mp_tac>>
  simp[store_offset_def,store_pos_def,word_offset_def,word_offset_def,INDEX_FIND_def
    ,word_store_def,GSYM word_mul_n2w, store_list_def
    ,word_list_rev_def,bytes_in_word_def] \\ rfs[] \\
  (* ntac 47 *) rpt (
  IF_CASES_TAC>>simp[Once one_fun2set]>>
  qmatch_abbrev_tac `P ∧ Q ∧ R ⇒ _`>>
  strip_tac>>
  qpat_x_assum`P` kall_tac>> qpat_x_assum`Q` kall_tac>>
  qpat_x_assum`Abbrev (P ⇔ _)` kall_tac>>
  qpat_x_assum`Abbrev (Q ⇔ _)` kall_tac>>
  fs[Abbr`R`]>>
  pop_assum mp_tac)>>
  fs[store_list_def]
QED

Triviality assoc_lem:
  (A:(('a -> bool) -> bool) * B) * C =
  (B * C) * A
Proof
  metis_tac[STAR_ASSOC,STAR_COMM]
QED

val write_fun2set2 = write_fun2set |> SIMP_RULE std_ss [GSYM STAR_COMM]

Triviality store_write_lemma:
  MEM name store_list ∧
  (memory s.memory s.mdomain *
        word_list
          (the_SOME_Word (FLOOKUP s.store BitmapBase) ≪ word_shift (:α))
          (MAP Word s.bitmaps ++ MAP Word s.data_buffer.buffer) *
        word_list_exists
          (the_SOME_Word (FLOOKUP s.store BitmapBase) ≪
           word_shift (:α) +
           bytes_in_word *
           n2w (LENGTH s.data_buffer.buffer + LENGTH s.bitmaps))
          s.data_buffer.space_left * word_store c s.store *
        word_list c s.stack) (fun2set (m,d)) ⇒
  (memory s.memory s.mdomain *
      word_list
        (the_SOME_Word (FLOOKUP s.store BitmapBase) ≪ word_shift (:α))
        (MAP Word s.bitmaps ++ MAP Word s.data_buffer.buffer) *
      word_list_exists
        (the_SOME_Word (FLOOKUP s.store BitmapBase) ≪ word_shift (:α) +
         bytes_in_word *
         n2w (LENGTH s.data_buffer.buffer + LENGTH s.bitmaps))
        s.data_buffer.space_left * word_store c (s.store |+ (name,x)) *
      word_list c s.stack) (fun2set ((c + store_offset name =+ x) m,d))
Proof
  strip_tac>>
  pop_assum mp_tac>>
  qmatch_goalsub_abbrev_tac`A * B * C`>>
  `A * B * C = B * (A * C)` by
    metis_tac[STAR_ASSOC,STAR_COMM]>>
  pop_assum SUBST_ALL_TAC>>
  qmatch_goalsub_abbrev_tac`A * B' * C`>>
  `A * B' * C = B' * (A * C)` by
    metis_tac[STAR_ASSOC,STAR_COMM]>>
  pop_assum SUBST_ALL_TAC>>
  qabbrev_tac`Z = (A*C)`>>
  fs[Abbr`B`,Abbr`B'`]>>
  simp[store_offset_def,store_pos_def,word_offset_def,word_offset_def,INDEX_FIND_def
      ,word_store_def,GSYM word_mul_n2w, store_list_def
      ,word_list_rev_def,bytes_in_word_def] \\ rfs[] \\
  simp[Once assoc_lem]>>strip_tac>>
  simp[Once assoc_lem]>>
  IF_CASES_TAC >> fs[]
  >-
    (rveq>>
    simp[FLOOKUP_UPDATE]>>
    match_mp_tac write_fun2set2>>
    qmatch_asmsub_abbrev_tac`(_* one(_,vv)) _`>>
    qexists_tac`vv`>>
    first_x_assum ACCEPT_TAC)
  >>
  (* ntac 42 *) rpt (
  qpat_x_assum` _ (fun2set _)` mp_tac>>
  simp[Once (GSYM STAR_ASSOC)]>>
  simp[Once assoc_lem]>>strip_tac>>
  simp[Once (GSYM STAR_ASSOC)]>>
  simp[Once assoc_lem]>>
  IF_CASES_TAC >> fs[]
  >-
    (rveq>>
    simp[FLOOKUP_UPDATE]>>
    match_mp_tac write_fun2set2>>
    qmatch_asmsub_abbrev_tac`(_* one(_,vv)) _`>>
    qexists_tac`vv`>>
    first_x_assum ACCEPT_TAC))>>
  fs[store_list_def]
QED

Theorem prog_comp_eta:
   prog_comp = \jump off k (n,p). (n,comp jump off k p)
Proof
  srw_tac[][FUN_EQ_THM,prog_comp_def,FORALL_PROD,LAMBDA_PROD]
QED

Theorem copy_each_thm:
  ∀pattern i a off bs d m dm i1 a1 m1 x (t:('a,'b,'c) stackSem$state).
    copy_words_for_pattern pattern i a off bs d m = SOME (i1,a1,m1) ∧
    ALL_DISTINCT [1;2;3;t1;t2] ∧ dm = t.mdomain ∧ good_dimindex (:'a) ∧
    get_var 1 t = SOME (Word pattern) ∧ d SUBSET dm ∧
    get_var 2 t = SOME (Word (a:'a word)) ∧
    get_var 3 t = SOME (Word off) ∧
    get_var t2 t = SOME (Word (x + bytes_in_word * n2w i)) ∧
    (word_list x (MAP Word bs) * rest * memory m d) (fun2set (t.memory,dm)) ⇒
    ∃ck y m2.
      evaluate (copy_each t1 t2, t with clock := t.clock + ck) =
        (NONE, t with <| memory := m2 ;
                         regs := ((if pattern = 1w then t.regs else t.regs |+ (t1,Word y))
                           |+ (2,Word a1) |+ (1,Word 1w)
                           |+ (t2, Word (x + bytes_in_word * n2w i1))) |>) ∧
      (word_list x (MAP Word bs) * rest * memory m1 d) (fun2set (m2,dm))
Proof
  ho_match_mp_tac copy_words_for_pattern_ind
  \\ rpt gen_tac \\ strip_tac
  \\ once_rewrite_tac [copy_words_for_pattern_def]
  \\ Cases_on ‘pattern = 1w’ \\ fs []
  THEN1
   (fs [copy_each_def]
    \\ once_rewrite_tac [evaluate_def]
    \\ fs [get_var_def,get_var_imm_def,asmTheory.word_cmp_def]
    \\ fs [state_component_equality]
    \\ rw [] \\ gvs []
    \\ fs [fmap_EXT,FLOOKUP_DEF,FAPPLY_FUPDATE_THM,EXTENSION]
    \\ rw [] \\ eq_tac \\ rw []\\ fs [])
  \\ rpt strip_tac \\ gvs []
  \\ simp [copy_each_def]
  \\ once_rewrite_tac [evaluate_def]
  \\ fs [get_var_def,get_var_imm_def,asmTheory.word_cmp_def]
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [evaluate_def,get_var_def,get_var_imm_def,asmTheory.word_cmp_def,inst_def,
         word_exp_def,get_var_def,wordLangTheory.word_op_def,mem_load_def]
  \\ drule miscTheory.LESS_LENGTH
  \\ strip_tac \\ gvs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ fs [word_list_def,word_list_APPEND]
  \\ SEP_R_TAC \\ gvs []
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [evaluate_def,get_var_def,get_var_imm_def,asmTheory.word_cmp_def,inst_def,
         word_exp_def,get_var_def,wordLangTheory.word_op_def,mem_load_def,assign_def,
         set_var_def,FLOOKUP_UPDATE]
  \\ once_rewrite_tac [list_Seq_def]
  \\ fs [evaluate_def,get_var_def,get_var_imm_def,asmTheory.word_cmp_def,inst_def,
         word_exp_def,get_var_def,wordLangTheory.word_op_def,mem_load_def,assign_def,
         set_var_def,FLOOKUP_UPDATE,labSemTheory.word_cmp_def]
  \\ qspec_then ‘pattern’ assume_tac (word_bit_test |> Q.INST [‘n’|->‘0’] |> GEN_ALL)
  \\ fs [word_bit_def]
  \\ Cases_on ‘1w && pattern = 0w’ \\ fs []
  \\ ‘32 ≤ dimindex (:'a)’ by fs [good_dimindex_def]
  \\ fs [SUBSET_DEF] \\ res_tac \\ fs []
  \\ fs [evaluate_def,get_var_def,get_var_imm_def,asmTheory.word_cmp_def,inst_def,
         word_exp_def,get_var_def,wordLangTheory.word_op_def,mem_load_def,assign_def,
         set_var_def,FLOOKUP_UPDATE,labSemTheory.word_cmp_def,list_Seq_def,
         wordLangTheory.word_sh_def,mem_store_def,dec_clock_def]
  \\ rewrite_tac [STOP_def]
  \\ fs [copy_each_def,list_Seq_def]
  \\ (fn x =>
        qexists_tac ‘1’ x
        |> fst |> hd |> snd |> find_term (can (match_term “stackSem$evaluate _”))
        |> rand |> rand |> (fn tm => qabbrev_tac ‘t8 = ^tm’ x))
  \\ fs [EL_LENGTH_APPEND]
  \\ last_x_assum (qspecl_then [‘x’,‘t8’] mp_tac)
  \\ (impl_tac
      THEN1
       (unabbrev_all_tac \\ fs [FLOOKUP_UPDATE]
        \\ gvs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
        \\ once_rewrite_tac [STAR_COMM]
        \\ irule memory_write \\ fs []
        \\ fs [AC STAR_ASSOC STAR_COMM])
      \\ strip_tac
      \\ unabbrev_all_tac \\ fs []
      \\ qexists_tac ‘ck + 1’
      \\ fs [state_component_equality]
      \\ rw []
      \\ fs [fmap_EXT,FLOOKUP_DEF,FAPPLY_FUPDATE_THM,EXTENSION]
      \\ rw [] \\ TRY eq_tac \\ rw []\\ fs []
      \\ TRY (qexists_tac ‘y’ \\ fs [] \\ rw [] \\ TRY eq_tac \\ rw []\\ fs [] \\ NO_TAC)
      \\ TRY (qexists_tac ‘y+off’ \\ fs [] \\ rw [] \\ TRY eq_tac \\ rw []\\ fs [] \\ NO_TAC)
      \\ TRY (qexists_tac ‘y'’ \\ fs [] \\ rw [] \\ TRY eq_tac \\ rw []\\ fs [] \\ NO_TAC))
QED

Theorem copy_loop_thm:
  ∀i a off bs d m dm i1 a1 m1 x (t:('a,'b,'c) stackSem$state).
    copy_words i a off bs d m = SOME (a1,m1) ∧
    ALL_DISTINCT [1;2;3;t1;t2] ∧ dm = t.mdomain ∧ good_dimindex (:'a) ∧
    d SUBSET dm ∧
    get_var 2 t = SOME (Word (a:'a word)) ∧
    get_var 3 t = SOME (Word off) ∧
    get_var t2 t = SOME (Word (x + bytes_in_word * n2w i)) ∧
    (word_list x (MAP Word bs) * rest * memory m d) (fun2set (t.memory,dm)) ⇒
    ∃ck b y y2 m2.
      evaluate (copy_loop t1 t2, t with clock := t.clock + ck) =
        (NONE, t with <| memory := m2 ;
                         regs := ((if b then t.regs else t.regs |+ (t1,Word y))
                           |+ (2,Word a1) |+ (1,Word 1w) |+ (t2,Word y2)) |>) ∧
      (word_list x (MAP Word bs) * rest * memory m1 d) (fun2set (m2,dm))
Proof
  ho_match_mp_tac copy_words_ind
  \\ rpt gen_tac \\ strip_tac
  \\ simp [Once copy_words_def]
  \\ Cases_on ‘copy_words_for_pattern (EL i bs) (i + 1) a off bs d m’
  \\ fs [] \\ PairCases_on ‘x’ \\ fs []
  \\ rpt strip_tac \\ gvs [wordsTheory.word_msb_neg]
  \\ simp [copy_loop_def]
  \\ simp [Once list_Seq_def]
  \\ simp [Once list_Seq_def]
  \\ ‘x' + bytes_in_word * n2w i ∈ t.mdomain ∧
      t.memory (x' + bytes_in_word * n2w i) = Word (EL i bs)’ by
   (fs [GSYM NOT_LESS] \\ drule LESS_LENGTH
    \\ strip_tac \\ gvs []
    \\ fs [word_list_def,word_list_APPEND] \\ SEP_R_TAC
    \\ simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ full_simp_tac(srw_ss())[EL_LENGTH_APPEND])
  \\ fs [evaluate_def,get_var_def,get_var_imm_def,asmTheory.word_cmp_def,inst_def,
         word_exp_def,get_var_def,wordLangTheory.word_op_def,mem_load_def,assign_def,
         set_var_def,FLOOKUP_UPDATE]
  \\ reverse (Cases_on ‘EL i bs < 0w’) \\ gvs []
  THEN1
   (simp [EVAL “list_Seq [_;_]”]
    \\ fs [evaluate_def,get_var_def,get_var_imm_def,asmTheory.word_cmp_def,inst_def,
           word_exp_def,get_var_def,wordLangTheory.word_op_def,mem_load_def,assign_def,
           set_var_def,FLOOKUP_UPDATE]
    \\ (fn x =>
        qexists_tac ‘0’ x
        |> fst |> hd |> snd |> find_term (can (match_term “stackSem$evaluate _”))
        |> rand |> rand |> (fn tm => qabbrev_tac ‘t8 = ^tm’ x))
    \\ drule copy_each_thm \\ fs []
    \\ disch_then (qspecl_then [‘x'’,‘t8’] mp_tac)
    \\ unabbrev_all_tac \\ fs [FLOOKUP_UPDATE,get_var_def]
    \\ impl_tac
    THEN1 (gvs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB])
    \\ strip_tac
    \\ qexists_tac ‘ck’
    \\ fs [] \\ gvs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
    \\ fs [state_component_equality]
    \\ qexists_tac ‘EL i bs = 1w’ \\ fs []
    \\ rw [] \\ fs []
    THEN1
     (qexists_tac ‘(x' + bytes_in_word * n2w x0)’
      \\ fs [fmap_EXT,FLOOKUP_DEF,FAPPLY_FUPDATE_THM,EXTENSION]
      \\ rw [] \\ TRY eq_tac \\ rw []\\ fs [])
    THEN1
     (qexists_tac ‘y’
      \\ qexists_tac ‘x' + bytes_in_word * n2w x0’
      \\ fs [fmap_EXT,FLOOKUP_DEF,FAPPLY_FUPDATE_THM,EXTENSION]
      \\ rw [] \\ TRY eq_tac \\ rw []\\ fs []))
  \\ simp [EVAL “list_Seq [_;_]”]
  \\ (fn x =>
        (qexists_tac ‘0’ \\ qexists_tac ‘ARB’ \\ qexists_tac ‘ARB’ \\ qexists_tac ‘ARB’) x
        |> fst |> hd |> snd |> find_term (can (match_term “stackSem$evaluate _”))
        |> rand |> rand |> (fn tm => qabbrev_tac ‘t8 = ^tm’ x))
  \\ fs [evaluate_def,get_var_def,get_var_imm_def,asmTheory.word_cmp_def,inst_def,
         word_exp_def,get_var_def,wordLangTheory.word_op_def,mem_load_def,assign_def,
         set_var_def,FLOOKUP_UPDATE]
  \\ qpat_abbrev_tac ‘ttt = STOP _’
  \\ simp [Once list_Seq_def]
  \\ drule copy_each_thm \\ fs []
  \\ disch_then (qspecl_then [‘x'’,‘t8’] mp_tac)
  \\ unabbrev_all_tac \\ fs [FLOOKUP_UPDATE,get_var_def]
  \\ impl_tac
  THEN1 (gvs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB])
  \\ strip_tac
  \\ ntac 2 (pop_assum mp_tac)
  \\ (fn x =>
        x |> snd |> dest_imp |> fst |> rand |> rand
          |> (fn tm => qabbrev_tac ‘t8 = ^tm’ x))
  \\ rw []
  \\ last_x_assum (qspecl_then [‘x'’,‘t8’] mp_tac)
  \\ impl_tac
  THEN1
   (unabbrev_all_tac \\ fs [FLOOKUP_UPDATE]
    \\ rw [] \\ fs [FLOOKUP_UPDATE])
  \\ rw []
  \\ unabbrev_all_tac \\ fs [FLOOKUP_UPDATE]
  \\ qpat_x_assum ‘evaluate (copy_each t1 t2,_) = _’ assume_tac
  \\ drule (evaluate_add_clock |> GEN_ALL) \\ fs []
  \\ disch_then (qspec_then ‘ck'+1’ assume_tac)
  \\ qexists_tac ‘ck+ck'+1’
  \\ fs [evaluate_def]
  \\ gvs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ ntac 2 (pop_assum kall_tac)
  \\ fs [list_Seq_def]
  \\ qpat_x_assum ‘evaluate (copy_loop t1 t2,_) = _’ mp_tac
  \\ rewrite_tac [copy_loop_def,list_Seq_def,STOP_def]
  \\ qpat_abbrev_tac ‘ttt = While _ _ _ _’
  \\ simp [evaluate_def,get_var_def,get_var_imm_def,asmTheory.word_cmp_def,inst_def,
         word_exp_def,get_var_def,wordLangTheory.word_op_def,mem_load_def,assign_def,
         set_var_def,FLOOKUP_UPDATE]
  \\ CASE_TAC \\ fs []
  \\ CASE_TAC \\ fs []
  \\ simp [evaluate_def,get_var_def,get_var_imm_def,asmTheory.word_cmp_def,inst_def,
         word_exp_def,get_var_def,wordLangTheory.word_op_def,mem_load_def,assign_def,
         set_var_def,FLOOKUP_UPDATE,dec_clock_def]
  \\ disch_then kall_tac
  \\ fs [state_component_equality]
  THEN1
   (qexists_tac ‘b’ \\ rw []
    THEN1
     (qexists_tac ‘y2’
      \\ fs [fmap_EXT,FLOOKUP_DEF,FAPPLY_FUPDATE_THM,EXTENSION]
      \\ rw [] \\ TRY eq_tac \\ rw []\\ fs [])
    THEN1
     (qexists_tac ‘y'’
      \\ qexists_tac ‘y2’
      \\ fs [fmap_EXT,FLOOKUP_DEF,FAPPLY_FUPDATE_THM,EXTENSION]
      \\ rw [] \\ TRY eq_tac \\ rw []\\ fs []))
  \\ Cases_on ‘b’ \\ fs []
  THEN1
   (qexists_tac ‘F’
    \\ qexists_tac ‘y’
    \\ qexists_tac ‘y2’
    \\ fs [fmap_EXT,FLOOKUP_DEF,FAPPLY_FUPDATE_THM,EXTENSION]
    \\ rw [] \\ TRY eq_tac \\ rw []\\ fs [])
  \\ qexists_tac ‘F’
  \\ qexists_tac ‘y'’
  \\ qexists_tac ‘y2’
  \\ fs [fmap_EXT,FLOOKUP_DEF,FAPPLY_FUPDATE_THM,EXTENSION]
  \\ rw [] \\ TRY eq_tac \\ rw []\\ fs []
QED

Theorem memory_fun2set_SUBSET:
  (memory m1 d1 * rest) (fun2set (m2,d2)) ⇒ d1 SUBSET d2
Proof
  fs [STAR_def,memory_def,fun2set_def] \\ fs [SPLIT_def]
  \\ rw [] \\ fs [EXTENSION,FORALL_PROD,SUBSET_DEF]
  \\ metis_tac []
QED

Theorem comp_correct[local]:
  !p s1 r s2 t1 k off jump.
     evaluate (p,s1) = (r,s2) /\ r <> SOME Error /\
     state_rel jump off k s1 t1 /\ reg_bound p k ==>
     ?ck t2. evaluate (comp jump off k p,t1 with clock := ck + t1.clock) = (r,t2) /\
             (case r of
              | SOME (Halt _) => t2.ffi = s2.ffi
              | SOME TimeOut => t2.ffi = s2.ffi
              | SOME (FinalFFI _) => t2.ffi = s2.ffi
              | _ =>  (state_rel jump off k s2 t2))
Proof
  recInduct evaluate_ind \\ rpt strip_tac
  THEN1 (* Skip *)
   (full_simp_tac(srw_ss())[comp_def,evaluate_def] \\ rpt var_eq_tac
    \\ qexists_tac`0` \\ full_simp_tac(srw_ss())[])
  THEN1 (* Halt *)
   (full_simp_tac(srw_ss())[comp_def,evaluate_def,reg_bound_def]
    \\ imp_res_tac state_rel_get_var \\ full_simp_tac(srw_ss())[]
    \\ qexists_tac`0`
    \\ BasicProvers.TOP_CASE_TAC \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[state_rel_def])
  THEN1 (* Alloc *)
   (fs [comp_def,evaluate_def] \\ fs [state_rel_def])
  THEN1 (* StoreConsts *)
   (fs [comp_def]
    \\ ‘¬s.use_alloc’ by fs [state_rel_def]
    \\ gvs [stackSemTheory.evaluate_def,list_Seq_def,AllCaseEqs()]
    \\ full_simp_tac(srw_ss())[reg_bound_def,GSYM NOT_LESS] \\ srw_tac[][]
    \\ `?ww. FLOOKUP s.store BitmapBase = SOME (Word ww)` by
     (full_simp_tac(srw_ss())[state_rel_def] \\ Cases_on `FLOOKUP s.store BitmapBase`
      \\ full_simp_tac(srw_ss())[is_SOME_Word_def] \\ Cases_on `x`
      \\ full_simp_tac(srw_ss())[is_SOME_Word_def])
    \\ `inst (Mem Load t2 (Addr (k + 1) (store_offset BitmapBase))) t1' =
          SOME (set_var t2 (Word ww) t1')` by
     (qpat_x_assum `state_rel jump off k s t1'` mp_tac
      \\ simp [Once state_rel_def] \\ full_simp_tac(srw_ss())[]
      \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
      \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[] \\ strip_tac
      \\ full_simp_tac(srw_ss())[wordLangTheory.word_op_def,stackSemTheory.inst_def,
             word_exp_def,LET_THM]
      \\ `mem_load (c + store_offset BitmapBase) t1' = SOME (Word ww)` by
        (match_mp_tac (GEN_ALL mem_load_lemma)>>fs[store_list_def]>>
          asm_exists_tac>> simp[])
      \\ simp[])
    \\ fs [] \\ pop_assum kall_tac
    \\ fs [inst_def,assign_def,word_exp_def,set_var_def,FLOOKUP_UPDATE]
    \\ gvs [store_const_sem_def,AllCaseEqs(),get_var_def]
    \\ ‘FLOOKUP t1'.regs 3 = SOME (Word off') ∧
        FLOOKUP t1'.regs 2 = SOME (Word a) ∧
        FLOOKUP t1'.regs 1 = SOME (Word i)’ by (rpt strip_tac \\ fs [state_rel_def])
    \\ ‘shift (:α) < dimindex (:α)’ by
       fs [state_rel_def,good_dimindex_def,backend_commonTheory.word_shift_def]
    \\ fs [wordLangTheory.word_sh_def,FLOOKUP_UPDATE,wordLangTheory.word_op_def]
    \\ qpat_x_assum ‘state_rel jump off k s _’ mp_tac
    \\ rename [‘state_rel jump off k s t6’]
    \\ simp [Once state_rel_def]
    \\ TOP_CASE_TAC \\ fs []
    \\ TOP_CASE_TAC \\ fs [the_SOME_Word_def]
    \\ strip_tac
    \\ qabbrev_tac ‘r2 = t6.regs |+ (t2,Word (i ≪ shift (:α) + ww ≪ shift (:α)))’
    \\ drule (GEN_ALL copy_loop_thm) \\ fs []
    \\ disch_then (qspecl_then [‘t2’,‘t1’] mp_tac) \\ fs []
    \\ fs [word_list_APPEND]
    \\ qpat_x_assum ‘_ (fun2set _)’ mp_tac
    \\ fs [GSYM STAR_ASSOC]
    \\ qmatch_goalsub_abbrev_tac ‘(_ * (_ * rest)) (fun2set _)’
    \\ fs [lsl_word_shift]
    \\ strip_tac
    \\ disch_then (qspecl_then [‘rest’,‘ww * bytes_in_word’,‘t6 with regs := r2’] mp_tac)
    \\ impl_tac THEN1
     (unabbrev_all_tac \\ fs [get_var_def,FLOOKUP_UPDATE]
      \\ gvs [lsl_word_shift]
      \\ imp_res_tac memory_fun2set_SUBSET
      \\ fs [AC STAR_COMM STAR_ASSOC])
    \\ strip_tac \\ qexists_tac ‘ck’ \\ gvs []
    \\ Cases_on ‘b’ \\ fs [FLOOKUP_UPDATE]
    \\ fs [state_rel_def,set_var_def,FLOOKUP_UPDATE,Abbr‘r2’,the_SOME_Word_def]
    \\ fs [word_list_APPEND]
    \\ gvs [lsl_word_shift,Abbr‘rest’,AC STAR_COMM STAR_ASSOC]
    \\ rw [] \\ res_tac \\ fs [])
  THEN1 (* Inst *)
   (full_simp_tac(srw_ss())[comp_def,evaluate_def]
    \\ last_x_assum mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ strip_tac \\ rveq
    \\ drule (GEN_ALL state_rel_inst)
    \\ full_simp_tac(srw_ss())[reg_bound_def]
    \\ disch_then drule
    \\ disch_then drule
    \\ strip_tac
    \\ simp[]
    \\ imp_res_tac inst_const
    \\ qexists_tac`0` \\ simp[]
    \\ metis_tac[with_same_clock])
  THEN1 (* Get *)
   (qexists_tac`0`
    \\ `s.use_store` by full_simp_tac(srw_ss())[state_rel_def]
    \\ full_simp_tac(srw_ss())[comp_def,evaluate_def,reg_bound_def]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[evaluate_def,inst_def,assign_def,word_exp_def,LET_DEF]
    THEN1 (`FLOOKUP t1.regs (k + 2) = SOME x` by full_simp_tac(srw_ss())[state_rel_def] \\ full_simp_tac(srw_ss())[])
    \\ qpat_x_assum `state_rel jump off k s t1` mp_tac
    \\ simp [Once state_rel_def] \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[] \\ strip_tac
    \\ full_simp_tac(srw_ss())[wordLangTheory.word_op_def]
    \\ `mem_load (c + store_offset name) t1 = SOME x` by
     (drule name_cases>>
     strip_tac>>
     metis_tac[mem_load_lemma])
    \\ fs[] \\ res_tac
    \\ fs[] \\ match_mp_tac state_rel_set_var
    \\ fs[state_rel_def]
    \\ metis_tac[])
  THEN1 (* Set *)
   (qexists_tac`0`
    \\ `s.use_store` by full_simp_tac(srw_ss())[state_rel_def]
    \\ full_simp_tac(srw_ss())[comp_def,evaluate_def,reg_bound_def]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[evaluate_def,inst_def,assign_def,word_exp_def,LET_DEF,get_var_def]
    THEN1 (
      fs[state_rel_def,set_var_def,set_store_def,FLOOKUP_UPDATE] \\
      rfs[] \\ fs[] \\ fs[word_store_def,word_store_CurrHeap] \\
      metis_tac[])
    \\ qpat_x_assum `state_rel jump off k s t1` mp_tac
    \\ simp [Once state_rel_def] \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[] \\ strip_tac
    \\ fs[wordLangTheory.word_op_def,mem_store_def]
    \\ `c + store_offset name IN t1.mdomain` by
     (drule name_cases>>
     strip_tac>>
     metis_tac[mem_load_lemma2])
    \\ fs[]
    \\ fs[state_rel_def,set_store_def,FLOOKUP_UPDATE]
    \\ rfs[]
    \\ conj_tac >- metis_tac[]
    \\ full_simp_tac(srw_ss())[AC MULT_COMM MULT_ASSOC]
    \\ Q.ABBREV_TAC `m = t1.memory`
    \\ Q.ABBREV_TAC `d = t1.mdomain`
    \\ drule name_cases
    \\ metis_tac[store_write_lemma])
  THEN1 (* OpCurrHeap *)
   (qexists_tac`0`
    \\ `s.use_store` by full_simp_tac(srw_ss())[state_rel_def]
    \\ full_simp_tac(srw_ss())[comp_def,evaluate_def,reg_bound_def]
    \\ gvs [AllCaseEqs(),word_exp_def]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ fs [inst_def,assign_def,word_exp_def]
    \\ gvs [AllCaseEqs(),word_exp_def,PULL_EXISTS]
    \\ rename [‘FLOOKUP s.regs src = SOME (Word c1)’]
    \\ rename [‘FLOOKUP s.store CurrHeap = SOME (Word c2)’]
    \\ qsuff_tac ‘FLOOKUP t1.regs src = SOME (Word c1) ∧
                  FLOOKUP t1.regs (k + 2) = SOME (Word c2)’ THEN1 fs []
    \\ fs [state_rel_def])
  THEN1 (* Tick *)
   (full_simp_tac(srw_ss())[comp_def,evaluate_def]
    \\ `s.clock = t1.clock` by full_simp_tac(srw_ss())[state_rel_def] \\ full_simp_tac(srw_ss())[]
    \\ qexists_tac`0` \\ full_simp_tac(srw_ss())[]
    \\ CASE_TAC \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ imp_res_tac state_rel_IMP \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[state_rel_def])
  THEN1 (* Seq *)
   (full_simp_tac(srw_ss())[] \\ simp [Once comp_def]
    \\ full_simp_tac(srw_ss())[evaluate_def,reg_bound_def,LET_DEF]
    \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
    \\ reverse(Cases_on `res = NONE`) \\ full_simp_tac(srw_ss())[]
    >- (rpt var_eq_tac
      \\ first_x_assum drule >> simp[]
      \\ strip_tac >> full_simp_tac(srw_ss())[]
      \\ pop_assum mp_tac >> CASE_TAC
      \\ rpt var_eq_tac >> full_simp_tac(srw_ss())[]
      \\ strip_tac
      \\ qexists_tac`ck`\\simp[])
    \\ first_x_assum drule >> simp[] >> strip_tac
    \\ first_x_assum drule \\ simp[] \\ strip_tac
    \\ ntac 2 (pop_assum mp_tac)
    \\ drule (GEN_ALL evaluate_add_clock)
    \\ disch_then(qspec_then`ck'`mp_tac)
    \\ simp[] \\ ntac 3 strip_tac
    \\ qexists_tac`ck+ck'`\\simp[])
  THEN1 (* Return *)
   (full_simp_tac(srw_ss())[comp_def,evaluate_def,reg_bound_def]
    \\ qexists_tac`0`
    \\ imp_res_tac state_rel_get_var \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[])
  THEN1 (* Raise *)
   (full_simp_tac(srw_ss())[comp_def,evaluate_def,reg_bound_def]
    \\ qexists_tac`0`
    \\ imp_res_tac state_rel_get_var \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[])
  THEN1 (* If *)
   (full_simp_tac(srw_ss())[] \\ simp [Once comp_def]
    \\ full_simp_tac(srw_ss())[evaluate_def,reg_bound_def]
    \\ imp_res_tac state_rel_get_var \\ full_simp_tac(srw_ss())[]
    \\ qpat_x_assum`_ = (r,_)`mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ strip_tac \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[]
    \\ first_x_assum drule \\ simp[] \\ strip_tac
    \\ qexists_tac`ck` \\ simp[]
    \\ full_simp_tac(srw_ss())[get_var_def]
    \\ Cases_on `ri` \\ full_simp_tac(srw_ss())[get_var_imm_def]
    \\ imp_res_tac state_rel_get_var \\ full_simp_tac(srw_ss())[])
  THEN1 (* While *)
   (qpat_x_assum `evaluate _ = _` mp_tac
    \\ simp [Once evaluate_def,get_var_def]
    \\ ntac 4 (BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[])
    \\ `get_var_imm ri s = get_var_imm ri t1 /\
        get_var r1 s = get_var r1 t1` by
     (Cases_on `ri` \\ full_simp_tac(srw_ss())[get_var_imm_def,reg_bound_def]
      \\ imp_res_tac state_rel_get_var \\ full_simp_tac(srw_ss())[get_var_def])
    \\ reverse (BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[])
    THEN1
     (strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
      \\ qexists_tac `0`
      \\ simp [Once comp_def,evaluate_def]
      \\ full_simp_tac(srw_ss())[reg_bound_def,get_var_def])
    \\ strip_tac \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
    \\ rev_full_simp_tac(srw_ss())[get_var_def] \\ full_simp_tac(srw_ss())[]
    \\ qpat_x_assum `SOME (Word _) = _` (assume_tac o GSYM) \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `res <> NONE` \\ full_simp_tac(srw_ss())[]
    THEN1
     (rpt var_eq_tac \\ full_simp_tac(srw_ss())[] \\ simp [Once comp_def]
      \\ full_simp_tac(srw_ss())[evaluate_def,get_var_def,LET_THM]
      \\ rev_full_simp_tac(srw_ss())[] \\ first_x_assum drule \\ full_simp_tac(srw_ss())[reg_bound_def]
      \\ strip_tac \\ full_simp_tac(srw_ss())[]
      \\ qexists_tac `ck` \\ full_simp_tac(srw_ss())[])
    \\ Cases_on `s1.clock = 0` \\ full_simp_tac(srw_ss())[]
    THEN1
     (rpt var_eq_tac \\ full_simp_tac(srw_ss())[] \\ simp [Once comp_def]
      \\ full_simp_tac(srw_ss())[evaluate_def,get_var_def,LET_THM]
      \\ rev_full_simp_tac(srw_ss())[] \\ first_x_assum drule \\ full_simp_tac(srw_ss())[reg_bound_def]
      \\ strip_tac \\ full_simp_tac(srw_ss())[]
      \\ qexists_tac `ck` \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[state_rel_def])
    \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[] \\ simp [Once comp_def]
    \\ full_simp_tac(srw_ss())[evaluate_def,get_var_def,LET_THM] \\ full_simp_tac(srw_ss())[STOP_def]
    \\ first_x_assum drule \\ full_simp_tac(srw_ss())[reg_bound_def]
    \\ strip_tac \\ rev_full_simp_tac(srw_ss())[]
    \\ rename1 `state_rel jump off k s3 t3`
    \\ `state_rel jump off k (dec_clock s3) (dec_clock t3)` by
        (fs[state_rel_def,dec_clock_def] \\ rev_full_simp_tac(srw_ss())[] \\ metis_tac[])
    \\ first_x_assum drule \\ full_simp_tac(srw_ss())[]
    \\ strip_tac \\ full_simp_tac(srw_ss())[] \\ ntac 2 (pop_assum mp_tac)
    \\ drule (GEN_ALL evaluate_add_clock) \\ full_simp_tac(srw_ss())[]
    \\ disch_then (qspec_then `ck'` assume_tac)
    \\ simp [Once comp_def] \\ rpt strip_tac \\ full_simp_tac(srw_ss())[]
    \\ qexists_tac `ck+ck'` \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC]
    \\ `t3.clock <> 0` by full_simp_tac(srw_ss())[state_rel_def] \\ full_simp_tac(srw_ss())[dec_clock_def]
    \\ `ck' + (t3.clock - 1) = ck' + t3.clock - 1` by decide_tac \\ full_simp_tac(srw_ss())[])
  THEN1 (* JumpLower *)
   (simp [Once comp_def]
    \\ full_simp_tac(srw_ss())[reg_bound_def,evaluate_def]
    \\ imp_res_tac state_rel_get_var \\ full_simp_tac(srw_ss())[find_code_def]
    \\ Cases_on `get_var r1 t1` \\ full_simp_tac(srw_ss())[] \\ Cases_on `x` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `get_var r2 t1` \\ full_simp_tac(srw_ss())[] \\ Cases_on `x` \\ full_simp_tac(srw_ss())[]
    \\ reverse (Cases_on `word_cmp Lower c c'`) \\ full_simp_tac(srw_ss())[] THEN1 (
      srw_tac[][] \\ qexists_tac`0`\\simp[])
    \\ Cases_on `lookup dest s.code` \\ full_simp_tac(srw_ss())[]
    \\ `lookup dest t1.code = SOME (comp jump off k x) /\
        reg_bound x k /\ s.clock = t1.clock` by
     (qpat_x_assum `bb ==> bbb` (K all_tac)
      \\ full_simp_tac(srw_ss())[state_rel_def,code_rel_def] \\ res_tac \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[])
    \\ full_simp_tac(srw_ss())[] \\ Cases_on `t1.clock = 0` \\ full_simp_tac(srw_ss())[]
    THEN1 (srw_tac[][] \\ qexists_tac`t1.clock` \\ full_simp_tac(srw_ss())[state_rel_def,code_rel_def])
    \\ split_pair_case_tac \\ fs[]
    \\ Cases_on `v` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
    \\ `state_rel jump off k (dec_clock s) (dec_clock t1)` by metis_tac [state_rel_IMP]
    \\ res_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ qexists_tac`ck`
    \\ fsrw_tac[ARITH_ss][get_var_def,dec_clock_def]
    \\ rev_full_simp_tac(srw_ss()++ARITH_ss)[])
  THEN1 (* RawCall *)
   (simp [Once comp_def]
    \\ fs [evaluate_def,CaseEq"option",PULL_EXISTS]
    \\ drule (GEN_ALL (find_code_lemma |> Q.INST [`dest`|->`INL d`]))
    \\ fs [find_code_def]
    \\ disch_then drule \\ strip_tac \\ fs []
    \\ Cases_on `prog` \\ fs [dest_Seq_def] \\ rveq \\ fs []
    \\ once_rewrite_tac [comp_def] \\ fs [dest_Seq_def]
    \\ `t1.clock = s.clock` by fs [state_rel_def]
    \\ fs [CaseEq"bool",pair_case_eq,CaseEq"option"] \\ rveq \\ fs []
    THEN1 (qexists_tac `0` \\ fs [] \\ fs [state_rel_def])
    \\ `state_rel jump off k (dec_clock s) (dec_clock t1)` by
          (fs [state_rel_def,dec_clock_def] \\ metis_tac [])
    \\ first_x_assum drule \\ fs [dec_clock_def]
    \\ disch_then match_mp_tac
    \\ pop_assum kall_tac
    \\ fs [state_rel_def]
    \\ res_tac \\ fs [reg_bound_def])
  THEN1 (* Call *)
   (Cases_on `ret` \\ full_simp_tac(srw_ss())[] THEN1
     (full_simp_tac(srw_ss())[evaluate_def]
      \\ Cases_on `find_code dest s.regs s.code` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `handler` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] THEN1
       (qexists_tac`0`
        \\ full_simp_tac(srw_ss())[evaluate_def,Once comp_def,reg_bound_def]
        \\ imp_res_tac find_code_lemma \\ full_simp_tac(srw_ss())[] \\ pop_assum (K all_tac)
        \\ full_simp_tac(srw_ss())[state_rel_def,code_rel_def])
      \\ Cases_on `evaluate (x,dec_clock s)` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `q` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
      \\ simp [evaluate_def,Once comp_def,reg_bound_def]
      \\ full_simp_tac(srw_ss())[reg_bound_def]
      \\ `find_code dest t1.regs t1.code = SOME (comp jump off k x) /\ reg_bound x k` by
           (match_mp_tac find_code_lemma \\ full_simp_tac(srw_ss())[]) \\ full_simp_tac(srw_ss())[]
      \\ `t1.clock <> 0` by full_simp_tac(srw_ss())[state_rel_def] \\ full_simp_tac(srw_ss())[]
      \\ `state_rel jump off k (dec_clock s) (dec_clock t1)` by
       (full_simp_tac(srw_ss())[state_rel_def,dec_clock_def] \\ rev_full_simp_tac(srw_ss())[] \\ metis_tac [])
      \\ first_x_assum drule \\ full_simp_tac(srw_ss())[]
      \\ strip_tac \\ full_simp_tac(srw_ss())[]
      \\ qexists_tac`ck`
      \\ rev_full_simp_tac(srw_ss()++ARITH_ss)[dec_clock_def])
    \\ PairCases_on `x` \\ full_simp_tac(srw_ss())[reg_bound_def]
    \\ simp[Once comp_def]
    \\ qhdtm_x_assum`evaluate`mp_tac
    \\ simp[Once evaluate_def]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ drule (GEN_ALL find_code_lemma2)
    \\ disch_then drule
    \\ disch_then drule
    \\ strip_tac
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    >- (
      strip_tac \\ rveq
      \\ simp[evaluate_def]
      \\ qexists_tac`0`\\simp[]
      \\ `t1.clock = 0` by fs[state_rel_def]
      \\ simp[] \\ fs[state_rel_def] )
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ simp[Once evaluate_def]
    \\ `t1.clock = s.clock` by fs[state_rel_def]
    \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ qmatch_assum_rename_tac`_ = (SOME res,_)`
    \\ Cases_on`res = TimeOut` \\ fs[]
    >- (
      strip_tac \\ rveq \\ fs[]
      \\ qmatch_asmsub_abbrev_tac`state_rel _ _ _ ss _`
      \\ (fn g => subterm (fn tm => (sg `state_rel jump off k ss (^tm with clock := s.clock - 1)`) g) (#2 g))
      >- (
        simp[Abbr`ss`,dec_clock_def]
        \\ match_mp_tac state_rel_with_clock
        \\ match_mp_tac state_rel_set_var
        \\ simp[] )
      \\ first_x_assum drule
      \\ simp[]
      \\ strip_tac
      \\ fs[dec_clock_def]
      \\ qexists_tac`ck'`\\simp[] )
    \\ Cases_on`∃w. res = Halt w` \\ fs[]
    >- (
      strip_tac \\ rveq \\ fs[]
      \\ qmatch_asmsub_abbrev_tac`state_rel _ _ _ ss _`
      \\ (fn g => subterm (fn tm => (sg `state_rel jump off k ss (^tm with clock := s.clock - 1)`) g) (#2 g))
      >- (
        simp[Abbr`ss`,dec_clock_def]
        \\ match_mp_tac state_rel_with_clock
        \\ match_mp_tac state_rel_set_var
        \\ simp[] )
      \\ first_x_assum drule
      \\ simp[]
      \\ strip_tac
      \\ fs[dec_clock_def]
      \\ qexists_tac`ck'`\\simp[] )
    \\ Cases_on`∃l. res = Result l` \\ fs[]
    >- (
      BasicProvers.TOP_CASE_TAC \\ fs[]
      \\ strip_tac \\ fs[] \\ rfs[]
      \\ qmatch_asmsub_abbrev_tac`state_rel _ _ _ (dec_clock sss) _`
      \\ qabbrev_tac`ss = dec_clock sss`
      \\ (fn g => subterm (fn tm => (sg `state_rel jump off k ss (^tm with clock := s.clock - 1)`) g) (#2 g))
      >- (
        simp[Abbr`ss`,dec_clock_def,Abbr`sss`]
        \\ match_mp_tac state_rel_with_clock
        \\ match_mp_tac state_rel_set_var
        \\ simp[] )
      \\ first_x_assum drule \\ simp[] \\ strip_tac
      \\ first_x_assum drule \\ simp[] \\ strip_tac
      \\ fs[dec_clock_def]
      \\ qhdtm_x_assum`evaluate`mp_tac
      \\ qmatch_goalsub_rename_tac`ck2 + t2.clock`
      \\ drule (GEN_ALL evaluate_add_clock)
      \\ disch_then(qspec_then`ck2`mp_tac)
      \\ simp[] \\ ntac 2 strip_tac
      \\ qexists_tac`ck' + ck2` \\  simp[] )
    \\ Cases_on`∃f. res = FinalFFI f` \\ fs[]
    >- (
      strip_tac \\ rveq \\ fs[]
      \\ qmatch_asmsub_abbrev_tac`state_rel _ _ _ ss _`
      \\ (fn g => subterm (fn tm => (sg `state_rel jump off k ss (^tm with clock := s.clock - 1)`) g) (#2 g))
      >- (
        simp[Abbr`ss`,dec_clock_def]
        \\ match_mp_tac state_rel_with_clock
        \\ match_mp_tac state_rel_set_var
        \\ simp[] )
      \\ first_x_assum drule
      \\ simp[]
      \\ strip_tac
      \\ fs[dec_clock_def]
      \\ qexists_tac`ck'`\\simp[] )
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    >- (
      strip_tac \\ rveq
      \\ qmatch_asmsub_abbrev_tac`state_rel _ _ _ ss _`
      \\ (fn g => subterm (fn tm => (sg `state_rel jump off k ss (^tm with clock := s.clock - 1)`) g) (#2 g))
      >- (
        simp[Abbr`ss`,dec_clock_def]
        \\ match_mp_tac state_rel_with_clock
        \\ match_mp_tac state_rel_set_var
        \\ simp[] )
      \\ first_x_assum drule
      \\ simp[]
      \\ strip_tac
      \\ fs[dec_clock_def]
      \\ qexists_tac`ck'`\\simp[] )
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ strip_tac \\ fs[] \\ rfs[]
    \\ qmatch_asmsub_abbrev_tac`state_rel _ _ _ (dec_clock sss) _`
    \\ qabbrev_tac`ss = dec_clock sss`
    \\ (fn g => subterm (fn tm => (sg `state_rel jump off k ss (^tm with clock := s.clock - 1)`) g) (#2 g))
    >- (
      simp[Abbr`ss`,dec_clock_def,Abbr`sss`]
      \\ match_mp_tac state_rel_with_clock
      \\ match_mp_tac state_rel_set_var
      \\ simp[] )
    \\ first_x_assum drule \\ simp[] \\ strip_tac
    \\ first_x_assum drule \\ simp[] \\ strip_tac
    \\ fs[dec_clock_def]
    \\ qhdtm_x_assum`evaluate`mp_tac
    \\ qmatch_goalsub_rename_tac`ck2 + t2.clock`
    \\ drule (GEN_ALL evaluate_add_clock)
    \\ disch_then(qspec_then`ck2`mp_tac)
    \\ simp[] \\ ntac 2 strip_tac
    \\ qexists_tac`ck' + ck2` \\  simp[] )
  THEN1 ( (* Install *)
    rw[comp_def]
    \\ fs[evaluate_def]
    \\ fs[reg_bound_def]
    \\ imp_res_tac state_rel_get_var
    \\ imp_res_tac state_rel_const
    \\ fs[get_var_def]
    \\ ntac 8 (TOP_CASE_TAC \\ fs[])
    \\ pairarg_tac \\ fs[]
    \\ pairarg_tac \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ qpat_x_assum`_ = (r,_)`mp_tac
    \\ TOP_CASE_TAC \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ rveq
    \\ TOP_CASE_TAC \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ rewrite_tac[GSYM MAP]
    \\ qmatch_goalsub_abbrev_tac`fromAList code`
    \\ simp[prog_comp_eta]
    \\ TOP_CASE_TAC \\ fs[]
    \\ simp[shift_seq_def]
    \\ TOP_CASE_TAC \\ fs[]
    \\ strip_tac \\ rveq \\ fs[]
    \\ qexists_tac`0`
    \\ fs[state_rel_def]
    \\ conj_tac >- (
      simp[FUN_EQ_THM,prog_comp_eta] )
    \\ conj_tac >- metis_tac[]
    \\ conj_tac >- (
      simp[FLOOKUP_UPDATE,FLOOKUP_DRESTRICT] )
    \\ conj_tac >- (
      qhdtm_x_assum`code_rel`mp_tac \\
      simp[code_rel_def,lookup_union,lookup_fromAList] \\
      strip_tac >>
      conj_tac>-(
        ntac 2 strip_tac \\
        reverse TOP_CASE_TAC >- (
          strip_tac  \\ rveq \\
          res_tac \\ simp[] ) \\
        strip_tac \\ imp_res_tac ALOOKUP_MEM \\
        simp[ALOOKUP_MAP_2] \\
        last_x_assum(qspec_then`0` mp_tac)>>simp[]>>
        disch_then drule>>strip_tac>>simp[]>>
        CASE_TAC>>fs[EXTENSION,domain_lookup,PULL_EXISTS]>>
        first_x_assum(qspec_then`n` assume_tac)>>rfs[]>>
        fs[backend_commonTheory.stack_num_stubs_def])>>
     simp[domain_union,domain_fromAList,MAP_MAP_o,o_DEF,UNCURRY,ETA_AX]>>
     metis_tac[UNION_COMM,UNION_ASSOC])
    \\ conj_tac >- simp[lookup_union]
    \\ conj_tac >- (
      simp[FLOOKUP_DRESTRICT,FLOOKUP_UPDATE] \\
      rfs[] )
    \\ conj_tac >- metis_tac[]
    \\ conj_tac >- (
      fs[wordSemTheory.buffer_flush_def]
      \\ rveq \\ fs[GSYM bytes_in_word_def,WORD_LEFT_ADD_DISTRIB,GSYM word_add_n2w] )
    \\ simp[FLOOKUP_DRESTRICT,FLOOKUP_UPDATE]
    \\ reverse IF_CASES_TAC >- metis_tac[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ conj_tac >- metis_tac[]
    \\ fs[wordSemTheory.buffer_flush_def]
    \\ rveq \\ fs[])
  THEN1 ( (* ShMemOp *)
    rw[comp_def]
    \\ fs[evaluate_def]
    \\ fs[reg_bound_def]
    \\ imp_res_tac state_rel_get_var
    \\ imp_res_tac state_rel_const
    \\ fs[get_var_def,word_exp_def,IS_SOME_EXISTS,
         wordLangTheory.word_op_def]>>
    ntac 2 (FULL_CASE_TAC>>fs[])
    \\ fs[CaseEq"bool"]
    >- (imp_res_tac state_rel_IMP>>
        gvs[empty_env_def,state_rel_def]>>
        TRY (qexists_tac`0`)>>gvs[])>>
    qexists_tac ‘0’>>gs[]>>
    imp_res_tac state_rel_IMP
    \\ Cases_on ‘op’
    \\ fs[sh_mem_op_def,sh_mem_load_def,sh_mem_store_def,
          sh_mem_load32_def,sh_mem_store32_def,
          sh_mem_load_byte_def,sh_mem_store_byte_def,get_var_def]
    \\ imp_res_tac state_rel_get_var >> fs[get_var_def]
    \\ ntac 2 (TOP_CASE_TAC>>fs[]) >>TRY (ntac 2 (CASE_TAC>>fs[]))>>
    rveq>>simp[]>>
    fs[state_rel_def,state_component_equality,FLOOKUP_UPDATE,dec_clock_def]>>rfs[]>>
    metis_tac[])
  THEN1 ( (* CodeBufferWrite *)
    rw[comp_def]
    \\ fs[evaluate_def]
    \\ fs[reg_bound_def]
    \\ imp_res_tac state_rel_get_var
    \\ imp_res_tac state_rel_const
    \\ fs[get_var_def]
    \\ ntac 5 (TOP_CASE_TAC \\ fs[])
    \\ rveq \\ fs[]
    \\ qexists_tac`0`
    \\ fs[state_rel_def]
    \\ metis_tac[])
  THEN1 ( (* DataBufferWrite *)
    rw[comp_def]
    \\ fs[reg_bound_def]
    \\ fs[evaluate_def]
    \\ fs[case_eq_thms] \\ rveq \\ fs[]
    \\ simp[PULL_EXISTS]
    \\ simp[inst_def,word_exp_def]
    \\ imp_res_tac state_rel_get_var
    \\ fs[get_var_def]
    \\ simp[wordLangTheory.word_op_def]
    \\ simp[case_eq_thms]
    \\ simp[mem_store_def]
    \\ qexists_tac`0`
    \\ qhdtm_x_assum`state_rel`mp_tac
    \\ simp[state_rel_def] \\ strip_tac
    \\ qhdtm_x_assum`option_CASE`mp_tac
    \\ TOP_CASE_TAC \\ simp[]
    \\ TOP_CASE_TAC \\ simp[]
    \\ strip_tac
    \\ first_x_assum(qspec_then`ARB`kall_tac)
    \\ fs[wordSemTheory.buffer_write_def]
    \\ rveq \\ fs[]
    \\ conj_tac
    >- (
      fs[word_list_APPEND,GSYM word_add_n2w] \\
      qmatch_asmsub_abbrev_tac`fun2set (m,dm)` \\
      Cases_on`s.data_buffer.space_left` \\ fs[word_list_exists_thm] \\
      fs[SEP_CLAUSES,SEP_EXISTS_THM] \\
      qmatch_asmsub_abbrev_tac`one (aa,_)` \\
      qmatch_abbrev_tac`bb ∈ dm` \\
      `aa = bb` by (
        simp[Abbr`aa`,Abbr`bb`,GSYM bytes_in_word_def] \\
        simp[WORD_LEFT_ADD_DISTRIB] ) \\
      rveq \\ SEP_R_TAC )
    \\ conj_tac >- metis_tac[]
    \\ fs[word_list_APPEND,word_list_def]
    \\ Cases_on`s.data_buffer.space_left` \\ fs[word_list_exists_thm] \\
    fs[SEP_CLAUSES,SEP_EXISTS_THM] \\
    qmatch_asmsub_abbrev_tac`fun2set (m,dm)` \\
    qmatch_goalsub_abbrev_tac`(aa =+ ww) m` \\
    qmatch_goalsub_abbrev_tac`one (bb,_)` \\
    `aa = bb` by (simp[Abbr`aa`,Abbr`bb`,GSYM bytes_in_word_def,WORD_LEFT_ADD_DISTRIB,GSYM word_add_n2w]) \\
    rveq \\
    SEP_W_TAC \\
    fs[GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB] \\
    fsrw_tac[star_ss][])
  THEN1 (* FFI *)
   (simp [Once comp_def]
    \\ qexists_tac`0`
    \\ full_simp_tac(srw_ss())[reg_bound_def,evaluate_def]
    \\ imp_res_tac state_rel_get_var \\ full_simp_tac(srw_ss())[]
    \\ qpat_x_assum `xxx = (r,s2)` mp_tac
    \\ rpt (BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[])
    \\ imp_res_tac read_bytearray_IMP_read_bytearray \\ full_simp_tac(srw_ss())[]
    \\ pop_assum kall_tac \\ srw_tac[][] \\ full_simp_tac(srw_ss())[LET_THM]
    \\ full_simp_tac(srw_ss())[]
    \\ `t1.ffi = s.ffi` by full_simp_tac(srw_ss())[state_rel_def] \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[markerTheory.Abbrev_def] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[state_rel_def,FLOOKUP_DRESTRICT]
    \\ rev_full_simp_tac(srw_ss())[] \\ CASE_TAC \\ full_simp_tac(srw_ss())[] \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ fs[GSYM STAR_ASSOC]
    \\ match_mp_tac write_bytearray_lemma \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac read_bytearray_LENGTH \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac call_FFI_LENGTH \\ full_simp_tac(srw_ss())[])
  THEN1 (* LocValue *)
   (full_simp_tac(srw_ss())[evaluate_def,Once comp_def] \\ srw_tac[][]
    \\ last_x_assum mp_tac \\ IF_CASES_TAC \\ rw[] \\ rw[]
    \\ reverse CASE_TAC
    THEN1 (fs [state_rel_def] \\ imp_res_tac code_rel_loc_check \\ fs [])
    \\ fs[state_rel_def,set_var_def,FLOOKUP_UPDATE,reg_bound_def]
    \\ `r <> k /\ r <> k+1 /\ r <> k+2` by decide_tac \\ full_simp_tac(srw_ss())[]
    \\ every_case_tac \\ rw[] \\ fs[] \\ res_tac \\ fs[] \\ rfs[])
  THEN1 (* StackAlloc *) (
    simp[comp_def]
    \\ drule evaluate_stack_alloc
    \\ simp[]
    \\ disch_then drule
    \\ strip_tac \\ simp[]
    \\ asm_exists_tac \\ simp[]
    \\ BasicProvers.CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[state_rel_def] )
  THEN1 (* StackFree *) (
    simp[comp_def]
    \\ drule evaluate_stack_free
    \\ simp[]
    \\ disch_then drule
    \\ strip_tac \\ simp[]
    \\ asm_exists_tac \\ simp[]
    \\ fs[evaluate_def]
    \\ every_case_tac \\ fs[])
  THEN1 (* StackLoad *) (
    simp[comp_def]
    \\ IF_CASES_TAC
    \\ qhdtm_x_assum`evaluate`mp_tac
    \\ simp[evaluate_def]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ strip_tac \\ rveq
    \\ simp[inst_def,assign_def,word_exp_def]
    \\ imp_res_tac state_rel_get_var_k
    \\ full_simp_tac(srw_ss())[get_var_def]
    \\ qexists_tac `0` \\ full_simp_tac(srw_ss())[]
    >-
      (simp[wordLangTheory.word_op_def]
      \\ simp[mem_load_def]
      \\ imp_res_tac LESS_LENGTH_IMP_APPEND
      \\ full_simp_tac(srw_ss())[word_list_APPEND,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
      \\ pop_assum (fn th => full_simp_tac(srw_ss())[GSYM th])
      \\ Cases_on `zs` \\ full_simp_tac(srw_ss())[word_list_def,word_offset_eq]
      \\ full_simp_tac(srw_ss())[EL_LENGTH_APPEND] \\ SEP_R_TAC \\ full_simp_tac(srw_ss())[]
      \\ `set_var r h t1 with clock := t1.clock = set_var r h t1` by full_simp_tac(srw_ss())[set_var_def]
      \\ full_simp_tac(srw_ss())[] \\ match_mp_tac state_rel_set_var
      \\ full_simp_tac(srw_ss())[reg_bound_def])
    >>
      fs[stack_load_def,evaluate_def]>>
      qpat_abbrev_tac`t = (set_var r _ _) with clock:= _`>>
      `FLOOKUP t.regs r = SOME(Word (c + bytes_in_word * n2w s.stack_space))` by
        fs[Abbr`t`,set_var_def,FLOOKUP_UPDATE]>>
      drule evaluate_upshift>>
      disch_then (qspec_then `n` assume_tac)>>
      simp[inst_def,assign_def,word_exp_def,FLOOKUP_UPDATE,wordLangTheory.word_op_def]>>fs[Abbr`t`,set_var_def]>>
      simp[mem_load_def]
      \\ fsrw_tac[ARITH_ss][NOT_LESS]
      \\ imp_res_tac LESS_LENGTH_IMP_APPEND
      \\ full_simp_tac(srw_ss())[word_list_APPEND,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
      \\ pop_assum (fn th => full_simp_tac(srw_ss())[GSYM th])
      \\ Cases_on `zs` \\ full_simp_tac(srw_ss())[word_list_def,word_offset_eq]
      \\ full_simp_tac(srw_ss())[EL_LENGTH_APPEND] \\ SEP_R_TAC \\ full_simp_tac(srw_ss())[]>>
      simp[GSYM set_var_def]>>
      match_mp_tac state_rel_set_var>>
      full_simp_tac(srw_ss())[reg_bound_def])
  THEN1 (* StackLoadAny *) (
    simp[comp_def]
    \\ qhdtm_x_assum`evaluate`mp_tac
    \\ simp[evaluate_def]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ strip_tac \\ rveq
    \\ simp[inst_def,assign_def,word_exp_def]
    \\ fs[reg_bound_def]
    \\ imp_res_tac state_rel_get_var
    \\ imp_res_tac state_rel_get_var_k
    \\ full_simp_tac(srw_ss())[get_var_def,set_var_def,FLOOKUP_UPDATE]
    \\ `r ≠ k` by fs[]
    \\ simp[wordLangTheory.word_op_def]
    \\ fs[FLOOKUP_UPDATE]
    \\ qexists_tac`0` \\ simp[]
    \\ simp[mem_load_def]
    \\ rpt(qpat_x_assum`∀x. _`kall_tac)
    \\ imp_res_tac LESS_LENGTH_IMP_APPEND
    \\ full_simp_tac(srw_ss())[word_list_APPEND]
    \\ Cases_on`zs` \\ full_simp_tac(srw_ss())[word_list_def]
    \\ full_simp_tac(srw_ss())[GSYM word_add_n2w]
    \\ full_simp_tac(srw_ss())[WORD_LEFT_ADD_DISTRIB]
    \\ pop_assum (fn th => full_simp_tac(srw_ss())[GSYM th,EL_LENGTH_APPEND])
    \\ `bytes_in_word * c >>> word_shift (:'a) = c` by
          rev_full_simp_tac(srw_ss())[lsl_word_shift,state_rel_def]
    \\ full_simp_tac(srw_ss())[] \\ SEP_R_TAC \\ full_simp_tac(srw_ss())[]
    \\ simp[GSYM set_var_def])
  THEN1 (* StackStore *) (
    simp[comp_def]
    \\ IF_CASES_TAC
    \\ qhdtm_x_assum`evaluate`mp_tac
    \\ simp[evaluate_def]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ strip_tac \\ rveq
    \\ qexists_tac`0` \\ simp[]
    \\ full_simp_tac(srw_ss())[reg_bound_def]
    \\ imp_res_tac state_rel_get_var
    \\ imp_res_tac state_rel_get_var_k
    >-
      (simp[inst_def]
      \\ full_simp_tac(srw_ss())[]
      \\ simp[word_exp_def]
      \\ full_simp_tac(srw_ss())[get_var_def]
      \\ simp[wordLangTheory.word_op_def]
      \\ simp[mem_store_def]
      \\ full_simp_tac(srw_ss())[NOT_LESS_EQUAL]
      \\ imp_res_tac LESS_LENGTH_IMP_APPEND
      \\ full_simp_tac(srw_ss())[word_list_APPEND]
      \\ Cases_on`zs`\\full_simp_tac(srw_ss())[word_list_def]
      \\ full_simp_tac(srw_ss())[word_offset_eq,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
      \\ SEP_R_TAC \\ full_simp_tac(srw_ss())[]
      \\ match_mp_tac (GEN_ALL state_rel_stack_store)
      \\ simp[])
    >>
      simp[stack_store_def,evaluate_def]>>
      fs[get_var_def]>>
      drule evaluate_upshift >> disch_then(qspec_then`n` assume_tac)>>
      simp[inst_def,word_exp_def,FLOOKUP_UPDATE,wordLangTheory.word_op_def]>>
      fs[get_var_def,FLOOKUP_UPDATE,set_var_def]>>
      simp[mem_store_def]>>
      full_simp_tac(srw_ss())[NOT_LESS_EQUAL]
      \\ simp[wordLangTheory.word_op_def]
      \\ simp[mem_store_def]
      \\ full_simp_tac(srw_ss())[NOT_LESS_EQUAL]
      \\ imp_res_tac LESS_LENGTH_IMP_APPEND
      \\ full_simp_tac(srw_ss())[word_list_APPEND]
      \\ Cases_on`zs`\\full_simp_tac(srw_ss())[word_list_def]
      \\ full_simp_tac(srw_ss())[word_offset_eq,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
      \\ SEP_R_TAC \\ full_simp_tac(srw_ss())[]
      \\ qpat_abbrev_tac`t' = t1 with <|regs:=_ ; memory := _|>`>>
      `FLOOKUP t'.regs k = SOME (Word (c + bytes_in_word * n2w n + bytes_in_word * n2w s.stack_space))` by
        fs[Abbr`t'`,FLOOKUP_UPDATE]>>
      drule evaluate_downshift>>disch_then(qspec_then`n` assume_tac)>>
      fs[word_offset_eq,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB,Abbr`t'`]>>
      qmatch_goalsub_abbrev_tac `t1 with <| regs:= R ; memory := M|>`>>
      `t1 with <|regs:=R;memory:=M|> = t1 with memory := M` by
        (simp[state_component_equality,Abbr`R`]>>
        match_mp_tac FUPDATE_ELIM>>
        qpat_x_assum`FLOOKUP _ k = SOME w` kall_tac>>
        qpat_x_assum`FLOOKUP _ k = SOME w` mp_tac>>
        simp[FDOM_FLOOKUP,Once FLOOKUP_DEF])>>
      simp[Abbr`M`]>>
      match_mp_tac (GEN_ALL state_rel_stack_store)>>
      simp[])
  THEN1 (* StackStoreAny *) (
    simp[comp_def]
    \\ qhdtm_x_assum`evaluate`mp_tac
    \\ simp[evaluate_def]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ strip_tac \\ rveq \\ full_simp_tac(srw_ss())[reg_bound_def]
    \\ qexists_tac`0`\\simp[]
    \\ simp[inst_def,assign_def,word_exp_def,GSYM get_var_def]
    \\ imp_res_tac state_rel_get_var_k \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac state_rel_get_var \\ full_simp_tac(srw_ss())[]
    \\ simp[wordLangTheory.word_op_def]
    \\ REWRITE_TAC[GSYM set_var_with_const]
    \\ REWRITE_TAC[with_same_clock]
    \\ simp[get_var_set_var]
    \\ pop_assum kall_tac
    \\ full_simp_tac(srw_ss())[NOT_LESS_EQUAL]
    \\ imp_res_tac LESS_LENGTH_IMP_APPEND
    \\ full_simp_tac(srw_ss())[word_list_APPEND]
    \\ Cases_on`zs` \\ full_simp_tac(srw_ss())[word_list_def]
    \\ `bytes_in_word * c >>> word_shift (:'a) = c` by
          rev_full_simp_tac(srw_ss())[lsl_word_shift,state_rel_def]
    \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[mem_store_def,WORD_LEFT_ADD_DISTRIB,GSYM word_add_n2w]
    \\ SEP_R_TAC \\ full_simp_tac(srw_ss())[set_var_def,get_var_def,FLOOKUP_UPDATE]
    \\ full_simp_tac(srw_ss())[DECIDE ``n<m:num ==> n<>m``]
    \\ pop_assum (fn th => full_simp_tac(srw_ss())[GSYM th,EL_LENGTH_APPEND] \\ mp_tac th)
    \\ pop_assum (fn th => full_simp_tac(srw_ss())[GSYM th,EL_LENGTH_APPEND] \\ mp_tac th)
    \\ strip_tac \\ strip_tac
    \\ full_simp_tac(srw_ss())[state_rel_def,FLOOKUP_UPDATE,DECIDE ``n<m:num ==> n<>m``]
    \\ rev_full_simp_tac(srw_ss())[ADD1,AC ADD_COMM ADD_ASSOC,word_list_def,word_list_APPEND]
    \\ fs[WORD_LEFT_ADD_DISTRIB,GSYM word_add_n2w]
    \\ CONJ_TAC >- metis_tac[]
    \\ qabbrev_tac `m = t1.memory`
    \\ qabbrev_tac `dm = t1.mdomain`
    \\ fs[word_list_APPEND]
    \\ SEP_WRITE_TAC)
  THEN1 (* StackGetSize *) (
    simp[comp_def]
    \\ qhdtm_x_assum`evaluate`mp_tac
    \\ simp[evaluate_def]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ strip_tac \\ rveq
    \\ simp[inst_def,assign_def,word_exp_def]
    \\ imp_res_tac state_rel_get_var_k
    \\ full_simp_tac(srw_ss())[get_var_def,set_var_def,FLOOKUP_UPDATE]
    \\ `r ≠ k+1` by fs[reg_bound_def]
    \\ simp[wordLangTheory.word_op_def]
    \\ qexists_tac`0` \\ simp[]
    \\ simp[Once set_var_def,FLOOKUP_UPDATE]
    \\ simp[wordLangTheory.word_sh_def]
    \\ IF_CASES_TAC \\ simp[]
    >- (
      full_simp_tac(srw_ss())[word_shift_def]
      \\ rev_full_simp_tac(srw_ss())[state_rel_def,good_dimindex_def]
      \\ rev_full_simp_tac(srw_ss())[] )
    \\ simp[]
    \\ ONCE_REWRITE_TAC[GSYM set_var_with_const]
    \\ REWRITE_TAC[with_same_clock]
    \\ dep_rewrite.DEP_REWRITE_TAC[bytes_in_word_word_shift]
    \\ qhdtm_x_assum`reg_bound`mp_tac \\simp[reg_bound_def]
    \\ strip_tac
    \\ qpat_x_assum`¬_`kall_tac
    \\ full_simp_tac(srw_ss())[state_rel_def,FLOOKUP_UPDATE]
    \\ `r ≠ k+2` by fs[] \\ rfs[]
    \\ `s.stack_space MOD dimword (:'a) ≤ LENGTH s.stack`
    by (
      `0 < dimword (:'a)` by simp[]
      \\ metis_tac[MOD_LESS_EQ,LESS_EQ_TRANS] )
    \\ reverse CONJ_TAC>- metis_tac[]
    \\ qmatch_assum_abbrev_tac`(a:num) + b * d < dw`
    \\ qmatch_abbrev_tac`d * f < dw`
    \\ `f ≤ s.stack_space ∧ f ≤ b` by
      (unabbrev_all_tac>>
      CONJ_ASM1_TAC>>fs[]>>
      match_mp_tac MOD_LESS_EQ>>
      fs[good_dimindex_def,dimword_def])
    \\ `d * f ≤ d * b ` by metis_tac[LESS_MONO_MULT,MULT_COMM]
    \\ decide_tac)
  THEN1 (* StackSetSize *) (
    simp[comp_def]
    \\ qhdtm_x_assum`evaluate`mp_tac
    \\ simp[evaluate_def]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ strip_tac \\ rveq
    \\ simp[inst_def,assign_def,word_exp_def]
    \\ full_simp_tac(srw_ss())[reg_bound_def]
    \\ imp_res_tac state_rel_get_var
    \\ imp_res_tac state_rel_get_var_k
    \\ full_simp_tac(srw_ss())[get_var_def]
    \\ simp[wordLangTheory.word_op_def]
    \\ qexists_tac`0` \\ simp[]
    \\ simp[Once set_var_def,FLOOKUP_UPDATE]
    \\ simp[wordLangTheory.word_sh_def]
    \\ IF_CASES_TAC \\ simp[]
    >- (
      full_simp_tac(srw_ss())[word_shift_def]
      \\ rev_full_simp_tac(srw_ss())[state_rel_def,good_dimindex_def]
      \\ rev_full_simp_tac(srw_ss())[])
    \\ ONCE_REWRITE_TAC[GSYM set_var_with_const]
    \\ ONCE_REWRITE_TAC[GSYM set_var_with_const]
    \\ REWRITE_TAC[with_same_clock]
    \\ simp [set_var_def,FLOOKUP_UPDATE]
    \\ pop_assum kall_tac
    \\ full_simp_tac(srw_ss())[state_rel_def]
    \\ simp[set_var_def,FLOOKUP_UPDATE]
    \\ rev_full_simp_tac(srw_ss())[lsl_word_shift]
    \\ fs[]
    \\ metis_tac[])
  THEN1 (* BitmapLoad *)
   (full_simp_tac(srw_ss())[stackSemTheory.evaluate_def] \\ every_case_tac
    \\ full_simp_tac(srw_ss())[reg_bound_def,GSYM NOT_LESS] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[comp_def,list_Seq_def,stackSemTheory.evaluate_def]
    \\ `?ww. FLOOKUP s.store BitmapBase = SOME (Word ww)` by
     (full_simp_tac(srw_ss())[state_rel_def] \\ Cases_on `FLOOKUP s.store BitmapBase`
      \\ full_simp_tac(srw_ss())[is_SOME_Word_def] \\ Cases_on `x` \\ full_simp_tac(srw_ss())[is_SOME_Word_def])
    \\ `inst (Mem Load r (Addr (k + 1) (store_offset BitmapBase))) t1 =
          SOME (set_var r (Word ww) t1)` by
     (qpat_x_assum `state_rel jump off k s t1` mp_tac
      \\ simp [Once state_rel_def] \\ full_simp_tac(srw_ss())[]
      \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
      \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[] \\ strip_tac
      \\ full_simp_tac(srw_ss())[wordLangTheory.word_op_def,stackSemTheory.inst_def,
             word_exp_def,LET_THM]
      \\ `mem_load (c' + store_offset BitmapBase) t1 = SOME (Word ww)` by
        (
          match_mp_tac (GEN_ALL mem_load_lemma)>>fs[store_list_def]>>
          asm_exists_tac>> simp[])
      \\ simp[])
    \\ qexists_tac`0`
    \\ full_simp_tac(srw_ss())[LET_THM,stackSemTheory.inst_def,stackSemTheory.assign_def,
           word_exp_def,set_var_def,FLOOKUP_UPDATE,get_var_def]
    \\ `FLOOKUP t1.regs v = SOME (Word c)` by metis_tac [state_rel_def] \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[wordLangTheory.word_op_def,FLOOKUP_UPDATE,
           wordLangTheory.word_sh_def]
    \\ `mem_load (c << word_shift (:'a) + ww << word_shift (:'a)) t1 =
        SOME (Word (EL (w2n c) s.bitmaps))` by
     (fs[state_rel_def] \\ ntac 2 (qpat_x_assum `xx = SOME yy` kall_tac)
      \\ every_case_tac \\ full_simp_tac(srw_ss())[good_dimindex_def,word_shift_def]
      \\ rev_full_simp_tac(srw_ss())[WORD_MUL_LSL, the_SOME_Word_def]
      \\ imp_res_tac LESS_LENGTH_IMP_APPEND \\ full_simp_tac(srw_ss())[word_list_APPEND]
      \\ rev_full_simp_tac(srw_ss())[bytes_in_word_def]
      \\ pop_assum (fn th => simp [GSYM th])
      \\ Cases_on `zs` \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[rich_listTheory.EL_LENGTH_APPEND,word_list_def]
      \\ full_simp_tac(srw_ss())[mem_load_def]  \\ SEP_R_TAC \\ full_simp_tac(srw_ss())[])
    \\ `good_dimindex(:'a)` by full_simp_tac(srw_ss())[state_rel_def]
    \\ full_simp_tac(srw_ss())[good_dimindex_def,word_shift_def,FLOOKUP_UPDATE]
    \\ full_simp_tac(srw_ss())[mem_load_def] \\ full_simp_tac(srw_ss())[GSYM mem_load_def] \\ full_simp_tac(srw_ss())[GSYM set_var_def])
QED

Theorem compile_semantics:
   state_rel jump off k s1 s2 /\ semantics start s1 <> Fail ==>
   semantics start s2 = semantics start s1
Proof
  simp[GSYM AND_IMP_INTRO] \\ strip_tac
  \\ simp[semantics_def]
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]
  \\ DEEP_INTRO_TAC some_intro \\ full_simp_tac(srw_ss())[]
  \\ conj_tac
  >- (
    gen_tac >> ntac 2 strip_tac >>
    IF_CASES_TAC >> full_simp_tac(srw_ss())[] >- (
      first_x_assum(qspec_then`k''`mp_tac)>>simp[]>>
      (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >>
      simp[] >>
      qmatch_assum_rename_tac`_ = (res,_)` >>
      Cases_on`res=SOME Error`>>simp[]>>
      drule comp_correct >>
      simp[reg_bound_def,RIGHT_FORALL_IMP_THM] >>
      drule (GEN_ALL state_rel_with_clock)
      \\ disch_then(qspec_then`k''`strip_assume_tac)
      \\ disch_then drule
      \\ simp[comp_def]
      \\ strip_tac \\ full_simp_tac(srw_ss())[]
      \\ qpat_x_assum`FST _ ≠ _`mp_tac
      \\ (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g)
      \\ drule (GEN_ALL evaluate_add_clock)
      \\ full_simp_tac(srw_ss())[]
      \\ disch_then(qspec_then`ck`mp_tac)
      \\ simp[]) >>
    DEEP_INTRO_TAC some_intro >> full_simp_tac(srw_ss())[] >>
    conj_tac >- (
      srw_tac[][] >>
      Cases_on`r=TimeOut`>>full_simp_tac(srw_ss())[] >>
      qhdtm_x_assum`evaluate`mp_tac >>
      drule (GEN_ALL evaluate_add_clock) >>
      disch_then(qspec_then`k''`mp_tac) >>
      simp[] >> strip_tac >>
      drule comp_correct >>
      simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
      impl_tac >- (
        rpt(first_x_assum(qspec_then`k'`mp_tac))>>srw_tac[][] ) >>
      simp[reg_bound_def,comp_def] >>
      drule (GEN_ALL state_rel_with_clock) >>
      disch_then(qspec_then`k'+k''`strip_assume_tac) >>
      disch_then drule >>
      strip_tac >> full_simp_tac(srw_ss())[] >>
      strip_tac >>
      qmatch_assum_abbrev_tac`evaluate (e,ss) = _` >>
      qspecl_then[`ck+k'`,`e`,`ss`]mp_tac(GEN_ALL evaluate_add_clock_io_events_mono)>>
      simp[Abbr`ss`] >> strip_tac >>
      drule (GEN_ALL evaluate_add_clock) >>
      disch_then(qspec_then`ck+k'`mp_tac) >>
      simp[] >> strip_tac >> fs[] >>
      first_x_assum(qspec_then`k''`mp_tac) >>
      simp[] >> strip_tac >> fs[state_rel_def]) >>
    drule comp_correct >>
    simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO,reg_bound_def] >>
    impl_tac >- (
      rpt(first_x_assum(qspec_then`k'`mp_tac))>>srw_tac[][]) >>
    simp[comp_def] >>
    drule (GEN_ALL state_rel_with_clock)
    \\ disch_then(qspec_then`k'`strip_assume_tac)
    \\ disch_then drule
    \\ simp[] \\ strip_tac
    \\ first_x_assum(qspec_then`ck+k'`mp_tac)
    \\ simp[]
    \\ pop_assum mp_tac
    \\ BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[]
    \\ TRY (strip_tac \\ qexists_tac `ck + k'` \\ fs [])
    \\ first_x_assum(qspec_then`k'`mp_tac) \\ fs []
    \\ simp[] >> strip_tac >> full_simp_tac(srw_ss())[]
    \\ strip_tac \\ qexists_tac `ck + k'` \\ fs [])
  \\ strip_tac
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]
  >- (
    full_simp_tac(srw_ss())[]
    \\ qpat_x_assum`_ ≠ _`mp_tac
    \\ (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g)
    \\ strip_tac \\ full_simp_tac(srw_ss())[]
    \\ last_x_assum(qspec_then`k'`mp_tac)
    \\ (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g)
    \\ drule comp_correct
    \\ qmatch_assum_rename_tac`_ = (res,_)`
    \\ Cases_on`res=SOME Error`\\ full_simp_tac(srw_ss())[]
    \\ drule (GEN_ALL state_rel_with_clock)
    \\ disch_then(qspec_then`k'`strip_assume_tac)
    \\ disch_then drule
    \\ simp[reg_bound_def,comp_def]
    \\ strip_tac
    \\ first_x_assum(qspec_then`k'`mp_tac)
    \\ simp[]
    \\ BasicProvers.FULL_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.FULL_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ ntac 2 (qhdtm_x_assum`evaluate`mp_tac)
    \\ drule (GEN_ALL evaluate_add_clock)
    \\ simp[] )
  \\ DEEP_INTRO_TAC some_intro \\ full_simp_tac(srw_ss())[]
  \\ conj_tac >- (
    srw_tac[][]
    \\ full_simp_tac(srw_ss())[METIS_PROVE[]``¬a ∨ b ⇔ a ⇒ b``]
    \\ full_simp_tac(srw_ss())[]
    \\ last_assum(qspec_then`k'`mp_tac)
    \\ (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g)
    \\ qpat_x_assum`∀x y. _`(fn th => assume_tac th >> qspec_then`k'`mp_tac th)
    \\ simp[]
    \\ drule comp_correct
    \\ qmatch_assum_rename_tac`_ = (res,_)`
    \\ Cases_on`res=SOME Error`\\ full_simp_tac(srw_ss())[]
    \\ drule (GEN_ALL state_rel_with_clock)
    \\ disch_then(qspec_then`k'`strip_assume_tac)
    \\ disch_then drule
    \\ simp[reg_bound_def,comp_def]
    \\ strip_tac
    \\ qpat_x_assum`∀k. _ ∨ _`(fn th => assume_tac th >> qspec_then`ck+k'`mp_tac th)
    \\ qhdtm_x_assum`evaluate`mp_tac
    \\ simp_tac(srw_ss())[]
    \\ strip_tac
    \\ qpat_x_assum`option_CASE _ _ _`mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ strip_tac
    \\ `t2.ffi = r'.ffi`
    by (
      pop_assum mp_tac
      \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[state_rel_def] )
    \\ full_simp_tac(srw_ss())[]
    \\ qmatch_assum_abbrev_tac`evaluate (e,ss) = (_,t)`
    \\ qspecl_then[`e`,`ss`](mp_tac o Q.GEN`extra`) evaluate_add_clock_io_events_mono
    \\ disch_then(qspec_then`ck`mp_tac)
    \\ simp[Abbr`ss`] \\ strip_tac
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.FULL_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac evaluate_add_clock \\ rev_full_simp_tac(srw_ss())[]
    \\ first_x_assum(qspec_then`ck`mp_tac)
    \\ simp[])
  \\ simp[]
  \\ strip_tac
  \\ qmatch_abbrev_tac`build_lprefix_lub l1 = build_lprefix_lub l2`
  \\ `(lprefix_chain l1 ∧ lprefix_chain l2) ∧ equiv_lprefix_chain l1 l2`
       suffices_by metis_tac[build_lprefix_lub_thm,lprefix_lub_new_chain,unique_lprefix_lub]
  \\ conj_asm1_tac >- (
    UNABBREV_ALL_TAC >>
    conj_tac >>
    Ho_Rewrite.ONCE_REWRITE_TAC[GSYM o_DEF] >>
    REWRITE_TAC[IMAGE_COMPOSE] >>
    match_mp_tac prefix_chain_lprefix_chain >>
    simp[prefix_chain_def,PULL_EXISTS] >>
    qx_genl_tac[`k1`,`k2`] >>
    qspecl_then[`k1`,`k2`]mp_tac LESS_EQ_CASES >>
    metis_tac[
      LESS_EQ_EXISTS,
      evaluate_add_clock_io_events_mono
        |> CONV_RULE(SWAP_FORALL_CONV)
        |> Q.SPEC`s with <| use_alloc := F; clock := k; code := c|>`
        |> SIMP_RULE(srw_ss())[],
      evaluate_add_clock_io_events_mono
        |> CONV_RULE(SWAP_FORALL_CONV)
        |> Q.SPEC`s with <| clock := k |>`
        |> SIMP_RULE(srw_ss())[]]) >>
  simp[equiv_lprefix_chain_thm] >>
  unabbrev_all_tac >> simp[PULL_EXISTS] >>
  ntac 2 (pop_assum kall_tac) >>
  simp[LNTH_fromList,PULL_EXISTS] >>
  simp[GSYM FORALL_AND_THM] >>
  rpt gen_tac >>
  (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) >> full_simp_tac(srw_ss())[] >>
  (fn g => subterm (fn tm => Cases_on`^(assert (fn tm => has_pair_type tm andalso free_in tm (#2 g)) tm)`) (#2 g) g) >> full_simp_tac(srw_ss())[] >>
  drule comp_correct >>
  simp[comp_def,reg_bound_def,RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
  impl_tac >- (
    rpt(first_x_assum(qspec_then`k'`mp_tac))>>srw_tac[][] ) >>
  drule (GEN_ALL state_rel_with_clock) >>
  disch_then(qspec_then`k'`strip_assume_tac) >>
  disch_then drule >>
  strip_tac >> full_simp_tac(srw_ss())[] >>
  `t2.ffi = r'.ffi` by (
    pop_assum mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ TRY BasicProvers.TOP_CASE_TAC \\ full_simp_tac(srw_ss())[]
    \\ simp[state_rel_def] ) >>
  reverse conj_tac >- (
    srw_tac[][] >>
    qexists_tac`ck+k'`>>simp[] ) >>
  srw_tac[][] >>
  qexists_tac`k'`>>simp[] >>
  ntac 2 (qhdtm_x_assum`evaluate`mp_tac) >>
  qmatch_assum_abbrev_tac`evaluate (e,ss) = _` >>
  qspecl_then[`ck`,`e`,`ss`]mp_tac(GEN_ALL evaluate_add_clock_io_events_mono)>>
  simp[Abbr`ss`] >>
  ntac 3 strip_tac >> full_simp_tac(srw_ss())[] >>
  rev_full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[IS_PREFIX_APPEND] >>
  simp[EL_APPEND1]
QED

(* init code *)

val tac = simp [list_Seq_def,evaluate_def,inst_def,word_exp_def,get_var_def,
       wordLangTheory.word_op_def,mem_load_def,assign_def,set_var_def,
       FLOOKUP_UPDATE,mem_store_def,dec_clock_def,get_var_imm_def,
       asmTheory.word_cmp_def,
       labSemTheory.word_cmp_def,GREATER_EQ,GSYM NOT_LESS,FUPDATE_LIST,
       wordLangTheory.word_sh_def,halt_inst_def]

val tac1 = simp [Once list_Seq_def,evaluate_def,inst_def,word_exp_def,get_var_def,
       wordLangTheory.word_op_def,mem_load_def,assign_def,set_var_def,
       FLOOKUP_UPDATE,mem_store_def,dec_clock_def,get_var_imm_def,
       asmTheory.word_cmp_def,
       labSemTheory.word_cmp_def,GREATER_EQ,GSYM NOT_LESS,FUPDATE_LIST,
       wordLangTheory.word_sh_def,halt_inst_def]

Definition mem_val_def:
  (mem_val regs (INL w) = Word w) /\
  (mem_val (regs:num |-> 'a word_loc) (INR n) = regs ' n)
End

Theorem store_list_code_thm:
   !xs s w frame ys m dm.
      (word_list w ys * frame) (fun2set (m,dm)) /\
      m = s.memory /\ dm = s.mdomain /\
      (LENGTH ys = LENGTH xs) /\ a <> t /\
      get_var a s = SOME (Word w) /\ t IN FDOM s.regs /\
      EVERY (\x. !n. (INR n = x) ==> n <> a /\ n <> t /\ n IN FDOM s.regs) xs ==>
      ?r1 m1.
        (word_list w (MAP (mem_val s.regs) xs) * frame) (fun2set (m1,s.mdomain)) /\
        evaluate (store_list_code a t xs,s) =
          (NONE,s with <| memory := m1;
                          regs := s.regs |++
            [(a,Word (w + bytes_in_word * n2w (LENGTH xs)));(t,r1)] |>)
Proof
  simp_tac std_ss []
  \\ Induct \\ fs [] THEN1
   (fs [word_list_def,SEP_CLAUSES,store_list_code_def,LENGTH_NIL]
    \\ tac
    \\ fs [finite_mapTheory.fmap_EXT,state_component_equality]
    \\ rw [] \\ qexists_tac `s.regs ' t`
    \\ fs [EXTENSION,FAPPLY_FUPDATE_THM,FLOOKUP_DEF]
    \\ metis_tac [])
  \\ Cases_on `ys` \\ Cases \\ fs [mem_val_def]
  \\ fs [word_list_def,SEP_CLAUSES,store_list_code_def,LENGTH_NIL]
  THEN1
   (tac \\ fs [store_list_code_def]
    \\ rpt strip_tac
    \\ SEP_R_TAC \\ fs []
    \\ fs [FLOOKUP_UPDATE]
    \\ qabbrev_tac `m = s.memory`
    \\ qabbrev_tac `dm = s.mdomain`
    \\ SEP_W_TAC
    \\ pop_assum mp_tac
    \\ once_rewrite_tac [GSYM STAR_ASSOC]
    \\ once_rewrite_tac [STAR_COMM]
    \\ once_rewrite_tac [GSYM STAR_ASSOC]
    \\ qpat_abbrev_tac `s4 = s with <| regs := _; memory := _ |>`
    \\ first_x_assum (qspec_then `s4` mp_tac)
    \\ unabbrev_all_tac \\ fs []
    \\ rpt strip_tac \\ first_x_assum drule
    \\ impl_tac
    THEN1 (fs [get_var_def,FLOOKUP_UPDATE,EVERY_MEM])
    \\ strip_tac
    \\ fs [state_component_equality,ADD1,GSYM word_add_n2w,
           WORD_LEFT_ADD_DISTRIB]
    \\ qexists_tac `r1` \\ fs []
    \\ `MAP (mem_val (s.regs |+ (t,Word x) |+ (a,Word (w + bytes_in_word)))) xs =
        MAP (mem_val s.regs) xs` by
     (fs [MAP_EQ_f,EVERY_MEM]
      \\ Cases \\ fs [mem_val_def]
      \\ rw [] \\ res_tac \\ fs [FAPPLY_FUPDATE_THM])
    \\ fs []
    \\ fs [finite_mapTheory.fmap_EXT,state_component_equality,
           FAPPLY_FUPDATE_THM,FUPDATE_LIST,EXTENSION]
    \\ metis_tac [])
  THEN1
   (tac \\ fs [store_list_code_def]
    \\ rpt strip_tac \\ SEP_R_TAC \\ fs []
    \\ fs [FLOOKUP_UPDATE]
    \\ fs [FLOOKUP_DEF]
    \\ qabbrev_tac `m = s.memory`
    \\ qabbrev_tac `dm = s.mdomain`
    \\ SEP_W_TAC
    \\ pop_assum mp_tac
    \\ once_rewrite_tac [GSYM STAR_ASSOC]
    \\ once_rewrite_tac [STAR_COMM]
    \\ once_rewrite_tac [GSYM STAR_ASSOC]
    \\ qpat_abbrev_tac `s4 = s with <| regs := _; memory := _ |>`
    \\ first_x_assum (qspec_then `s4` mp_tac)
    \\ unabbrev_all_tac \\ fs []
    \\ rpt strip_tac \\ first_x_assum drule
    \\ impl_tac
    THEN1 (fs [get_var_def,FLOOKUP_UPDATE,EVERY_MEM])
    \\ strip_tac
    \\ fs [state_component_equality,ADD1,GSYM word_add_n2w,
           WORD_LEFT_ADD_DISTRIB]
    \\ qexists_tac `r1` \\ fs []
    \\ `MAP (mem_val (s.regs |+ (a,Word (w + bytes_in_word)))) xs =
        MAP (mem_val s.regs) xs` by
     (fs [MAP_EQ_f,EVERY_MEM]
      \\ Cases \\ fs [mem_val_def]
      \\ rw [] \\ res_tac \\ fs [FAPPLY_FUPDATE_THM])
    \\ fs []
    \\ fs [finite_mapTheory.fmap_EXT,state_component_equality,
           FAPPLY_FUPDATE_THM,FUPDATE_LIST,EXTENSION])
QED

val halt_tac =
  tac \\ fs [good_dimindex_def]
  \\ rw [] \\ fs [dimword_def]

Triviality MOD_EQ_IMP_MULT:
  !n d. n MOD d = 0 /\ d <> 0 ==> ?k. n = d * k
Proof
  rw [] \\ fs [MOD_EQ_0_DIVISOR] \\ metis_tac []
QED

Triviality star_move_lemma:
  p0 * p1 * p1' * p2 * p3 * p4 = p2 * (p1 * p1' * STAR p3 (p4 * p0))
Proof
  fs [AC STAR_COMM STAR_ASSOC]
QED

Definition read_mem_def:
  (read_mem a m 0 = []) /\
  (read_mem a m (SUC n) =
     m a :: read_mem (a + bytes_in_word) m n)
End

Definition addresses_def:
  (addresses a 0 = {}) /\
  (addresses a (SUC n) = a INSERT addresses (a + bytes_in_word) n)
End

Theorem LENGTH_read_mem:
  !n a m. LENGTH (read_mem a m n) = n
Proof
  Induct \\ fs [read_mem_def]
QED

Triviality IN_addresses:
  !n a x. x IN addresses a n <=>
            ?i. i < n /\ x = a + n2w i * bytes_in_word
Proof
  Induct \\ fs [addresses_def]
  \\ rw [] \\ eq_tac \\ rw []
  THEN1 (qexists_tac `0` \\ fs [])
  THEN1 (qexists_tac `SUC i`
         \\ fs [ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB])
  \\ Cases_on `i` \\ fs []
  \\ fs [ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ metis_tac []
QED

Theorem addresses_thm:
   !n a. addresses a n = { a + n2w i * bytes_in_word | i < n }
Proof
  rw[EXTENSION, IN_addresses] \\ metis_tac[]
QED

Triviality memory_addresses:
  !n (a:'a word) (m:'a word -> 'a word_loc).
      n * (dimindex (:'a) DIV 8) < dimword (:'a) /\ good_dimindex (:'a) ==>
      memory m (addresses a n) = word_list a (read_mem a m n)
Proof
  once_rewrite_tac [EQ_SYM_EQ]
  \\ Induct \\ fs [addresses_def,read_mem_def,word_list_def]
  THEN1 (fs [memory_def,FUN_EQ_THM,fun2set_def,emp_def])
  \\ simp [memory_def,Once FUN_EQ_THM,one_STAR]
  \\ rw []
  \\ fs [MULT_CLAUSES]
  \\ `n * (dimindex (:α) DIV 8) < dimword (:α)` by decide_tac
  \\ res_tac \\ fs []
  \\ fs [fun2set_def,memory_def]
  \\ fs [EXTENSION,FORALL_PROD]
  \\ fs [IN_addresses]
  \\ eq_tac \\ fs [] \\ strip_tac \\ fs [] THEN1 metis_tac []
  \\ rw [] \\ eq_tac \\ fs []
  \\ rw [] \\ fs []
  THEN1 metis_tac []
  THEN1 metis_tac []
  \\ full_simp_tac std_ss [GSYM WORD_ADD_ASSOC,addressTheory.WORD_EQ_ADD_CANCEL,
       bytes_in_word_def,word_add_n2w,word_mul_n2w]
  \\ sg `i * (dimindex (:α) DIV 8) + dimindex (:α) DIV 8 < dimword (:α)`
  \\ fs[]
  \\ fs [good_dimindex_def,dimword_def]
  \\ fs [good_dimindex_def,dimword_def]
QED

Triviality MOD_LESS_EQ_MOD_IMP:
  m MOD k <= n /\ m < k ==> m <= n
Proof
  rw [] \\ fs []
QED

Triviality MAP_mem_val_MAP_INL:
  !ws f. MAP (mem_val f) (MAP INL ws) = MAP Word ws
Proof
  Induct \\ fs [mem_val_def]
QED

Theorem word_list_EQ_rev:
   !xs a. word_list a xs =
           word_list_rev (a + n2w (LENGTH xs) * bytes_in_word) (REVERSE xs)
Proof
  recInduct SNOC_INDUCT \\ fs [REVERSE_SNOC]
  \\ fs [SNOC_APPEND,word_list_APPEND,word_list_rev_def,word_list_def]
  \\ rw [SEP_CLAUSES,ADD1,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ fs [AC STAR_COMM STAR_ASSOC]
QED

Triviality word_list_and_rev_join_lemma:
  (b = a + n2w (LENGTH xs + LENGTH ys) * bytes_in_word) /\
    (p * word_list a (xs ++ REVERSE ys) * q) ss /\ b1 ==>
    (p * word_list a xs * word_list_rev b ys * q) ss /\ b1
Proof
  fs [word_list_APPEND,WORD_LEFT_ADD_DISTRIB]
  \\ fs [word_list_EQ_rev] \\ rw []
  \\ fs [AC STAR_COMM STAR_ASSOC,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
QED

Triviality word_list_IMP_read_mem:
  !xs a p.
      (p * word_list a xs) (fun2set (m,dm)) ==>
      read_mem a m (LENGTH xs) = xs
Proof
  Induct \\ fs [read_mem_def,word_list_def,STAR_ASSOC]
  \\ rw [] \\ res_tac \\ SEP_R_TAC
QED

Triviality INSERT_DELETE_EQ_DELETE:
  (x INSERT s) DELETE x = s DELETE x
Proof
  fs [EXTENSION] \\ metis_tac []
QED

Theorem word_list_exists_addresses:
   !n a. (dimindex(:'a) DIV 8) * n < dimword (:'a) /\
          good_dimindex (:'a) ==>
          word_list_exists a n (fun2set (m1,addresses (a:'a word) n))
Proof
  Induct
  THEN1 (fs [word_list_exists_thm,fun2set_def,emp_def,addresses_def])
  \\ fs [word_list_exists_thm,emp_def,addresses_def,INSERT_DELETE_EQ_DELETE,
         SEP_EXISTS_THM,MULT_CLAUSES,set_sepTheory.one_fun2set]
  \\ rw [] \\ imp_res_tac (DECIDE ``m+n<k:num ==> m < k``) \\ res_tac
  \\ sg `addresses (a + bytes_in_word) n DELETE a =
      addresses (a + bytes_in_word) n` \\ fs []
  \\ fs [EXTENSION] \\ rw [] \\ eq_tac \\ fs []
  \\ fs [IN_addresses,PULL_EXISTS]
  \\ full_simp_tac std_ss [addressTheory.WORD_EQ_ADD_CANCEL,GSYM WORD_ADD_ASSOC]
  \\ rw [] \\ fs [bytes_in_word_def,word_mul_n2w,word_add_n2w]
  \\ sg `(i * (dimindex (:'a) DIV 8) + dimindex (:'a) DIV 8)
      < dimword (:'a)` \\ fs []
  \\ fs [good_dimindex_def,dimword_def] \\ rfs [] \\ fs []
QED

Definition init_reduce_def:
  init_reduce gen_gc jump off k code bitmaps data_sp coracle (s:('a,'c,'ffi)stackSem$state) =
    let heap_ptr = theWord (s.regs ' (k + 2)) in
    let bitmap_ptr = theWord (s.regs ' 3) << word_shift (:'a) in
    let stack_ptr = theWord (s.regs ' k) in
    let base_ptr = theWord (s.regs ' (k + 1)) in
    let heap_sp = w2n (base_ptr - heap_ptr) DIV (dimindex (:'a) DIV 8) - (LENGTH store_list) in
    let stack_sp = w2n (stack_ptr - base_ptr) DIV (dimindex (:'a) DIV 8) in
      s with
      <| use_stack := T;
         use_store := T;
         use_alloc := F;
         mdomain := addresses heap_ptr heap_sp;
         bitmaps := bitmaps;
         code := code;
         compile := (λc p. s.compile c (MAP (prog_comp jump off k) p)) ;
         compile_oracle := coracle ;
         data_buffer := <|buffer := []; position := (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps)); space_left := data_sp|>;
         stack_space := stack_sp;
         stack := read_mem base_ptr s.memory (stack_sp + 1);
         store := FEMPTY |++ (MAP (\n. case store_init gen_gc k n of
                                       | INL w => (n,Word w)
                                       | INR i => (n,s.regs ' i))
                               (CurrHeap::store_list)) |>
End

Triviality init_reduce_stack_space:
  (init_reduce gen_gc jump off k code bitmaps data_sp coracle s8).stack_space <=
    LENGTH (init_reduce gen_gc jump off k code bitmaps data_sp coracle s8).stack
Proof
  fs [init_reduce_def,LENGTH_read_mem]
QED

Definition stack_heap_limit_ok_def:
  stack_heap_limit_ok t (stack_lim, heap_lim) <=>
    FLOOKUP t.store HeapLength = SOME (Word (n2w heap_lim * bytes_in_word:'a word)) /\
    heap_lim * (dimindex (:'a) DIV 8) < dimword (:'a) /\
    stack_lim = LENGTH t.stack
End

Definition init_prop_def:
  init_prop gen_gc max_heap data_sp stack_heap_lim (s:('a,'c,'ffi)stackSem$state) =
    ?curr other bitmap_base len.
       FLOOKUP s.store CurrHeap = SOME (Word curr) /\
       FLOOKUP s.store NextFree = SOME (Word curr) /\
       FLOOKUP s.store TriggerGC = SOME (Word (if gen_gc then curr else other)) /\
       FLOOKUP s.store EndOfHeap = SOME (Word other) /\
       FLOOKUP s.store OtherHeap = SOME (Word other) /\
       FLOOKUP s.store BitmapBase = SOME (Word bitmap_base) /\
       FLOOKUP s.store HeapLength = SOME (Word (n2w len * bytes_in_word)) /\
       FLOOKUP s.store ProgStart = SOME (Word 0w) /\
       FLOOKUP s.store AllocSize = SOME (Word 0w) /\
       FLOOKUP s.store Globals = SOME (Word 0w) /\
       FLOOKUP s.store GlobReal = SOME (Word curr) /\
       FLOOKUP s.store Handler = SOME (Word 0w) /\
       FLOOKUP s.store GenStart = SOME (Word 0w) /\
       FLOOKUP s.store CodeBuffer = SOME (Word s.code_buffer.position) ∧
       FLOOKUP s.store CodeBufferEnd =
         SOME (Word (s.code_buffer.position + n2w s.code_buffer.space_left)) ∧
       FLOOKUP s.store BitmapBuffer = SOME (Word s.data_buffer.position) ∧
       FLOOKUP s.store BitmapBufferEnd =
         SOME (Word
          (s.data_buffer.position +
           bytes_in_word * n2w s.data_buffer.space_left)) ∧
       stack_heap_limit_ok s stack_heap_lim ∧
       s.code_buffer.buffer = [] ∧ s.data_buffer.buffer = [] ∧
       s.use_stack /\ s.use_store /\
       FLOOKUP s.regs 0 = SOME (Loc 1 0) /\
       LENGTH s.bitmaps + data_sp + 1 < dimword (:'a) /\
       LENGTH s.stack < dimword (:'a) /\
       (other = curr + bytes_in_word * n2w len) /\
       byte_aligned curr /\
       LAST s.stack = Word 0w /\
       LENGTH s.stack = SUC s.stack_space /\
       LENGTH s.stack * (dimindex (:α) DIV 8) < dimword (:α) /\
       len + len <= max_heap /\
       (word_list_exists curr len * word_list_exists other len)
          (fun2set (s.memory,s.mdomain))
End

Definition init_code_pre_def:
  init_code_pre k bitmaps data_sp s <=>
    ?ptr2 ptr3 ptr4 bitmap_ptr.
      good_dimindex (:'a) /\ 8 <= k /\ 1 ∈ domain s.code /\
      {k; k + 1; k + 2} SUBSET s.ffi_save_regs /\
      ~s.use_stack /\ ~s.use_store /\ ~s.use_alloc /\
      FLOOKUP s.regs 2 = SOME (Word (ptr2:'a word)) /\
      FLOOKUP s.regs 3 = SOME (Word ptr3) /\
      FLOOKUP s.regs 4 = SOME (Word ptr4) /\
      s.memory ptr2 = Word bitmap_ptr /\
      s.memory (ptr2 + bytes_in_word) =
        Word (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps)) /\
      s.memory (ptr2 + 2w * bytes_in_word) =
        Word (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps) +
                           bytes_in_word * n2w data_sp) /\
      s.memory (ptr2 + 3w * bytes_in_word) = Word (s.code_buffer.position) /\
      s.memory (ptr2 + 4w * bytes_in_word) =
         Word (s.code_buffer.position + n2w s.code_buffer.space_left) /\
      ptr2 <=+ ptr4 ∧ 1024w * bytes_in_word <=+ ptr4 - ptr2 /\
      byte_aligned ptr2 ∧ byte_aligned ptr4 /\ byte_aligned bitmap_ptr /\
      (* NOTE: The last conjunct only needs to hold if
        the entry checks hold. Probably can make more assumptions
        about the bitmap_ptr too *)
      s.code_buffer.buffer = [] /\
      (word_list bitmap_ptr (MAP Word bitmaps) *
       word_list_exists (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps)) data_sp *
       word_list_exists ptr2 (w2n (ptr4 - ptr2) DIV w2n (bytes_in_word:'a word)))
        (fun2set (s.memory,s.mdomain))
End

Triviality byte_aligned_bytes_in_word_MULT:
  good_dimindex (:'a) ==>
    byte_aligned (bytes_in_word * w:'a word)
Proof
  fs [good_dimindex_def] \\ rw []
  \\ fs [alignmentTheory.byte_aligned_def,bytes_in_word_def]
  \\ qspecl_then [`2`,`w`] mp_tac alignmentTheory.aligned_mul_shift_1
  \\ qspecl_then [`3`,`w`] mp_tac alignmentTheory.aligned_mul_shift_1
  \\ fs [WORD_MUL_LSL]
QED

(* The extra b equality makes this work better with SEP_NEQ_TAC *)
Theorem word_list_wrap:
    good_dimindex (:'a) ∧
  dimword(:'a) DIV (dimindex(:'a) DIV 8) < LENGTH ls ⇒
  ∃x xs y ys b.
  word_list (a:'a word) ls = word_list a (x::xs) * word_list b (y::ys)  ∧
  b = a
Proof
  rw[]>>
  `∃r.r < LENGTH ls ∧ 0 < r ∧ a + bytes_in_word * n2w r = a` by
    (fs[addressTheory.WORD_EQ_ADD_CANCEL,bytes_in_word_def,word_mul_n2w]>>
    `0 <dimword(:'a)` by fs[good_dimindex_def] >>
    drule (GEN_ALL MOD_EQ_0_DIVISOR)>>fs[]>>disch_then kall_tac>>
    fs[good_dimindex_def,dimword_def,PULL_EXISTS]>>rfs[]>>
    asm_exists_tac>>fs[])>>
  Q.ISPECL_THEN [`TAKE r ls`,`DROP r ls`,`a`] assume_tac word_list_APPEND>>
  fs[]>>
  `0 < LENGTH (DROP r ls)` by fs[]>>
  Cases_on`DROP r ls`>>fs[]>>
  Cases_on`ls`>>fs[]>>
  metis_tac[]
QED

Triviality sub_rewrite:
  ptr <= ptr' ⇒
  -1w * n2w ptr + n2w ptr' = n2w (ptr'-ptr)
Proof
  rw[]>>simp[Once WORD_SUB_INTRO]>>
  simp[WORD_LITERAL_ADD]
QED

Triviality div_rewrite:
  n <= x ∧ 1 < n
  ⇒
  x DIV n ≠ 0
Proof
  rw[]>>
  fs[DIV_EQ_0]
QED

Theorem push_if:
   (if b then f x else f y) = f (if b then x else y) /\
    (if b then f x else g x) = (if b then f else g) x
Proof
  rw []
QED

val fmap_simp_lemma1 = prove(
  ``g |+ (0n,x) |+ (5,y) |+ (0,z) = g |+ (0,z) |+ (5,y)``,
  fs [fmap_EXT] \\ rw [] \\ fs [EXTENSION,FAPPLY_FUPDATE_THM]
  \\ rw [] \\ fs [] \\ metis_tac []);

Definition get_stack_heap_limit''_def:
  get_stack_heap_limit'' (h2:num) (h3:num) (h4:num) =
    (h4 - h3 - LENGTH store_list, (h3 - h2) DIV 2)
End

Definition get_stack_heap_limit'_def:
  get_stack_heap_limit' max_heap p2 p3 (p4:'a word) =
    let ptr2 = w2n p2 in
    let ptr3 = w2n p3 in
    let ptr4 = w2n p4 in
    let d = dimindex (:'a) DIV 8 in
    let max_heap_w = if max_heap * w2n (bytes_in_word:'a word) < dimword (:α) then
                       bytes_in_word * n2w max_heap
                     else -1w :'a word in
    let reg3 = n2w ptr2 +
               (-1w * n2w ptr2 +
                if max_heap_w <₊ -1w * n2w ptr2 + n2w ptr3 then
                  max_heap_w + n2w ptr2 :'a word
                else n2w ptr3) ⋙ (shift (:α) + 1) ≪ (shift (:α) + 1) in
      get_stack_heap_limit'' (ptr2 DIV d) (w2n reg3 DIV d) (ptr4 DIV d)
End

Definition get_stack_heap_limit_def:
  get_stack_heap_limit max_heap (ptr2,ptr3,ptr4:'a word) =
    let middle = ptr2 + (-1w * ptr2 + ptr4) ⋙ (shift (:α) + 1) ≪ shift (:α) in
    let adj_ptr2 = ptr2 + bytes_in_word * n2w max_stack_alloc in
    let adj_ptr4 = ptr4 - (bytes_in_word * n2w max_stack_alloc) in
    let adj_ptr3 = (if adj_ptr2 ≤₊ ptr3 ∧ ptr3 ≤₊ adj_ptr4 then ptr3 else middle) in
      get_stack_heap_limit' max_heap ptr2 adj_ptr3 ptr4
End

Definition read_pointers_def:
  read_pointers s =
    (theWord (THE (FLOOKUP s.regs 2)),
     theWord (THE (FLOOKUP s.regs 3)),
     theWord (THE (FLOOKUP s.regs 4)))
End


(* memory *)
(* move *)
Theorem word_list_inj:
  ∀xs a u u'. word_list a xs u ∧ word_list a xs u' ⇒ u = u'
Proof
  Induct>>rw[miscTheory.word_list_def]>- gs[set_sepTheory.emp_def]>>
  first_x_assum $ qspecl_then [‘a+bytes_in_word’, ‘u DIFF {(a,h)}’, ‘u' DIFF {(a,h)}’] assume_tac>>
  fs [Once set_sepTheory.STAR_def,set_sepTheory.SPLIT_EQ,word_list_def]>>
  fs [Once set_sepTheory.STAR_def,set_sepTheory.SPLIT_EQ,word_list_def]>>
  fs [set_sepTheory.one_def] >> gs[]>>
  gs[DIFF_DEF,EXTENSION]>>metis_tac[]
QED

(* move? *)
Theorem word_list_set:
  ∀xs a. good_dimindex (:'a) ∧
         w2n a + LENGTH xs * w2n (bytes_in_word :'a word) < dimword (:'a) ⇒
         word_list a xs (set (GENLIST (λi. a + n2w i * bytes_in_word:'a word, EL i xs) (LENGTH xs)))
Proof
  Induct>>gs[word_list_def,emp_def]>>
  rpt strip_tac>>
  gs[one_def,STAR_def,SPLIT_EQ,GENLIST]>>
  conj_tac >-
   (Cases_on ‘xs’>>gs[]>>
    irule OR_INTRO_THM2>>gs[MEM_GENLIST]>>qexists_tac ‘0’>>gs[LENGTH])>>
  first_x_assum $ qspec_then ‘a+bytes_in_word’ assume_tac>>
  simp[LIST_TO_SET_SNOC]>>
  Cases_on ‘xs’>-gs[word_add_def]>>gs[]>>
  ‘w2n (a + bytes_in_word:'a word) + SUC (LENGTH t) * w2n (bytes_in_word:'a word) < dimword (:'a)’
    by gs[bytes_in_word_def,good_dimindex_def,dimword_def,word_add_def]>>gs[]>>
  ‘(bytes_in_word:'a word) * n2w (SUC (LENGTH t)) ≠ 0w’
    by (rewrite_tac[Once WORD_MULT_COMM]>>
        irule IMP_F>>
        simp[word_mul_def]>>
        gs[bytes_in_word_def,good_dimindex_def,dimword_def])>>gs[]>>
  ‘set (GENLIST (λi. (a + bytes_in_word:'a word * n2w i,EL i (h::h'::t)))
        (SUC (LENGTH t))) DIFF {(a,h)} =
   set
   (GENLIST (λi. ((a + bytes_in_word + bytes_in_word * n2w i:'a word),EL i (h'::t)))
    (LENGTH t))’
    by (simp[EXTENSION]>>strip_tac>>simp[MEM_GENLIST]>>
        simp[EQ_IMP_THM]>>strip_tac>>gs[]
        >- (strip_tac>>
            Cases_on ‘i’>>fs[]>>
            qexists_tac ‘n’>>fs[]>>
            simp[n2w_SUC,WORD_LEFT_ADD_DISTRIB])>>
        rpt strip_tac
        >- (qexists_tac ‘SUC i’>>fs[]>>
            simp[n2w_SUC,WORD_LEFT_ADD_DISTRIB])>>
        Cases_on ‘i’>>gvs[]
        >- (pop_assum $ assume_tac o GSYM>>
            drule (iffLR WORD_ADD_INV_0_EQ)>>
            gs[bytes_in_word_def,good_dimindex_def,dimword_def])>>
        pop_assum $ mp_tac>>
        TRY (rewrite_tac[Once (GSYM WORD_ADD_ASSOC)])>>strip_tac>>
        pop_assum $ assume_tac o GSYM>>
        drule (iffLR WORD_ADD_INV_0_EQ)>>
        gs[word_add_def,word_mul_def]>>
        gs[bytes_in_word_def,good_dimindex_def,dimword_def])>>
  gs[]>>
  ‘(a + bytes_in_word * n2w (SUC (LENGTH t)),EL (LENGTH t) (h'::t)) INSERT
   set (GENLIST
        (λi. (a + bytes_in_word + bytes_in_word * n2w i,EL i (h'::t)))
        (LENGTH t)) =
   set (GENLIST
        (λi. (a + bytes_in_word + bytes_in_word * n2w i,EL i (h'::t)))
        (SUC (LENGTH t)))’
    by (simp[EXTENSION]>>strip_tac>>simp[MEM_GENLIST]>>
        simp[EQ_IMP_THM]>>strip_tac>>gs[]
        >- (strip_tac
            >- (qexists_tac ‘LENGTH t’>>gs[n2w_SUC,WORD_LEFT_ADD_DISTRIB])>>
            qexists_tac ‘i’>>gs[])>>
        strip_tac>>
        Cases_on ‘i = LENGTH t’>>gs[]
        >- (irule OR_INTRO_THM1>>gs[n2w_SUC,WORD_LEFT_ADD_DISTRIB])>>
        irule OR_INTRO_THM2>>qexists_tac ‘i’>>gs[])>>gs[]
QED

(* move? *)
Theorem word_list_seteq:
  ∀xs a. good_dimindex (:'a) ∧
         w2n a + LENGTH xs * w2n (bytes_in_word :'a word) < dimword (:'a) ⇒
         word_list a xs = (λs. s = set (GENLIST (λi. a + n2w i * bytes_in_word:'a word, EL i xs) (LENGTH xs)))
Proof
  rpt strip_tac>>rw[Once FUN_EQ_THM]>>
  drule_all word_list_set>>strip_tac>>
  simp[Once EQ_IMP_THM]>>strip_tac>>strip_tac>>gs[]>>
  drule word_list_inj>>
  qpat_x_assum ‘word_list _ _ (set _)’ $ assume_tac>>
  disch_then $ drule>>strip_tac>>gs[]
QED

(* move? *)
Theorem word_list_EL_in_memory:
  good_dimindex (:'a) ∧
  w2n a + LENGTH xs * w2n (bytes_in_word :'a word) < dimword (:'a) ∧
  (r1 * word_list a xs * r2) (fun2set (m, dm)) ∧
  i < LENGTH xs ⇒ m (a + n2w i * bytes_in_word:'a word) = EL i xs
Proof
  rpt strip_tac>>
  fs [Once set_sepTheory.STAR_def,set_sepTheory.SPLIT_EQ,memory_def,word_list_def]>>
  fs [Once set_sepTheory.STAR_def,set_sepTheory.SPLIT_EQ,memory_def,word_list_def]>>
  full_simp_tac(srw_ss())[set_sepTheory.fun2set_def,SUBSET_DEF,PULL_EXISTS]>>
  gs[word_list_seteq]>>
  qabbrev_tac ‘x = (a + bytes_in_word* n2w i, EL i xs)’>>
  ‘x ∈ u DIFF u'’
    by (
    qpat_assum ‘_ = _’ $ (fn h => REWRITE_TAC[h])>>
    gs[MEM_GENLIST,Abbr ‘x’]>>metis_tac[])>>
  last_x_assum $ qspec_then ‘x’ assume_tac>>
  gs[Abbr ‘x’]
QED

(* move? *)
Theorem word_list_in_memory:
  (r1 * word_list a xs * r2) (fun2set (m, dm)) ∧
  good_dimindex (:'a) ∧
  w2n a + LENGTH xs * w2n (bytes_in_word :'a word) < dimword (:'a) ⇒
           memory m (addresses a (LENGTH xs)) = word_list (a:'a word) xs
Proof
  rpt strip_tac>>
  drule_then drule word_list_EL_in_memory>>
  disch_then $ drule_at Any>>strip_tac>>

  simp[Once FUN_EQ_THM]>>strip_tac>>
  gs[word_list_seteq,memory_def]>>

  qmatch_goalsub_abbrev_tac ‘x = X ⇔ x = Y’>>
  ‘X=Y’
    by (gs[Abbr ‘X’, Abbr ‘Y’]>>
        simp[LIST_TO_SET_GENLIST]>>
        simp[count_def,IMAGE_DEF,
             fun2set_def,addresses_thm]>>
        simp[EXTENSION]>>strip_tac>>
        simp[EQ_IMP_THM]>>strip_tac>>strip_tac>>metis_tac[])>>
  gs[]
QED

Theorem init_code_thm:
   init_code_pre k bitmaps data_sp s /\ code_rel jump off k code s.code /\
    s.compile_oracle = (I ## MAP (prog_comp jump off k) ## I) o coracle /\
    (∀n i p. MEM (i,p) (FST(SND(coracle n))) ⇒ reg_bound p k ∧ num_stubs ≤ i+1) ∧
    lookup stack_err_lab s.code = SOME (halt_inst 2w) /\
    max_stack_alloc <= max_heap ==>
    case evaluate (init_code gen_gc max_heap k,s) of
    | (SOME res,t) => F
    | (NONE,t) =>
         (∃w2 w3 (w4:'a word).
         FLOOKUP s.regs 2 = SOME (Word w2) ∧ byte_aligned w2 ∧
         FLOOKUP t.regs (k+2) = SOME (Word w2) ∧
         FLOOKUP s.regs 4 = SOME (Word w4) ∧ byte_aligned w4 ∧ w2 <+ w4 ∧
         FLOOKUP t.regs k = SOME (Word (w4 - bytes_in_word)) ∧
         (w2 + n2w max_stack_alloc * bytes_in_word ≤₊ w3 ∧
          w3 ≤₊ w4 - n2w max_stack_alloc * bytes_in_word ∧
          w2n (-1w * w2 + w3) ≤ max_heap * w2n (bytes_in_word:'a word) ∧
          (w2n (bytes_in_word:'a word)) * max_heap < dimword (:α) ⇒
          FLOOKUP t.regs (k+1) =
          SOME (Word (((w3 + -1w * w2) ⋙ (shift (:α) + 1) ≪ (shift (:α) + 1))
                      + w2 + (bytes_in_word:'a word) * (n2w (LENGTH store_list))))) ∧
         FLOOKUP s.regs 3 = SOME (Word w3)) ∧
         state_rel jump off k (init_reduce gen_gc jump off k code bitmaps data_sp coracle t) t /\
         t.ffi = s.ffi /\
         init_prop gen_gc max_heap data_sp (get_stack_heap_limit max_heap (read_pointers s))
                   (init_reduce gen_gc jump off k code bitmaps data_sp coracle t) ∧
         s.mdomain = t.mdomain ∧
         s.sh_mdomain = t.sh_mdomain ∧
         (let t0 = init_reduce gen_gc jump off k code bitmaps data_sp coracle t in
            fun2set (s.memory, t0.mdomain) = fun2set (t.memory, t0.mdomain))
Proof
  simp_tac std_ss [init_code_pre_def] \\ strip_tac
  \\ `k <> 3 /\ k <> 4 /\ k <> 5` by decide_tac
  \\ full_simp_tac std_ss [init_code_def,LET_DEF]
  \\ qpat_abbrev_tac `max_heap_w = if _ then _ else _`
  \\ fs [GSYM NOT_LESS]
  \\ `shift (:α) + 1 < dimindex (:α)` by
        fs [good_dimindex_def,
            backend_commonTheory.word_shift_def]
  \\ ntac 9 tac1 \\ fs [fmap_simp_lemma1]
  \\ qmatch_goalsub_abbrev_tac `(0,Word middle)`
  \\ qmatch_goalsub_abbrev_tac `(2,Word adj_ptr2)`
  \\ qmatch_goalsub_abbrev_tac `(4,Word adj_ptr4)`
  \\ qpat_abbrev_tac `pat = (if _ then _ else _)`
  \\ `pat = (NONE, s with regs := s.regs |+ (0,Word middle) |+
                 (5,Word (bytes_in_word * n2w max_stack_alloc)) |+
                 (2,Word adj_ptr2) |+ (4,Word adj_ptr4) |+ (3,Word
       (if adj_ptr2 <=+ ptr3 /\ ptr3 <=+ adj_ptr4 then ptr3 else middle)))` by
   (unabbrev_all_tac \\ rw []
    \\ fs [fmap_EXT,state_component_equality,FLOOKUP_DEF,
           FAPPLY_FUPDATE_THM,EXTENSION] \\ rw [] \\ fs []
    \\ fs [GSYM WORD_NOT_LOWER_EQUAL] \\ metis_tac [])
  \\ pop_assum (fn th => rewrite_tac [th])
  \\ pop_assum kall_tac
  \\ qpat_abbrev_tac `adj_ptr3 = (if _ then _ else middle)`
  \\ fs [read_pointers_def,wordSemTheory.theWord_def,get_stack_heap_limit_def]
  \\ Cases_on `ptr2` \\ fs []
  \\ rename1 `FLOOKUP s.regs 2 = SOME (Word (n2w ptr2))`
  \\ Cases_on `ptr3` \\ fs []
  \\ rename1 `FLOOKUP s.regs 3 = SOME (Word (n2w ptr3))`
  \\ Cases_on `ptr4` \\ fs []
  \\ rename1 `FLOOKUP s.regs 4 = SOME (Word (n2w ptr4))`
  \\ fs [WORD_LS,get_stack_heap_limit'_def]
  \\ `?l. ptr4 = ptr2 + l` by fs [GSYM LESS_EQ_EXISTS]
  \\ rveq \\ fs [GSYM word_add_n2w]
  \\ `?ptr3. adj_ptr3 = n2w ptr3 /\
             ptr2 + max_stack_alloc * (dimindex (:α) DIV 8) <= ptr3 /\
             ptr3 + max_stack_alloc * (dimindex (:α) DIV 8) <= ptr2 + l` by
   (fs [Abbr`adj_ptr3`] \\ rw [] THEN1
     (qexists_tac `ptr3` \\ fs []
      \\ fs [Abbr`adj_ptr4`,Abbr`adj_ptr2`]
      \\ `n2w ptr2 + -1w * n2w max_stack_alloc * bytes_in_word + n2w l : 'a word =
          n2w ptr2 + n2w (l - max_stack_alloc * (dimindex (:α) DIV 8))` by
       (rewrite_tac [WORD_EQ_ADD_LCANCEL,GSYM WORD_ADD_ASSOC]
        \\ rfs [good_dimindex_def,bytes_in_word_def,dimword_def,
                max_stack_alloc_def]
        \\ TRY (qsuff_tac `n2w l - 1020w = n2w (l − 1020)` THEN1 fs [])
        \\ TRY (qsuff_tac `n2w l - 2040w = n2w (l − 2040)` THEN1 fs [])
        \\ rfs [addressTheory.word_arith_lemma2,dimword_def])
      \\ fs []
      \\ rfs [good_dimindex_def,bytes_in_word_def,dimword_def]
      \\ rfs [good_dimindex_def,bytes_in_word_def,dimword_def]
      \\ rfs [max_stack_alloc_def,word_add_n2w,dimword_def])
    \\ pop_assum kall_tac
    \\ qunabbrev_tac `middle`
    \\ qexists_tac `w2n (n2w ptr2 +
          (n2w l ⋙ (shift (:α) + 1) ≪ shift (:α)) :'a word)`
    \\ simp []
    \\ qabbrev_tac `l1 = l DIV (2 ** (shift (:α) + 1)) * 2 ** (shift (:α))`
    \\ `n2w l ⋙ (shift (:α) + 1) ≪ shift (:α) = n2w l1:'a word` by
     (qunabbrev_tac `l1` \\ fs [WORD_MUL_LSL,GSYM word_mul_n2w]
      \\ qsuff_tac `n2w l ⋙ (shift (:α) + 1) =
                    n2w (l DIV 2 ** (shift (:α) + 1)) :'a word` THEN1 fs []
      \\ once_rewrite_tac [GSYM w2n_11]
      \\ rewrite_tac [w2n_lsr] \\ fs []
      \\ fs [DIV_LT_X] \\ rfs [good_dimindex_def]
      \\ rfs [dimword_def,backend_commonTheory.word_shift_def])
    \\ asm_rewrite_tac []
    \\ `l1 <= l DIV 2` by
     (fs [X_LE_DIV] \\ fs [Abbr`l1`]
      \\ rfs [good_dimindex_def]
      \\ rfs [dimword_def,backend_commonTheory.word_shift_def]
      \\ TRY (qspec_then `l` mp_tac (MATCH_MP DIVISION (DECIDE ``0n < 8``))
        \\ disch_then (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th])))
        \\ fs [] \\ NO_TAC)
      \\ TRY (qspec_then `l` mp_tac (MATCH_MP DIVISION (DECIDE ``0n < 16``))
        \\ disch_then (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th])))
        \\ fs [] \\ NO_TAC))
    \\ `l1 <= l` by fs [X_LE_DIV]
    \\ fs [word_add_n2w,max_stack_alloc_def]
    \\ rfs [good_dimindex_def]
    \\ rfs [bytes_in_word_def,dimword_def,X_LE_DIV]
    \\ rfs [Abbr`l1`,backend_commonTheory.word_shift_def]
    \\ qspec_then `l` strip_assume_tac (MATCH_MP DIVISION (DECIDE ``0n < 8``))
    \\ qspec_then `l` strip_assume_tac (MATCH_MP DIVISION (DECIDE ``0n < 16``))
    \\ decide_tac)
  \\ `n2w ptr2 <=+ n2w (ptr2 + l)` by fs[word_lo_n2w,word_ls_n2w]
  \\ `n2w (ptr3 - ptr2) >>> 1 = n2w ((ptr3 - ptr2) DIV 2)` by
     (once_rewrite_tac [GSYM w2n_11] \\ rewrite_tac [w2n_lsr] \\ fs [DIV_LT_X])
  \\ ntac 7 tac1
  \\ fs [Abbr`adj_ptr2`,Abbr`adj_ptr4`]
  \\ qpat_abbrev_tac `pat = (if _ then _ else _)`
  \\ `pat = (NONE, s with regs :=
                 s.regs |+ (0,Word (-1w * n2w ptr2 + n2w ptr3'))
                        |+ (5,Word max_heap_w) |+ (3,Word
           (if max_heap_w <₊ -1w * n2w ptr2 + n2w ptr3' :'a word
            then n2w ptr2 + max_heap_w else n2w ptr3')))` by
   (fs [Abbr`pat`] \\ rw []
    \\ fs [fmap_EXT,state_component_equality,FLOOKUP_DEF,
           FAPPLY_FUPDATE_THM,EXTENSION] \\ rw [] \\ fs []
    \\ fs [GSYM WORD_NOT_LOWER_EQUAL]
    \\ eq_tac \\ rw [] \\ fs [])
  \\ pop_assum (fn th => rewrite_tac [th])
  \\ pop_assum kall_tac \\ fs []
  \\ ntac 4 tac1
  \\ qmatch_goalsub_abbrev_tac `(3n,Word reg3)`
  \\ `n2w ptr2 ∈ s.mdomain /\
      n2w ptr2 + bytes_in_word ∈ s.mdomain /\
      n2w ptr2 + 2w * bytes_in_word ∈ s.mdomain /\
      n2w ptr2 + 3w * bytes_in_word ∈ s.mdomain /\
      n2w ptr2 + 4w * bytes_in_word ∈ s.mdomain` by (
    qabbrev_tac `kk = l DIV w2n (bytes_in_word:'a word)`
    \\ `5 <= kk` by (fs [Abbr`kk`,good_dimindex_def]
                     \\ rfs [bytes_in_word_def,dimword_def,X_LE_DIV])
    \\ Cases_on `kk` THEN1 fs []
    \\ Cases_on `n` THEN1 fs []
    \\ Cases_on `n'` THEN1 fs []
    \\ Cases_on `n` THEN1 fs []
    \\ Cases_on `n'` THEN1 fs []
    \\ fs [word_list_exists_thm,SEP_CLAUSES,SEP_EXISTS_THM]
    \\ SEP_R_TAC \\ simp [])
  \\ fs [] \\ tac
  \\ `w2n (bytes_in_word:'a word) = dimindex (:'a) DIV 8` by
    (fs [good_dimindex_def,bytes_in_word_def,dimword_def])
  \\ fs [] \\ pop_assum kall_tac
  \\ fs [word_add_n2w,WORD_LO]
  \\ `byte_aligned = aligned (shift (:'a)):'a word -> bool` by
      (rpt (fs [alignmentTheory.byte_aligned_def,
            backend_commonTheory.word_shift_def,
            good_dimindex_def,FUN_EQ_THM]))
  \\ fs [GSYM word_add_n2w]
  \\ rfs [alignmentTheory.aligned_add_sub]
  \\ `aligned (shift (:α)) reg3` by
   (fs [Abbr`reg3`] \\ rw []
    \\ fs [alignmentTheory.aligned_add_sub]
    \\ fs [alignmentTheory.aligned_add_sub |> ONCE_REWRITE_RULE [WORD_ADD_COMM]]
    \\ match_mp_tac aligned_lsl_leq \\ simp [])
  \\ Cases_on `reg3`
  \\ rename [`Abbrev (n2w final_ptr3 = _)`]
  \\ `bytes_in_word * bitmap_ptr ⋙ shift (:α) = bitmap_ptr :'a word` by
   (once_rewrite_tac [WORD_MULT_COMM]
    \\ simp [GSYM lsl_word_shift]
    \\ fs [alignmentTheory.aligned_def,alignmentTheory.align_shift])

  \\ qabbrev_tac `d = dimindex (:α) DIV 8`
  \\ `d <> 0 /\ 0 < d /\
      ptr2 MOD d = 0 /\
      final_ptr3 MOD d = 0 /\
      l MOD d = 0` by
    (qpat_x_assum `byte_aligned = aligned (shift (:α))` (assume_tac o GSYM)
     \\ fs [alignmentTheory.byte_aligned_def,aligned_w2n]
     \\ fs [good_dimindex_def,Abbr`d`]
     \\ fs [] \\ rfs [backend_commonTheory.word_shift_def])
  \\ ntac 3 (drule MOD_EQ_IMP_MULT \\ asm_rewrite_tac [] \\ pop_assum kall_tac)
  \\ strip_tac \\ rename1 `ptr2 = d * h2`
  \\ strip_tac \\ rename1 `final_ptr3 = d * h3`
  \\ strip_tac \\ rename1 `l = d * l4`
  \\ fs []
  \\ qpat_abbrev_tac `pat = get_stack_heap_limit'' _ _ _`

  \\ `pat = get_stack_heap_limit'' h2 h3 (h2 + l4)` by
       (fs [Abbr`pat`] \\ drule MULT_DIV \\ fs []
        \\ simp_tac std_ss [GSYM LEFT_ADD_DISTRIB])
  \\ pop_assum (fn th => rewrite_tac [th]) \\ pop_assum kall_tac
  \\ fs [bytes_in_word_def,word_mul_n2w]
  \\ `(d * l4 DIV d) = l4` by fs [DIV_EQ_X,Abbr`d`]
  \\ fs [] \\ pop_assum kall_tac
  \\ rfs [] \\ fs []
  \\ rpt (qpat_x_assum `_ MOD _ = 0n` kall_tac)
  \\ `?heap_length. h3 = h2 + heap_length /\ heap_length <= max_heap /\
                    EVEN heap_length /\
                    max_stack_alloc <= heap_length + LENGTH store_list /\
                    heap_length + max_stack_alloc <= l4` by
   (simp [EVAL ``LENGTH store_list``]
    \\ qpat_x_assum `Abbrev (n2w (d * h3) = _)` mp_tac
    \\ IF_CASES_TAC \\ fs [] THEN1
     (Cases_on `d * max_heap < dimword (:α)`
      \\ fs [Abbr`max_heap_w`] \\ TRY (fs [GSYM WORD_LO,WORD_LO_word_T] \\ NO_TAC)
      \\ `n2w (d * max_heap) ⋙ (shift (:α) + 1) ≪ (shift (:α) + 1) =
          n2w (d * 2 * (max_heap DIV 2)) :'a word` by
       (rewrite_tac [GSYM alignmentTheory.align_shift]
        \\ fs [alignmentTheory.align_w2n,EXP_ADD]
        \\ `2 ** shift (:α) = d` by
          (unabbrev_all_tac \\ rfs [good_dimindex_def]
           \\ rfs [backend_commonTheory.word_shift_def])
        \\ pop_assum (fn th => rewrite_tac [th])
        \\ qsuff_tac `d * max_heap DIV (2 * d) = max_heap DIV 2` \\ fs []
        \\ once_rewrite_tac [MULT_COMM]
        \\ drule DIV_DIV_DIV_MULT
        \\ disch_then (fn th => simp [GSYM th])
        \\ once_rewrite_tac [MULT_COMM]
        \\ drule MULT_DIV \\ fs [])
      \\ fs [] \\ simp [markerTheory.Abbrev_def,word_add_n2w]
      \\ `w2n (n2w ptr3' + -1w * n2w (d * h2):'a word) = ptr3' - d * h2` by
       (rewrite_tac [WORD_SUB_INTRO,WORD_MULT_CLAUSES,
           addressTheory.word_arith_lemma2] \\ fs [])
      \\ fs [] \\ strip_tac
      \\ qspec_then `max_heap` mp_tac (MATCH_MP DIVISION (DECIDE ``0 < 2n``))
      \\ disch_then (assume_tac o GSYM)
      \\ `(d * h2 + 2 * (d * (max_heap DIV 2))) < dimword (:α)` by
       (fs [Abbr`d`,good_dimindex_def]
        \\ rfs [dimword_def,max_stack_alloc_def])
      \\ fs []
      \\ `h3 = h2 + 2 * (max_heap DIV 2)` by
       (fs [Abbr`d`,good_dimindex_def]
        \\ rfs [dimword_def,max_stack_alloc_def])
      \\ pop_assum (fn th => fs [th])
      \\ fs [Abbr`d`,good_dimindex_def]
      \\ rfs [EVEN_DOUBLE]
      \\ `max_heap MOD 2 < 2` by fs [] \\ decide_tac)
    \\ `w2n (n2w (d * h2) + n2w (d * max_stack_alloc):'a word) ≤ ptr3' ∧
        ptr3' ≤ w2n(n2w (d * h2) + n2w (d * l4) +
                   -1w * n2w (d * max_stack_alloc):'a word)` by
     (qpat_x_assum `Abbrev (n2w _ = _)` mp_tac \\ IF_CASES_TAC
      THEN1 (simp [markerTheory.Abbrev_def] \\ strip_tac \\ fs [])
      \\ pop_assum kall_tac
      \\ simp [markerTheory.Abbrev_def] \\ strip_tac \\ rveq
      \\ fs [word_add_n2w]
      \\ rewrite_tac [WORD_SUB_INTRO,WORD_MULT_CLAUSES,
           addressTheory.word_arith_lemma2] \\ fs [])
    \\ ntac 2 (pop_assum mp_tac)
    \\ fs [] \\ rewrite_tac [markerTheory.Abbrev_def]
    \\ strip_tac \\ rveq
    \\ `d * h2 <= ptr3'` by fs [] \\ pop_assum mp_tac
    \\ simp [Once LESS_EQ_EXISTS]
    \\ strip_tac \\ fs [GSYM word_add_n2w]
    \\ rveq \\ fs []
    \\ rewrite_tac [GSYM alignmentTheory.align_shift]
    \\ fs [alignmentTheory.align_w2n,EXP_ADD]
    \\ `2 ** shift (:α) = d` by
      (unabbrev_all_tac \\ rfs [good_dimindex_def]
       \\ rfs [backend_commonTheory.word_shift_def])
    \\ pop_assum (fn th => rewrite_tac [th])
    \\ fs [] \\ simp [markerTheory.Abbrev_def,word_add_n2w]
    \\ `2 * (d * (p DIV (2 * d))) <= p` by
     (`0 < 2 * d` by fs [] \\ drule DIVISION
      \\ disch_then (qspec_then `p` mp_tac) \\ decide_tac)
    \\ `(d * h2 + 2 * (d * (p DIV (2 * d)))) < dimword (:α)` by
       (fs [Abbr`d`,good_dimindex_def]
        \\ rfs [dimword_def,max_stack_alloc_def])
    \\ fs [] \\ rpt strip_tac
    \\ `h3 = h2 + 2 * (p DIV (2 * d))` by
       (fs [Abbr`d`,good_dimindex_def] \\ rfs [dimword_def])
    \\ rveq \\ fs [EVEN_DOUBLE]
    \\ rfs [word_add_n2w]
    \\ `p ≤ d * l4 − d * max_stack_alloc` by fs []
    \\ conj_tac THEN1
     (Cases_on `d * max_heap < dimword (:α)` \\ fs []
      \\ fs [Abbr`max_heap_w`] \\ rfs []
      \\ fs [Abbr`d`,good_dimindex_def] \\ rfs [])
    \\ fs [Abbr`d`,good_dimindex_def]
    \\ rfs [dimword_def,max_stack_alloc_def,word_add_n2w]
    \\ TRY (`127 <= p DIV 8` by fs [X_LE_DIV] \\ fs [])
    \\ TRY (`127 <= p DIV 16` by fs [X_LE_DIV] \\ fs []))
  \\ rveq \\ fs []
  \\ `?stack_length. l4 = heap_length + stack_length /\
                     LENGTH store_list + 1 <= stack_length` by
   (qexists_tac `l4 - heap_length` \\ fs [] \\ EVAL_TAC
    \\ fs [max_stack_alloc_def,Abbr`d`,good_dimindex_def]
    \\ rfs [dimword_def,LEFT_ADD_DISTRIB])
  \\ rveq \\ fs [LEFT_ADD_DISTRIB,word_add_n2w]
  \\ full_simp_tac std_ss [GSYM ADD_ASSOC]
  \\ rpt (qpat_x_assum `T` kall_tac)
  \\ `LENGTH store_list <= stack_length` by fs []
  \\ pop_assum mp_tac
  \\ simp_tac std_ss [Once LESS_EQ_EXISTS]
  \\ strip_tac \\ rename1 `_ = _ + rest_of_stack_len:num`
  \\ var_eq_tac \\ full_simp_tac std_ss []
  \\ full_simp_tac std_ss [ADD_ASSOC]
  \\ full_simp_tac std_ss [word_list_exists_ADD]
  \\ fs [bytes_in_word_def,word_mul_n2w,word_add_n2w]
  \\ fs [word_list_exists_def,SEP_CLAUSES,SEP_EXISTS_THM]
  \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR]
  \\ rename1 `LENGTH rest = rest_of_stack_len`
  \\ qpat_x_assum `LENGTH rest = rest_of_stack_len` mp_tac
  \\ rename1 `LENGTH bitst = LENGTH store_list`
  \\ qpat_x_assum `LENGTH bitst = LENGTH store_list` mp_tac

  \\ rename1 `LENGTH heap = heap_length`
  \\ qpat_x_assum `LENGTH heap = heap_length` mp_tac
  \\ rpt strip_tac \\ rpt var_eq_tac
  \\ full_simp_tac std_ss [LEFT_ADD_DISTRIB,ADD_ASSOC]
  \\ pop_assum (mp_tac o GSYM)
  \\ simp_tac std_ss [markerTheory.Abbrev_def] \\ strip_tac
  \\ `LENGTH rest <> 0` by (unabbrev_all_tac \\ decide_tac)
  \\ full_simp_tac std_ss [LENGTH_NIL]
  \\ fs [init_memory_def] \\ tac
  \\ `?r1 rest1. rest = SNOC r1 rest1` by metis_tac [SNOC_CASES]
  \\ var_eq_tac \\ full_simp_tac std_ss [SNOC_APPEND,LENGTH_APPEND,
       LEFT_ADD_DISTRIB,ADD_ASSOC,word_list_APPEND,word_add_n2w,
       word_list_def,bytes_in_word_def,LENGTH,ADD1,word_mul_n2w,
       SEP_CLAUSES]
  \\ fs [GSYM word_add_n2w] \\ fs [word_add_n2w]
  \\ SEP_R_TAC \\ fs []
  \\ qabbrev_tac `m = s.memory`
  \\ qabbrev_tac `dm = s.mdomain`
  \\ SEP_W_TAC
  \\ qpat_abbrev_tac `m4 = (_ =+ Word 0w) m`
  \\ qpat_x_assum `_ (fun2set (m,dm))` kall_tac
  \\ fs [star_move_lemma]
  \\ qpat_abbrev_tac `s7 = s with <| regs := _ ; memory := m4 |>`
  \\ drule (GEN_ALL store_list_code_thm)
  \\ disch_then (qspecl_then [`0`,`k+1`,
       `(MAP (store_init gen_gc k) (REVERSE store_list))`,`s7`] mp_tac)
  \\ impl_tac THEN1
   (unabbrev_all_tac \\ fs [get_var_def] \\ tac
    \\ fs [EVERY_MAP]
    \\ fs [store_list_def] \\ EVAL_TAC
    \\ fs [FLOOKUP_DEF] \\ IF_CASES_TAC \\ fs [])
  \\ strip_tac \\ fs []
  \\ reverse IF_CASES_TAC \\ fs[]
  >- ( fs[Abbr`s7`,loc_check_def] )
   \\ qpat_abbrev_tac `s8 = s7 with <|regs := _ ; memory := _ |>`
   \\ conj_tac >-
    (gs[Abbr ‘s7’, FLOOKUP_UPDATE, FUPDATE_LIST,wordsTheory.WORD_LITERAL_ADD]
     \\ strip_tac
     \\simp[(GSYM wordsTheory.word_add_n2w)]
     \\ qpat_x_assum `Abbrev (n2w _ = _)` $ assume_tac o REWRITE_RULE[markerTheory.Abbrev_def]
     \\ gs[]
     \\ gs[Abbr ‘ptr3'’]
     \\ gs[Abbr ‘max_heap_w’]
     \\ gs[]
     \\ `w2n (bytes_in_word:'a word) = dimindex (:'a) DIV 8` by
       (qpat_x_assum ‘Abbr (d = _)’ $ kall_tac>>
        fs [good_dimindex_def,bytes_in_word_def,dimword_def])>>
     ‘(bytes_in_word:'a word) * n2w (LENGTH bitst) = n2w (d * LENGTH bitst)’
       by gs[wordsTheory.word_mul_def]
     \\ gs[])
  \\ qpat_x_assum `n2w _ ⋙ 1 = n2w _` kall_tac
  \\ rpt (qpat_x_assum `Abbrev (n2w _ = _)` kall_tac)
 \\ rpt var_eq_tac>> rveq>>fs[]
  \\ fs [state_rel_def,GSYM CONJ_ASSOC]
  \\ rpt (conj_tac THEN1 (fs [init_reduce_def] \\ unabbrev_all_tac \\ fs []))
  \\ conj_tac >- (
    simp_tac(srw_ss()++LET_ss)[Abbr`s8`,Abbr`s7`,init_reduce_def,o_DEF] \\
    ASM_REWRITE_TAC[] \\
    simp_tac(srw_ss()++LET_ss)[o_DEF] )
  \\ conj_tac >- (
    fs[Abbr`s8`,init_reduce_def]
    \\ rpt gen_tac
    \\ disch_then assume_tac
    \\ res_tac \\ fs [NOT_LESS])
  \\ conj_tac >- (
    simp_tac(srw_ss()++LET_ss)[init_reduce_def] \\
    metis_tac[] )
  \\ `FLOOKUP s8.regs (k + 1) = SOME (Word
          (n2w (d * h2 + d * LENGTH heap) +
           bytes_in_word * n2w (LENGTH store_list)))` by
    (unabbrev_all_tac \\ fs [FLOOKUP_UPDATE,FUPDATE_LIST] \\ NO_TAC)
  \\ fs [bytes_in_word_def,word_mul_n2w,word_add_n2w]
  \\ `s8.ffi_save_regs = s.ffi_save_regs` by
    (unabbrev_all_tac \\ fs [FLOOKUP_UPDATE,FUPDATE_LIST] \\ NO_TAC)
  \\ fs [init_reduce_stack_space,INSERT_SUBSET]
  \\ fs [init_reduce_def]
  \\ rpt (qpat_x_assum `evaluate _ = _` kall_tac)
  \\ drule MOD_LESS_EQ_MOD_IMP
  \\ impl_tac THEN1
   (unabbrev_all_tac
    \\ fs [good_dimindex_def,dimword_def,max_stack_alloc_def]
    \\ rfs [] \\ decide_tac) \\ strip_tac
  \\ qunabbrev_tac `s8`
  \\ qunabbrev_tac `s7`
  \\ fs [FUPDATE_LIST,FAPPLY_FUPDATE_THM,wordSemTheory.theWord_def,
         FLOOKUP_UPDATE,mem_val_def]
  \\ fs [store_init_def,store_list_def,UPDATE_LIST_def,APPLY_UPDATE_THM,
         FLOOKUP_UPDATE,word_store_def,mem_val_def,FAPPLY_FUPDATE_THM]
  \\ fs [FLOOKUP_DEF,GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ fs [ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV,LENGTH_read_mem,
         wordSemTheory.theWord_def,init_prop_def,the_SOME_Word_def,
         is_SOME_Word_def, FLOOKUP_UPDATE]
  \\ fs [GSYM CONJ_ASSOC]
  \\ `read_mem (n2w (d * h2)) m1 (LENGTH heap) = heap` by
   (match_mp_tac(GEN_ALL(ONCE_REWRITE_RULE[STAR_COMM]word_list_IMP_read_mem))
    \\ fs [AC STAR_ASSOC STAR_COMM]
    \\ rename1`word_list (n2w(d*h2) + _) xxx`
    \\ metis_tac[STAR_ASSOC,STAR_COMM])
  \\ fs [mem_val_def,APPLY_UPDATE_THM,FAPPLY_FUPDATE_THM]
  \\ rfs [MAP_mem_val_MAP_INL]
  \\ `word_list
       (n2w (d * h2) + n2w (d * LENGTH bitst) + n2w (d * LENGTH heap)) rest1 *
      one (n2w (d * h2) + n2w (d * LENGTH bitst) +
        n2w (d * LENGTH heap) + n2w (d * LENGTH rest1):'a word,Word 0w) =
      word_list (n2w (d * h2) + n2w (d * LENGTH bitst) + n2w (d * LENGTH heap))
         (rest1 ++ [Word 0w])` by
   (fs [word_list_APPEND,word_list_def,SEP_CLAUSES,bytes_in_word_def,
        word_add_n2w,word_mul_n2w] \\ NO_TAC)
  \\ qmatch_assum_abbrev_tac `STAR rr1 rr2 = _`
  \\ fs [AC STAR_COMM STAR_ASSOC]
  \\ full_simp_tac std_ss [STAR_ASSOC]
  \\ ntac 3 (pop_assum kall_tac)
  \\ fs [word_add_n2w]
  \\ `n2w (d * h2 + d * LENGTH heap) >>> word_shift (:'a) =
      n2w (h2 + LENGTH heap):'a word` by
   (simp_tac std_ss [GSYM w2n_11,w2n_lsr] \\ fs []
    \\ `2 ** word_shift (:'a) = d` by
     (unabbrev_all_tac
      \\ fs [good_dimindex_def,word_shift_def])
    \\ fs [GSYM LEFT_ADD_DISTRIB,ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV]
    \\ Cases_on `d` \\ fs [MULT_CLAUSES] \\ decide_tac)
  \\ fs []
  \\ `!ww:'a word. ww << word_shift (:'a) = ww * n2w d` by
   (`2 ** word_shift (:'a) = d` by
     (unabbrev_all_tac
      \\ fs [good_dimindex_def,word_shift_def])
    \\ fs [WORD_MUL_LSL] \\ NO_TAC)
  \\ fs [GSYM word_add_n2w,GSYM word_mul_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ fs [word_mul_n2w,ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV]
  \\ `(LENGTH heap) * (dimindex (:'a) DIV 8) < dimword (:'a)` by rfs []
  \\ qmatch_goalsub_abbrev_tac`addresses _ lh`
  \\ `lh = LENGTH heap`
  by (
    simp[Abbr`lh`,GSYM LEFT_ADD_DISTRIB]
    \\ once_rewrite_tac[MULT_COMM]
    \\ simp[MULT_DIV] )
  \\ qunabbrev_tac`lh` \\ pop_assum SUBST_ALL_TAC
  \\ conj_tac THEN1 fs [bytes_in_word_def,word_mul_n2w]
  \\ conj_tac THEN1
     (fs [max_stack_alloc_def,Abbr`d`,good_dimindex_def] \\ rfs [])
  \\ drule memory_addresses \\ fs []
  \\ disch_then kall_tac
  \\ qmatch_goalsub_abbrev_tac `read_mem a`
  \\ qmatch_goalsub_abbrev_tac`read_mem a m1 b`
  \\ `read_mem a m1 (LENGTH rest1 + 1) = rest1 ++ [Word 0w]` by (
    `LENGTH rest1 + 1 = LENGTH (rest1 ++ [Word 0w])` by fs []
    \\ pop_assum (fn th => rewrite_tac [th])
    \\ match_mp_tac word_list_IMP_read_mem
    \\ once_rewrite_tac [STAR_COMM]
    \\ full_simp_tac std_ss [GSYM STAR_ASSOC]
    \\ asm_exists_tac \\ fs [])
  \\ fs[] \\ rfs[]
  \\ simp[word_list_APPEND,word_list_def,SEP_CLAUSES]
  \\ qpat_x_assum `_ (fun2set (m1,dm))`
       (assume_tac o ONCE_REWRITE_RULE [STAR_COMM])
  \\ qmatch_asmsub_abbrev_tac`word_list aa xx * _`
  \\ `a = aa + n2w (LENGTH xx) * bytes_in_word`
  by (
    simp[Abbr`aa`,Abbr`a`,Abbr`xx`,bytes_in_word_def] \\
    simp[word_mul_n2w] )
  \\ first_assum SUBST1_TAC
  \\ qmatch_goalsub_abbrev_tac`word_list_rev _ yy`
  \\ `yy = REVERSE xx` by (
    simp[Abbr`xx`,Abbr`yy`]
    \\ Cases_on`gen_gc` \\ fs[] )
  \\ qunabbrev_tac`yy` \\ pop_assum SUBST_ALL_TAC
  \\ rewrite_tac[GSYM word_list_EQ_rev]
  \\ pop_assum (SUBST_ALL_TAC o GSYM)
  \\ fs[AC STAR_ASSOC STAR_COMM,bytes_in_word_def,word_mul_n2w]
  \\ conj_tac >- (
    simp[word_list_exists_def,SEP_EXISTS_THM,SEP_CLAUSES]
    \\ qexists_tac`xs` \\ simp[SEP_CLAUSES]
    \\ fs [word_list_APPEND,word_list_def]
    \\ rfs [AC STAR_COMM STAR_ASSOC,bytes_in_word_def,word_mul_n2w,SEP_CLAUSES] )
  \\ qpat_abbrev_tac `get_lims = get_stack_heap_limit'' _ _ _`
  \\ `get_lims = (b, LENGTH heap DIV 2)` by
   (fs [Abbr`b`,Abbr`get_lims`,get_stack_heap_limit''_def]
    \\ qpat_x_assum `_ = LENGTH bitst` (assume_tac o GSYM)
    \\ fs [store_list_def])
  \\ asm_rewrite_tac [] \\ ntac 2 (pop_assum kall_tac)
  \\ `bytes_in_word * n2w (LENGTH heap DIV 2) =
      (n2w (d * LENGTH heap) >>> 1) :'a word` by
   (fs [bytes_in_word_def,word_mul_n2w]
    \\ `?hi. LENGTH heap = 2 * hi` by fs [EVEN_EXISTS] \\ fs []
    \\ fs [MULT_DIV |> ONCE_REWRITE_RULE [MULT_COMM]]
    \\ once_rewrite_tac [GSYM w2n_11]
    \\ rewrite_tac [w2n_lsr] \\ fs []
    \\ fs [Abbr`d`,good_dimindex_def] \\ fs []
    \\ once_rewrite_tac [EQ_SYM_EQ] \\ fs [DIV_EQ_X])
  \\ simp [stack_heap_limit_ok_def,FLOOKUP_UPDATE]
  \\ `d * (LENGTH heap DIV 2) < dimword (:α)` by
   (`LENGTH heap DIV 2 <= LENGTH heap` by fs [DIV_LE_X]
    \\ fs [Abbr`d`,good_dimindex_def,dimword_def] \\ fs [] \\ rfs [])
  \\ conj_tac >- (
   Cases_on `gen_gc` \\ fs []
   \\ `?hi. LENGTH heap = 2 * hi` by fs [EVEN_EXISTS]
   \\ qexists_tac `hi`
   \\ fs [bytes_in_word_def,word_mul_n2w]
   \\ `n2w d = bytes_in_word` by fs [bytes_in_word_def]
   \\ fs [GSYM word_mul_n2w,GSYM word_list_exists_ADD]
   \\ `(2w * (bytes_in_word * n2w hi)) ⋙ 1 = bytes_in_word * (n2w hi) :'a word` by
    (once_rewrite_tac [GSYM w2n_11] \\ rewrite_tac [w2n_lsr]
     \\ fs [bytes_in_word_def,word_mul_n2w] \\ fs [DIV_EQ_X])
   \\ fs []
   \\ `b < dimword (:α)` by
    (unabbrev_all_tac \\ fs []
     \\ rfs [good_dimindex_def] \\ rfs [dimword_def])
   \\ simp []
   \\ `LENGTH bitmaps + (LENGTH xs + 1) < dimword (:α)` by
    (qmatch_asmsub_abbrev_tac`(a1 * (word_list _ ls1 * (a2 * (a3 * (word_list _ ls2))))) _`>>
     `(word_list bitmap_ptr (ls1++ls2) * a1*a2*a3) (fun2set (m1,dm))` by
      (fs[Abbr`ls1`,Abbr`ls2`,word_list_APPEND]>>
       fs [AC STAR_COMM STAR_ASSOC]) >>
     qabbrev_tac`ls = ls1++ls2`>>
     CCONTR_TAC>>
     `dimword(:'a) ≤ LENGTH ls +1` by
       (unabbrev_all_tac>>fs[])>>
     `dimword(:'a) DIV d < LENGTH ls` by
       (
       DEP_REWRITE_TAC [DIV_LT_X]>>
       `2 < d ∧ 0 < LENGTH ls` by
         fs[Abbr`d`,good_dimindex_def]>>
       fs[]>>
       `LENGTH ls +1 < LENGTH ls * d` by
         (Cases_on`LENGTH ls`>>fs[ADD1]>>
         Cases_on`d`>>fs[ADD1])>>
       fs[])>>
     fs[Abbr`d`]>>
     Q.ISPECL_THEN [`ls`,`bitmap_ptr`] mp_tac (GEN_ALL word_list_wrap)>>
     impl_tac>-
       fs[]>>
     strip_tac>>
     ntac 2 (pop_assum mp_tac)>>simp[word_list_def]>>
     strip_tac>>
     pop_assum SUBST_ALL_TAC>>
     SEP_NEQ_TAC>>fs[])
   \\ simp [] \\ match_mp_tac word_list_exists_addresses \\ fs [])>>
  qpat_x_assum ‘_ (fun2set (m1,_))’ assume_tac>>
  qpat_x_assum ‘_ (fun2set (m4,_))’ assume_tac>>
  pop_assum mp_tac>>
  simp[Once STAR_ASSOC]>>
  simp[Once STAR_ASSOC]>>
  qmatch_goalsub_abbrev_tac ‘(r1 * word_list (n2w (d * h2)) heap * r2) (fun2set (_, _))’>>
  strip_tac>>drule word_list_in_memory>>gs[]>>
  ‘w2n (bytes_in_word:'a word) = d’
  by gs[byteTheory.bytes_in_word_def,Abbr ‘d’]>>
  ‘d * h2 + LENGTH heap * w2n (bytes_in_word:'a word) < dimword (:α)’
  by (irule LESS_TRANS>>
      qpat_assum ‘d  + _ < _’$ irule_at Any>>
      rewrite_tac[ADD_ASSOC]>>gs[])>>gs[]>>
  strip_tac>>
  qpat_x_assum ‘_ (fun2set (m1,_))’ mp_tac>>
  ntac 2 (simp[Once STAR_ASSOC])>>
  strip_tac>>drule word_list_in_memory>>gs[]>>
  strip_tac>>
  gs[memory_def]>>
  qpat_x_assum ‘_ = word_list _ heap’ mp_tac>>
  qpat_x_assum ‘_ = word_list _ heap’ mp_tac>>
  simp[Once FUN_EQ_THM]>>strip_tac>>
  simp[Once FUN_EQ_THM]>>strip_tac>>
  ‘word_list (n2w (d * h2)) heap
   (fun2set (m4,addresses (n2w (d * h2)) (LENGTH heap)))’
   by metis_tac[]>>
  gs[Abbr ‘m4’]>>

  ‘fun2set (m⦇a + n2w (d * LENGTH rest1) ↦ Word 0w⦈,
            addresses (n2w (d * h2)) (LENGTH heap)) =
   fun2set (m,addresses (n2w (d * h2)) (LENGTH heap))’
   by (rewrite_tac[set_sepTheory.fun2set_eq]>>
      strip_tac>>strip_tac>>
      gs[addresses_thm,UPDATE_def]>>IF_CASES_TAC>>gs[]>>
      gs[Abbr ‘a’]>>
      pop_assum $ mp_tac o GSYM>>
      ‘bytes_in_word :'a word = n2w d’
        by (qpat_x_assum ‘_ = d’ $ assume_tac o GSYM>>gs[])>>
      fs[]>>simp[wordsTheory.word_mul_n2w]>>
      simp[word_add_n2w]>>
      ‘d * i < d * LENGTH heap’ by gs[]>>
      ‘d * h2 + d * i < dimword (:'a)’
        by (irule LESS_TRANS>>
            qexists_tac ‘d * h2 + d * LENGTH heap’>>gs[])>>
      simp[])>>
  gs[]
QED

Definition make_init_opt_def:
  make_init_opt gen_gc max_heap bitmaps data_sp coracle jump off k code (s:('a,'c,'ffi)stackSem$state) =
    case evaluate (init_code gen_gc max_heap k,s) of
    | (SOME _,t) => NONE
    | (NONE,t) => if init_prop gen_gc max_heap data_sp
                       (get_stack_heap_limit max_heap (read_pointers s))
                       (init_reduce gen_gc jump off k code bitmaps data_sp coracle t)
                  then SOME (init_reduce gen_gc jump off k code bitmaps data_sp coracle t) else NONE
End

Definition init_pre_def:
  init_pre gen_gc max_heap bitmaps data_sp k start s <=>
    lookup 0 s.code = SOME (Seq (init_code gen_gc max_heap k)
                                (Call NONE (INL start) NONE)) /\
    init_code_pre k bitmaps data_sp s /\ max_stack_alloc ≤ max_heap
End

Theorem evaluate_init_code:
   init_pre gen_gc max_heap bitmaps data_sp k start s /\
    s.compile_oracle = ((I ## MAP (prog_comp jump off k) ## I) o coracle) /\
    (∀n i p. MEM (i,p) (FST(SND(coracle n))) ⇒ reg_bound p k ∧ num_stubs ≤ i+1) ∧
    lookup stack_err_lab s.code = SOME (halt_inst 2w) /\
    code_rel jump off k code s.code ==>
    case evaluate (init_code gen_gc max_heap k,s) of
    | (NONE,t) => ?r. make_init_opt gen_gc max_heap bitmaps data_sp coracle jump off k code s = SOME r /\
                      state_rel jump off k r t /\ t.ffi = s.ffi
    | _ => F
Proof
  strip_tac \\ fs [init_pre_def]
  \\ drule init_code_thm \\ fs []
  \\ impl_tac >- metis_tac[]
  \\ CASE_TAC \\ CASE_TAC
  \\ fs [make_init_opt_def]
  \\ strip_tac \\ fs[]
QED

Theorem clock_neutral_store_list_code:
   !xs n k. clock_neutral (store_list_code n k xs)
Proof
  Induct \\ fs [clock_neutral_def,store_list_code_def]
  \\ Cases \\ fs [clock_neutral_def,store_list_code_def,list_Seq_def]
QED

Triviality evaluate_init_code_clock:
  evaluate (init_code gen_gc max_heap k,s) = (res,t) ==>
    evaluate (init_code gen_gc max_heap k,s with clock := c) =
      (res,t with clock := c)
Proof
  srw_tac[][] \\ match_mp_tac evaluate_clock_neutral \\ fs []
  \\ fs [clock_neutral_def,init_code_def] \\ rw []
  \\ fs [clock_neutral_def,init_code_def,halt_inst_def,
         list_Seq_def,init_memory_def,clock_neutral_store_list_code]
QED

Theorem evaluate_init_code_ffi:
   evaluate (init_code gen_gc max_heap k,(s:('a,'c,'ffi) stackSem$state)) = (res,t) ==>
    evaluate (init_code gen_gc max_heap k,s with ffi := c) =
      (res,(t with ffi := c):('a,'c,'ffi) stackSem$state)
Proof
  srw_tac[][] \\ match_mp_tac evaluate_ffi_neutral \\ fs []
  \\ fs [clock_neutral_def,init_code_def] \\ rw []
  \\ fs [clock_neutral_def,init_code_def,halt_inst_def,
         list_Seq_def,init_memory_def,clock_neutral_store_list_code]
QED

Theorem init_semantics:
   lookup stack_err_lab s.code = SOME (halt_inst 2w) /\
    code_rel jump off k code s.code /\
    init_pre gen_gc max_heap bitmaps data_sp k start s ∧
    s.compile_oracle = ((I ## MAP (prog_comp jump off k) ## I) o coracle) /\
    (∀n i p. MEM (i,p) (FST(SND(coracle n))) ⇒ reg_bound p k ∧ num_stubs ≤ i+1)
    ==>
    case evaluate (init_code gen_gc max_heap k,s) of
    | (NONE,t) =>
        (semantics 0 s = semantics start t) /\
        ?r. make_init_opt gen_gc max_heap bitmaps data_sp coracle jump off k code s = SOME r /\
            state_rel jump off k r t
    | _ => F
Proof
  srw_tac[][]
  \\ qhdtm_x_assum`init_pre` (fn th => assume_tac th \\ mp_tac th)
  \\ simp_tac std_ss [init_pre_def] \\ rw []
  \\ imp_res_tac evaluate_init_code
  \\ every_case_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[semantics_def |> Q.SPEC `0`,LET_DEF]
  \\ once_rewrite_tac [evaluate_def] \\ full_simp_tac(srw_ss())[find_code_def]
  \\ once_rewrite_tac [evaluate_def] \\ full_simp_tac(srw_ss())[LET_DEF]
  \\ full_simp_tac(srw_ss())[dec_clock_def]
  \\ imp_res_tac evaluate_init_code_clock \\ full_simp_tac(srw_ss())[]
  \\ pop_assum (K all_tac)
  \\ full_simp_tac(srw_ss())[semantics_def,LET_DEF]
  \\ match_mp_tac (METIS_PROVE []
      ``x1 = x2 /\ (x1 /\ x2 ==> y1 = y2) /\ (~x1 /\ ~x2 ==> z1 = z2) ==>
        (if x1 then y1 else z1) = (if x2 then y2 else z2)``)
  \\ conj_tac \\ full_simp_tac(srw_ss())[] THEN1
   (EQ_TAC \\ strip_tac THEN1
     (Cases_on `k' = 0` \\ full_simp_tac(srw_ss())[]
      \\ qexists_tac `k'-1` \\ full_simp_tac(srw_ss())[]
      \\ every_case_tac \\ full_simp_tac(srw_ss())[])
    \\ qexists_tac `k' + 1` \\ full_simp_tac(srw_ss())[]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[])
  \\ strip_tac
  \\ match_mp_tac (METIS_PROVE []
      ``x1 = x2 /\ y1 = y2 /\ z1 = z2 ==> f x1 y1 z1 = f x2 y2 z2``)
  \\ conj_tac \\ full_simp_tac(srw_ss())[] THEN1
   (AP_TERM_TAC \\ full_simp_tac(srw_ss())[FUN_EQ_THM]
    \\ srw_tac[][] \\ reverse EQ_TAC \\ strip_tac
    THEN1 (qexists_tac `k' + 1` \\ full_simp_tac(srw_ss())[])
    \\ qexists_tac `k' - 1` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `k' = 0` \\ full_simp_tac(srw_ss())[]
     THEN1 (srw_tac[][] \\ full_simp_tac(srw_ss())[empty_env_def]
            \\ rev_full_simp_tac(srw_ss())[])
    \\ Cases_on `evaluate (Call NONE (INL start) NONE,r with clock := k' - 1)`
    \\ full_simp_tac(srw_ss())[] \\ Cases_on `q`
    \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ first_x_assum (qspec_then`k'-1`mp_tac) \\ full_simp_tac(srw_ss())[])
  \\ AP_TERM_TAC \\ full_simp_tac(srw_ss())[EXTENSION]
  \\ srw_tac[][] \\ reverse EQ_TAC \\ strip_tac
  THEN1 (full_simp_tac(srw_ss())[] \\ qexists_tac `k' + 1`
         \\ full_simp_tac(srw_ss())[] \\ every_case_tac
         \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[] \\ qexists_tac `k' - 1`
  \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `k' = 0` \\ full_simp_tac(srw_ss())[]
  THEN1 (full_simp_tac(srw_ss())[evaluate_def,empty_env_def]
         \\ every_case_tac \\ full_simp_tac(srw_ss())[])
  \\ every_case_tac \\ full_simp_tac(srw_ss())[]
QED

Theorem make_init_opt_SOME_semantics:
   init_pre gen_gc max_heap bitmaps data_sp k start s2 /\
    s2.compile_oracle = ((I ## MAP (prog_comp jump off k) ## I) o coracle) /\
    (∀n i p. MEM (i,p) (FST(SND(coracle n))) ⇒ reg_bound p k ∧ num_stubs ≤ i+1) ∧
    code_rel jump off k code s2.code /\
    lookup stack_err_lab s2.code = SOME (halt_inst 2w) ==>
    ?s1.
      make_init_opt gen_gc max_heap bitmaps data_sp coracle jump off k code s2 = SOME s1 /\
      (semantics start s1 <> Fail ==>
       semantics 0 s2 = semantics start s1)
Proof
  srw_tac[][] \\ imp_res_tac init_semantics \\ pop_assum (assume_tac o SPEC_ALL)
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ fs [] \\ rw []
  \\ match_mp_tac (GEN_ALL compile_semantics)
  \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ metis_tac []
QED

Triviality IMP_code_rel:
  EVERY (\(n,p). reg_bound p k /\ num_stubs ≤ n+1) code1 /\
   code2 = fromAList (compile jump off gen_gc max_heap k start code1) ==>
   code_rel jump off k (fromAList code1) code2
Proof
  rw[]>>
  fs[code_rel_def,lookup_fromAList]>>
  CONJ_TAC>- (
    fs[ALOOKUP_def,compile_def,init_stubs_def] \\ rw []
    \\ rpt var_eq_tac
    \\ imp_res_tac ALOOKUP_MEM
    \\ imp_res_tac EVERY_MEM \\ full_simp_tac(srw_ss())[]
    \\ simp[prog_comp_eta,ALOOKUP_MAP_2]
    \\ pop_assum mp_tac \\ EVAL_TAC)>>
  simp[domain_fromAList,compile_def,init_stubs_def,prog_comp_eta,MAP_MAP_o,UNCURRY,o_DEF,ETA_AX]>>
  simp[EXTENSION]>>
  metis_tac[]
QED

Definition make_init_any_def:
  make_init_any gen_gc max_heap bitmaps data_sp coracle jump off k code s =
    case make_init_opt gen_gc max_heap bitmaps data_sp coracle jump off k code s of
    | SOME t => t
    | NONE => s with <| regs := FEMPTY |+ (0,Loc 1 0)
                      ; fp_regs := FEMPTY
                      ; mdomain := EMPTY
                      ; bitmaps := [4w]
                      ; use_stack := T
                      ; use_store := T
                      ; use_alloc := F
                      ; stack := [Word 0w]
                      ; stack_space := 0
                      ; compile := (λc p. s.compile c (MAP (prog_comp jump off k) p))
                      ; compile_oracle := coracle
                      ; data_buffer := <|buffer := []; position := 0w; space_left := 0|>
                      ; code_buffer := <|buffer := []; position := 0w; space_left := 0|>
                      ; code := code
                      ; store := FEMPTY |++ (MAP (\x. (x,Word 0w))
                                   (CurrHeap::store_list)) |>
End

Definition discharge_these_def:
  discharge_these jump off gen_gc max_heap k start coracle code s2 ⇔
      EVERY (\(n,p). reg_bound p k /\ num_stubs ≤ n+1) code /\
      (∀n i p.
        MEM (i,p) (FST (SND (coracle n))) ⇒ reg_bound p k ∧ num_stubs ≤ i + 1) ∧
      s2.compile_oracle = (I ## MAP (prog_comp jump off k) ## I) ∘ coracle ∧
      s2.code = fromAList (compile jump off gen_gc max_heap k start code) ∧
      8 ≤ k ∧ 1 ∈ domain s2.code ∧
      {k; k + 1; k + 2} ⊆ s2.ffi_save_regs ∧ ¬s2.use_stack ∧
      ¬s2.use_store ∧ ¬s2.use_alloc ∧ max_stack_alloc <= max_heap
End

Definition propagate_these_def:
  propagate_these s (bitmaps:'a word list) data_sp ⇔
  good_dimindex(:'a) /\
  ∃ptr2 ptr3 ptr4 bitmap_ptr.
       FLOOKUP s.regs 2 = SOME (Word ptr2) ∧
       FLOOKUP s.regs 3 = SOME (Word ptr3) ∧
       FLOOKUP s.regs 4 = SOME (Word ptr4) ∧
       s.memory ptr2 = Word bitmap_ptr ∧
       s.memory (ptr2 + bytes_in_word) =
           Word (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps)) ∧
       s.memory (ptr2 + 2w * bytes_in_word) =
           Word (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps) +
                              bytes_in_word * n2w data_sp) ∧
       s.memory (ptr2 + 3w * bytes_in_word) =
         Word s.code_buffer.position ∧
       s.memory (ptr2 + 4w * bytes_in_word) =
         Word (s.code_buffer.position + n2w s.code_buffer.space_left) ∧
       s.code_buffer.buffer = [] /\
       ptr2 <=+ ptr4 /\
       byte_aligned ptr2 ∧ byte_aligned ptr4 /\ byte_aligned bitmap_ptr /\
       1024w * bytes_in_word <=+ ptr4 - ptr2 /\
       (word_list bitmap_ptr (MAP Word bitmaps) *
        word_list_exists (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps)) data_sp *
        word_list_exists ptr2
            (w2n (-1w * ptr2 + ptr4) DIV w2n (bytes_in_word:'a word)))
         (fun2set (s.memory,s.mdomain))
End

Theorem make_init_semantics:
   discharge_these jump off gen_gc max_heap k start coracle code s2 /\
   propagate_these s2 bitmaps data_sp ==>
   ?s1.
     make_init_opt gen_gc max_heap (bitmaps:'a word list) data_sp coracle jump off k (fromAList code) s2 = SOME s1 /\
     (semantics start s1 <> Fail
      ==>
      semantics 0 s2 = semantics start s1)
Proof
  rw[discharge_these_def]
  \\ match_mp_tac (GEN_ALL make_init_opt_SOME_semantics)
  \\ imp_res_tac IMP_code_rel
  \\ fs[init_pre_def,init_code_pre_def,propagate_these_def]
  \\ simp[lookup_fromAList,compile_def,ALOOKUP_APPEND]
  \\ conj_tac THEN1 EVAL_TAC
  \\ conj_tac THEN1 metis_tac []
  \\ EVAL_TAC
QED

Theorem make_init_any_ffi:
   (make_init_any gen_gc max_heap bitmaps data_sp coracle jump off k code s).ffi =
    (s:('a,'c,'ffi) stackSem$state).ffi
Proof
  fs [make_init_any_def,make_init_opt_def,init_reduce_def]
  \\ every_case_tac \\ fs []
  \\ imp_res_tac evaluate_init_code_ffi
  \\ pop_assum (qspec_then `s.ffi` mp_tac)
  \\ `s with ffi := s.ffi = s` by fs [state_component_equality]
  \\ fs [] \\ fs [state_component_equality]
QED

Theorem make_init_any_bitmaps:
   (make_init_any gen_gc max_heap bitmaps data_sp coracle jump off k code s).bitmaps =
       if IS_SOME (make_init_opt gen_gc max_heap bitmaps data_sp coracle jump off k code s)
       then bitmaps else [4w]
Proof
  fs [make_init_any_def,make_init_opt_def,init_reduce_def]
  \\ every_case_tac \\ fs []
QED

Theorem make_init_any_use_stack:
   (make_init_any gen_gc max_heap bitmaps data_sp coracle jump off k code s).use_stack
Proof
  fs [make_init_any_def,make_init_opt_def,init_reduce_def]
  \\ every_case_tac \\ fs []
QED

Theorem make_init_any_use_store:
   (make_init_any gen_gc max_heap bitmaps data_sp coracle jump off k code s).use_store
Proof
  fs [make_init_any_def,make_init_opt_def,init_reduce_def]
  \\ every_case_tac \\ fs []
QED

Theorem make_init_any_use_alloc:
   ~(make_init_any gen_gc max_heap bitmaps data_sp coracle jump off k code s).use_alloc
Proof
  fs [make_init_any_def,make_init_opt_def,init_reduce_def]
  \\ every_case_tac \\ fs []
QED

Theorem make_init_any_code:
   (make_init_any gen_gc max_heap bitmaps data_sp coracle jump off k code s).code = code
Proof
  fs [make_init_any_def,make_init_opt_def,init_reduce_def]
  \\ every_case_tac \\ fs []
QED

Theorem make_init_any_stack_limit:
   LENGTH ((make_init_any gen_gc max_heap (bitmaps:'a word list) data_sp coracle jump off k code s).stack) *
      (dimindex (:'a) DIV 8) < dimword (:'a)
Proof
  fs [make_init_any_def]
  \\ reverse (every_case_tac \\ fs [LENGTH_read_mem])
  \\ fs [make_init_opt_def]
  \\ reverse (every_case_tac \\ fs [LENGTH_read_mem])
  \\ fs [init_prop_def] \\ fs [dimword_def] \\ fs [DIV_LT_X]
  \\ match_mp_tac LESS_EQ_LESS_TRANS
  \\ qexists_tac `8 * dimindex (:'a)` \\ fs []
  \\ fs [X_LT_EXP_X_IFF]
QED

Theorem make_init_any_compile_oracle:
   (make_init_any ggc max_heap bitmaps data_sp coracle jump off k code s).compile_oracle = coracle
Proof
  fs [make_init_any_def,make_init_opt_def,init_reduce_def]
  \\ every_case_tac \\ fs []
QED

(*
Theorem make_init_any_data_buffer:
   (make_init_any ggc max_heap bitmaps data_sp coracle jump off k code s).data_buffer =
    the correct thing on the success branch (which needs to be set on the fail branch too)
Proof
  fs [make_init_any_def,make_init_opt_def,init_reduce_def]
  \\ every_case_tac \\ fs []
QED
*)

(* Syntactic *)

Theorem FST_prog_comp[simp]:
   FST (prog_comp jump off k pp) = FST pp
Proof
  Cases_on`pp` \\ EVAL_TAC
QED

Theorem stack_remove_lab_pres:
  ∀jump off k p.
    extract_labels p = extract_labels (comp jump off k p)
Proof
  ho_match_mp_tac comp_ind>>Cases_on`p`>>rw[]>>
  once_rewrite_tac [comp_def]>>fs[extract_labels_def]>>
  TRY(IF_CASES_TAC)>>
  fs[extract_labels_def,stack_store_def,stack_load_def]
  >- (BasicProvers.EVERY_CASE_TAC>>fs[])
  >- EVAL_TAC
  >-
    (qid_spec_tac`n`>>completeInduct_on`n`>>rw[Once stack_alloc_def]>>
    fs[single_stack_alloc_def]>> rw[]>> fs[ extract_labels_def,halt_inst_def]>>
    first_assum match_mp_tac>>
    fs[max_stack_alloc_def])
  >-
    (qid_spec_tac`n`>>completeInduct_on`n`>>rw[Once stack_free_def]>>
    fs[extract_labels_def,single_stack_free_def]>>
    first_assum match_mp_tac>>
    fs[max_stack_alloc_def])
  >-
    (pop_assum kall_tac>>rw[]>>completeInduct_on`n0`>>rw[Once upshift_def,Once downshift_def]>>
    fs[extract_labels_def]>>
    first_assum match_mp_tac>>
    fs[max_stack_alloc_def])
  >-
    (pop_assum kall_tac>>rw[]>>completeInduct_on`n0`>>rw[Once upshift_def,Once downshift_def]>>
    fs[extract_labels_def]>>
    first_assum match_mp_tac>>
    fs[max_stack_alloc_def])
  >- EVAL_TAC
QED

Theorem stack_remove_comp_stack_asm_name:
  ∀jump off k p.
    stack_asm_name c p ∧ stack_asm_remove (c:'a asm_config) p ∧
    addr_offset_ok c 0w ∧
    good_dimindex (:'a) ∧
    (∀n. n ≤ max_stack_alloc ⇒
    c.valid_imm (INL Sub) (n2w (n * (dimindex (:'a) DIV 8))) ∧
    c.valid_imm (INL Add) (n2w (n * (dimindex (:'a) DIV 8)))) ∧
    (* Needed to implement the global store *)
    (∀s. addr_offset_ok c (store_offset s)) ∧
    reg_name (k+2) c ∧
    reg_name (k+1) c ∧
    reg_name k c ∧ k ≠ 0 ∧
    off = c.addr_offset ⇒
    stack_asm_name c (comp jump off k p)
Proof
  ho_match_mp_tac comp_ind>>Cases_on`p`>>rw[]>>
  simp[Once comp_def]>>
  rw[]>>
  fs[stack_asm_name_def,inst_name_def,stack_asm_remove_def,addr_name_def,
     arith_name_def,reg_imm_name_def,stackLangTheory.list_Seq_def]
  >-
    (every_case_tac>>fs[])
  >-
   (fs [copy_loop_def,list_Seq_def,stack_asm_name_def,copy_each_def,
        inst_name_def,arith_name_def,reg_name_def,reg_imm_name_def,addr_name_def] >>
    ‘1 <= max_stack_alloc’ by EVAL_TAC >>
    res_tac >> fs [bytes_in_word_def] >>
    gvs [good_dimindex_def,word_shift_def])
  >-
    (* stack alloc *)
    (completeInduct_on`n`>>
    simp[Once stack_alloc_def]>>rw[]
    >-
      EVAL_TAC
    >-
      (EVAL_TAC>>rw[]>>EVAL_TAC>>fs[reg_name_def])
    >>
      rw[stack_asm_name_def]
      >-
        (EVAL_TAC>>rw[]>>EVAL_TAC>>fs[reg_name_def,max_stack_alloc_def])
      >>
        first_x_assum(qspec_then `n-max_stack_alloc` assume_tac)>>fs[]>>
        rfs[max_stack_alloc_def])
  >- (* stack free *)
    (completeInduct_on`n`>>
    simp[Once stack_free_def]>>rw[]
    >-
      EVAL_TAC
    >-
      (EVAL_TAC>>fs[reg_name_def])
    >>
      rw[stack_asm_name_def]
      >-
        (EVAL_TAC>>fs[reg_name_def,max_stack_alloc_def])
      >>
        first_x_assum(qspec_then `n-max_stack_alloc` assume_tac)>>fs[]>>
        rfs[max_stack_alloc_def])
  >>
    fs[good_dimindex_def,word_shift_def]
  >>
    simp[stack_load_def,stack_store_def,stack_asm_name_def,inst_name_def,addr_name_def]>>
    qpat_assum`!n. A ⇒ B` mp_tac>>
    rpt(qpat_x_assum`reg_name _ c` mp_tac)>>
    rpt (pop_assum kall_tac)>>
    rw[]>>completeInduct_on`n0`>>
    simp[Once upshift_def,Once downshift_def]>>rw[]>>
    fs[stack_asm_name_def,inst_name_def,arith_name_def,reg_imm_name_def,word_offset_def]>>
    first_x_assum match_mp_tac>>fs[max_stack_alloc_def]
QED

Theorem stack_remove_stack_asm_name:
    EVERY (λ(n,p). stack_asm_name c p) prog ∧
  EVERY (λ(n,p). (stack_asm_remove (c:'a asm_config) p)) prog ∧
  addr_offset_ok c 0w ∧
  good_dimindex (:'a) ∧
  (∀n. n ≤ max_stack_alloc ⇒
  c.valid_imm (INL Sub) (n2w (n * (dimindex (:'a) DIV 8))) ∧
  c.valid_imm (INL Add) (n2w (n * (dimindex (:'a) DIV 8)))) ∧
  c.valid_imm (INL Add) 4w ∧
  c.valid_imm (INL Add) 8w ∧
  (* Needed to implement the global store *)
  (∀s. addr_offset_ok c (store_offset s)) ∧
  reg_name 7 c ∧
  reg_name (k+2) c ∧
  reg_name (k+1) c ∧
  reg_name k c ∧ k ≠ 0 ⇒
  EVERY (λ(n,p). stack_asm_name c p)
  (compile jump c.addr_offset gen_gc max_heap k start prog)
Proof
  rw[compile_def]
  >-
    (fs[good_dimindex_def]>>EVAL_TAC>>fs[]>>rw[]>>EVAL_TAC>>fs[reg_name_def]>>
    pairarg_tac>>fs[asmTheory.offset_ok_def]>>
    Induct_on`bitmaps`>>rw[]>>
    EVAL_TAC>>fs[])
  >>
    fs[EVERY_MAP,EVERY_MEM,FORALL_PROD,prog_comp_def]>>
    metis_tac[stack_remove_comp_stack_asm_name]
QED

Theorem upshift_downshift_call_args:
    ∀n n0.
  call_args (upshift n n0) 1 2 3 4 0 ∧
  call_args (downshift n n0) 1 2 3 4 0
Proof
  completeInduct_on`n0`>>
  simp[Once stack_removeTheory.upshift_def,Once stack_removeTheory.downshift_def]>>
  strip_tac>>IF_CASES_TAC>>
  fs[call_args_def]>>
  first_assum match_mp_tac>>EVAL_TAC>>fs[]
QED

Theorem stack_remove_call_args:
   compile jump off gen_gc n k pos p = p' /\
    EVERY (λp. call_args p 1 2 3 4 0) (MAP SND p) ==>
    EVERY (λp. call_args p 1 2 3 4 0) (MAP SND p')
Proof
  rw[]>>
  unabbrev_all_tac>>fs[]>>
  EVAL_TAC>>
  fs[EVERY_MAP,EVERY_MEM,FORALL_PROD,stack_removeTheory.prog_comp_def]>>
  rw[]>>res_tac>>
  pop_assum mp_tac>> rpt (pop_assum kall_tac)>>
  map_every qid_spec_tac[`p_2`,`k`,`off`,`jump`]>>
  ho_match_mp_tac stack_removeTheory.comp_ind>>
  Cases_on`p_2`>>rw[]>>
  ONCE_REWRITE_TAC [stack_removeTheory.comp_def]>>
  fs[call_args_def]>>
  TRY(IF_CASES_TAC>>fs[call_args_def])
  >-
    (BasicProvers.EVERY_CASE_TAC>>fs[])
  >- EVAL_TAC
  >>
  TRY (* stack_alloc and stack_free *)
    (completeInduct_on`n`>>simp[Once stack_removeTheory.stack_alloc_def,stack_removeTheory.single_stack_alloc_def,
       Once stack_removeTheory.stack_free_def,stack_removeTheory.single_stack_free_def,stack_removeTheory.halt_inst_def]>>
    rpt (IF_CASES_TAC>>fs[call_args_def])>>
    first_assum match_mp_tac>>
    EVAL_TAC>>fs[]>>NO_TAC)>>
  simp[stack_removeTheory.stack_store_def,stack_removeTheory.stack_load_def,call_args_def,upshift_downshift_call_args]
  >- EVAL_TAC
QED

val _ = export_theory();

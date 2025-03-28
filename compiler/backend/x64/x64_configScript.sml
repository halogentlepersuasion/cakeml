(*
  Define the compiler configuration for x64
*)
open preamble backendTheory x64_targetTheory x64_targetLib

val _ = new_theory"x64_config";

Definition x64_names_def:
  x64_names =
    (* 16 regs, must avoid 4 and 5, names:
         r0=rax, r1=rcx, r2=rdx, r3=rbx, r4=rbp, r5=rsp, r6=rsi,
         r7=rdi, r8=r8, r9, r10, r11, r12, r13, r14, r15
       The first six arguments are passed in registers. The first
       argument (1) is passed in rdi(r7), the second(2) in rsi(r6),
       the third(3) in rdx(r3), the fourth(4) in rcx(2), the fifth(5)
       in r8 and the sixth in r9.
       Callee-saved regs: r12-r15, rbx
     *)
    (insert 1 7 o  (* arg 1 *)
     insert 2 6 o  (* arg 2 *)
     insert 3 2 o
     insert 4 1 o
     insert 5 8 o
     insert 6 9 o
     insert 11 14 o
     insert 12 13 o
     insert 13 12 o
     (* the rest just ensures that the mapping is well-formed *)
     insert 7 3 o
     insert 8 15 o
     insert 9 11 o
     insert 14 4 o
     insert 15 5) LN:num num_map
End

Theorem x64_names_def[compute,allow_rebind] =
  CONV_RULE (RAND_CONV EVAL) x64_names_def

val clos_conf = rconc (EVAL ``clos_to_bvl$default_config``)
val bvl_conf = rconc (EVAL``bvl_to_bvi$default_config``)
val word_to_word_conf = ``<| reg_alg:=2; col_oracle := [] |>``

val x64_data_conf = ``<| tag_bits:=4; len_bits:=4; pad_bits:=2; len_size:=32; has_div:=F; has_longdiv:=T; has_fp_ops:=T; has_fp_tern:=F; be:=F; call_empty_ffi:=F; gc_kind:=Simple|>``
val x64_word_conf = ``<| bitmaps_length := 0; stack_frame_size := LN |>``
val x64_stack_conf = ``<|jump:=T;reg_names:=x64_names|>``
val x64_lab_conf = ``<|pos:=0;ffi_names:=NONE;labels:=LN;sec_pos_len:=[];asm_conf:=x64_config;init_clock:=5;hash_size:=104729n;shmem_extra:=[]|>``

Definition x64_backend_config_def:
  x64_backend_config =
             <|source_conf:=prim_src_config;
               clos_conf:=^(clos_conf);
               bvl_conf:=^(bvl_conf);
               data_conf:=^(x64_data_conf);
               word_to_word_conf:=^(word_to_word_conf);
               word_conf:=^(x64_word_conf);
               stack_conf:=^(x64_stack_conf);
               lab_conf:=^(x64_lab_conf);
               symbols:=[];
               tap_conf:=default_tap_config;
               exported:=[]
               |>
End

val _ = export_theory();

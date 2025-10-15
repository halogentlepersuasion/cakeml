(*
  Semantics of panLang
*)
Theory panSem
Ancestors
  panLang alignment[qualified] finite_map[qualified]
  misc[qualified] (* for read_bytearray *)
  wordLang[qualified] (* for word_op and word_sh *)
  ffi[qualified]
  lprefix_lub[qualified]
Libs
  preamble


(* TODO: rename or remove *)
Datatype:
  word_lab = Word ('a word)
End

Datatype:
  v = Val ('a word_lab)
    | RStruct (v list)
    | NStruct stcname ((fldname # v) list)
End

Overload ValWord  = “\w. Val (Word w)”

Datatype:
  state =
    <| locals      : varname |-> 'a v
     ; globals     : varname |-> 'a v
     ; structs     : (stcname # struct_info) list
     ; code        : funname |-> ((varname # shape) list # ('a panLang$prog))
                     (* arguments (with shape), body *)
     ; eshapes     : eid |-> shape
     ; memory      : 'a word -> 'a word_lab
     ; memaddrs    : ('a word) set
     ; sh_memaddrs    : ('a word) set
     ; clock       : num
     ; be          : bool
     ; ffi         : 'ffi ffi_state
     ; base_addr   : 'a word
     ; top_addr   : 'a word
  (* ; gaddrs      : decname |-> ('a word) (* num? *) *)
  (* TODISC: this maps decname to its starting address in the memory and relative size *)|>
End

val state_component_equality = theorem"state_component_equality";

Datatype:
  result = Error
         | TimeOut
         | Break
         | Continue
         | Return    ('a v)
         | Exception mlstring ('a v)
         | FinalFFI final_event
End

val s = ``(s:('a,'ffi) panSem$state)``

Definition shape_of_def:
  shape_of (ValWord _) = One /\
  shape_of (RStruct vs) = Comb (MAP shape_of vs) /\
  shape_of (NStruct nm _) = Named nm
End

Definition mem_load_byte_def:
  mem_load_byte m dm be w =
  case m (byte_align w) of
    | Word v =>
       if byte_align w IN dm
       then SOME (get_byte w v be) else NONE
End

Definition mem_load_32_def:
  (* returns 32 word, first or second half of w if a = 64 *)
  mem_load_32 m dm be (w:'a word) =
  if aligned 2 w
  then
    case m (byte_align w) of
    | Word v =>
        if byte_align w IN dm
        then
          let b0 = get_byte w v be in
          let b1 = get_byte (w + 1w) v be in
          let b2 = get_byte (w + 2w) v be in
          let b3 = get_byte (w + 3w) v be in
          let v' =
              (if be
               then
                 (w2w b0) ≪ 24 ‖ (w2w b1) ≪ 16 ‖ (w2w b2) ≪ 8 ‖ (w2w b3)
               else
                 (w2w b0) ‖ (w2w b1) ≪ 8 ‖ (w2w b2) ≪ 16 ‖ (w2w b3) ≪ 24)
          in SOME (v': word32)
        else NONE
  else NONE
End

Definition mem_load_def:
  (mem_load sh addr dm (m: 'a word -> 'a word_lab) stcs =
   case sh of
   | One =>
     if addr IN dm
     then SOME (Val (m addr))
     else NONE
   | Comb shapes =>
     (case mem_loads shapes addr dm m stcs of
      | SOME vs => SOME (RStruct vs)
      | NONE => NONE)
   | Named nm =>
     (case dropWhile (\(n,i). ~(n = nm)) stcs of
      | (nm,info)::stcs' =>
          (case mem_load_flds info.fields addr dm m stcs' of
            | SOME vflds => SOME (NStruct nm vflds)
            | NONE => NONE)
      | _ => NONE)) /\
  (mem_loads [] addr dm m stcs = SOME []) /\
  (mem_loads (shape::shapes) addr dm m stcs =
   case (mem_load shape addr dm m stcs,
         mem_loads shapes (addr + bytes_in_word * n2w (size_of_sh_with_ctxt stcs shape)) dm m stcs) of
    | SOME v, SOME vs => SOME (v :: vs)
    | _ => NONE) /\
  (mem_load_flds [] addr dm m stcs = SOME []) /\
  (mem_load_flds ((fld,shape)::fields) addr dm m stcs =
   case (mem_load shape addr dm m stcs,
         mem_load_flds fields (addr + bytes_in_word * n2w (size_of_sh_with_ctxt stcs shape)) dm m stcs) of
    | SOME v, SOME vflds => SOME ((fld,v) :: vflds)
    | _ => NONE)
Termination
  wf_rel_tac
    ‘inv_image
      (* lexicographic combination of (struct info list size, shape/s size): *)
      (measure LENGTH
      LEX measure
        (\x. case x of
          | INL x => shape_size x
          | INR x => list_size shape_size x))
      (* getting pair from args: *)
      (\x. case x of
        | INL x => (SND $ SND $ SND $ SND x, INL $ FST x)
        | INR(INL x) => (SND $ SND $ SND $ SND x, INR $ FST x)
        | INR(INR x) => (SND $ SND $ SND $ SND x, INR $ MAP SND $ FST x))’ >>
  rw [] >>
  disj1_tac >>
  irule LESS_LESS_EQ_TRANS >>
  irule_at Any LENGTH_dropWhile_LESS_EQ >>
  qmatch_asmsub_abbrev_tac `dropWhile ff` >>
  qexists `ff` >>
  rw []
End

Definition pan_op_def:
  pan_op Mul [w1:'a word;w2] = SOME(w1 * w2) ∧
  pan_op _ _ = NONE
End

Definition eval_def:
  (eval ^s (Const w) = SOME (ValWord w)) /\
  (eval s  (Var Local v) = FLOOKUP s.locals v) /\
  (eval s  (Var Global v) = FLOOKUP s.globals v) /\
  (eval s (RStruct es) =
    case (OPT_MMAP (eval s) es) of
     | SOME vs => SOME (RStruct vs)
     | NONE => NONE) /\
  (eval s (RField index e) =
    case eval s e of
     | SOME (RStruct vs) =>
       if index < LENGTH vs then SOME (EL index vs)
       else NONE
     | _ => NONE) /\
  (eval s (NStruct nm eflds) =
    let (field_names, field_exps) = UNZIP eflds in
    (case ALOOKUP s.structs nm of
      | SOME info =>
        let (field_names', field_shapes) = UNZIP info.fields in
        if field_names' = field_names then
          case (OPT_MMAP (eval s) field_exps) of
          | SOME field_vals =>
            if EVERY (\(s,v). s = shape_of v) (ZIP (field_shapes, field_vals)) then
              SOME (NStruct nm (ZIP (field_names, field_vals)))
            else NONE
          | NONE => NONE
        else NONE
      | NONE => NONE)) /\
  (eval s (NField fld e) =
    case eval s e of
     | SOME (NStruct nm vflds) =>
       ALOOKUP vflds fld
     | _ => NONE) /\
  (eval s (Load shape addr) =
    if is_wf_shape s.structs shape then
      case eval s addr of
      | SOME (ValWord w) => mem_load shape w s.memaddrs s.memory s.structs
      | _ => NONE
    else NONE) /\
  (eval s (Load32 addr) =
    case eval s addr of
     | SOME (ValWord w) =>
        (case mem_load_32 s.memory s.memaddrs s.be w of
           | NONE => NONE
           | SOME w => SOME (ValWord (w2w w)))
        | _ => NONE) /\
  (eval s (LoadByte addr) =
    case eval s addr of
     | SOME (ValWord w) =>
        (case mem_load_byte s.memory s.memaddrs s.be w of
           | NONE => NONE
           | SOME w => SOME (ValWord (w2w w)))
        | _ => NONE) /\
  (eval s (Op op es) =
    case (OPT_MMAP (eval s) es) of
     | SOME ws =>
       if (EVERY (\w. case w of (ValWord _) => T | _ => F) ws)
       then OPTION_MAP ValWord
            (word_op op (MAP (\w. case w of ValWord n => n) ws)) else NONE
      | _ => NONE) /\
  (eval s (Panop op es) =
    case (OPT_MMAP (eval s) es) of
     | SOME ws =>
       if (EVERY (\w. case w of (ValWord _) => T | _ => F) ws)
       then OPTION_MAP ValWord
            (pan_op op (MAP (\w. case w of ValWord n => n) ws)) else NONE
      | _ => NONE) /\
  (eval s (Cmp cmp e1 e2) =
    case (eval s e1, eval s e2) of
     | (SOME (ValWord w1), SOME (ValWord w2)) =>
          SOME (ValWord (if word_cmp cmp w1 w2 then 1w else 0w))
     | _ => NONE) /\
  (eval s (Shift sh e n) =
    case eval s e of
     | SOME (ValWord w) => OPTION_MAP ValWord (word_sh sh w n)
     | _ => NONE) /\
  (eval s BaseAddr =
        SOME (ValWord s.base_addr)) /\
  (eval s TopAddr =
        SOME (ValWord s.top_addr)) /\
  (eval s BytesInWord =
        SOME (ValWord bytes_in_word))
Termination
  wf_rel_tac `measure (exp_size ARB o SND)`
  \\ rpt strip_tac \\ gs [UNZIP_MAP]
  \\ fs [MEM_SPLIT, MAP_EQ_APPEND, list_size_append, EXISTS_PROD, MAP_EQ_CONS]
End

(* TODISC: why NONE is returned here on write failure *)
Definition mem_store_byte_def:
  mem_store_byte m dm be w b =
  case m (byte_align w) of
   | Word v =>
     if byte_align w IN dm
     then SOME ((byte_align w =+ Word (set_byte w b v be)) m)
     else NONE
End

Definition write_bytearray_def:
  (write_bytearray a [] m dm be = m) /\
  (write_bytearray a (b::bs) m dm be =
     case mem_store_byte (write_bytearray (a+1w) bs m dm be) dm be a b of
     | SOME m => m
     | NONE => m)
End

(*
Definition write_bytearray_def:
  (write_bytearray a [] m dm be = SOME m) /\
  (write_bytearray a (b::bs) m dm be =
     case mem_store_byte m dm be a b of
     | SOME m => write_bytearray (a+1w) bs m dm be
     | NONE => NONE)
End
*)

Definition mem_store_32_def:
  (* takes a 32 word *)
  mem_store_32 m dm be (w:'a word) (hw:word32) =
  if aligned 2 w
  then
    case m (byte_align w) of
    | Word v =>
        if byte_align w IN dm
        then
          if be
          then
            let v0 = set_byte w (w2w (hw ⋙  24)) v be in
            let v1 = set_byte (w + 1w) (w2w (hw ⋙  16)) v0 be in
            let v2 = set_byte (w + 2w) (w2w (hw ⋙  8)) v1 be in
            let v3 = set_byte (w + 3w) (w2w hw) v2 be in
              SOME ((byte_align w =+ Word v3) m)
          else
            let v0 = set_byte w (w2w hw) v be in
            let v1 = set_byte (w + 1w) (w2w (hw ⋙  8)) v0 be in
            let v2 = set_byte (w + 2w) (w2w (hw ⋙  16)) v1 be in
            let v3 = set_byte (w + 3w) (w2w (hw ⋙  24)) v2 be in
              SOME ((byte_align w =+ Word v3) m)
        else NONE
  else NONE
End

Definition mem_store_def:
  mem_store (addr:'a word) (w:'a word_lab) dm m =
    if addr IN dm then
    SOME ((addr =+ w) m)
    else NONE
End

Definition mem_stores_def:
  (mem_stores a [] dm m = SOME m) /\
  (mem_stores a (w::ws) dm m =
   case mem_store a w dm m of
    | SOME m' => mem_stores (a + bytes_in_word) ws dm m'
    | NONE => NONE)
End

Definition flatten_def:
  (flatten (Val w) = [w]) ∧
  (flatten (RStruct vs) = FLAT (MAP flatten vs)) ∧
  (flatten (NStruct nm flds) = FLAT (MAP flatten (MAP SND flds)))
Termination
  wf_rel_tac `measure (v_size ARB)`
  \\ rpt strip_tac
  \\ fs [MEM_SPLIT, MAP_EQ_APPEND, list_size_append, EXISTS_PROD, MAP_EQ_CONS]
End

Definition set_var_def:
  set_var v value ^s =
    (s with locals := s.locals |+ (v,value))
End

Definition set_global_def:
  set_global v value ^s =
    (s with globals := s.globals |+ (v,value))
End

Definition set_kvar_def:
  set_kvar vk v value ^s =
  case vk of
    Local => set_var v value s
  | Global => set_global v value s
End

Definition lookup_kvar_def:
  lookup_kvar ^s vk v =
  case vk of
    Local => FLOOKUP s.locals v
  | Global => FLOOKUP s.globals v
End

Definition upd_locals_def:
   upd_locals varargs ^s =
     s with <| locals := FEMPTY |++ varargs  |>
End

Definition empty_locals_def:
   empty_locals ^s =
     s with <| locals := FEMPTY |>
End

Definition dec_clock_def:
  dec_clock ^s =
   s with clock := s.clock - 1
End

Definition fix_clock_def:
  fix_clock old_s (res, new_s) =
    (res, new_s with <|clock := if old_s.clock < new_s.clock then old_s.clock else new_s.clock |>)
End

Theorem fix_clock_IMP_LESS_EQ:
  !x. fix_clock ^s x = (res,s1) ==> s1.clock <= s.clock
Proof
  full_simp_tac(srw_ss())[fix_clock_def,FORALL_PROD] >>
  srw_tac[][] >> full_simp_tac(srw_ss())[] >> decide_tac
QED

Definition lookup_code_def:
  lookup_code code fname args =
    case (FLOOKUP code fname) of
      | SOME (vshapes, prog) =>
         if ALL_DISTINCT (MAP FST vshapes) ∧
            LIST_REL (\vshape arg. SND vshape = shape_of arg) vshapes args
         then SOME (prog, FEMPTY |++ ZIP (MAP FST vshapes,args))
         else NONE
      | _ => NONE
End

Definition is_valid_value_def:
  is_valid_value locals v value =
    case FLOOKUP locals v of
     | SOME w => shape_of value = shape_of w
     | NONE => F
End

Definition res_var_def:
  (res_var lc (n, NONE) = lc \\ n) /\
  (res_var lc (n, SOME v) = lc |+ (n,v))
End

Definition sh_mem_load_def:
  sh_mem_load vk v (addr:'a word) nb ^s =
  if nb = 0 then
    (if addr IN s.sh_memaddrs then
       (case call_FFI s.ffi (SharedMem MappedRead) [n2w nb] (word_to_bytes addr F) of
          FFI_final outcome => (SOME (FinalFFI outcome), empty_locals s)
        | FFI_return new_ffi new_bytes =>
            (NONE, (set_kvar vk v (ValWord (word_of_bytes F 0w new_bytes)) s) with ffi := new_ffi))
     else (SOME Error, s))
  else
    (if (byte_align addr) IN s.sh_memaddrs then
       (case call_FFI s.ffi (SharedMem MappedRead) [n2w nb] (word_to_bytes addr F) of
          FFI_final outcome => (SOME (FinalFFI outcome), empty_locals s)
        | FFI_return new_ffi new_bytes =>
            (NONE, (set_kvar vk v (ValWord (word_of_bytes F 0w new_bytes)) s) with ffi := new_ffi))
     else (SOME Error, s))
End

Definition sh_mem_store_def:
  sh_mem_store w (addr:'a word) nb ^s =
  if nb = 0 then
    (if addr IN s.sh_memaddrs then
       (case call_FFI s.ffi (SharedMem MappedWrite) [n2w nb]
                      (word_to_bytes w F ++ word_to_bytes addr F) of
          FFI_final outcome => (SOME (FinalFFI outcome), s)
        | FFI_return new_ffi new_bytes =>
            (NONE, s with ffi := new_ffi))
     else (SOME Error, s))
  else
    (if (byte_align addr) IN s.sh_memaddrs then
       (case call_FFI s.ffi (SharedMem MappedWrite) [n2w nb]
                      (TAKE nb (word_to_bytes w F)
                       ++ word_to_bytes addr F) of
          FFI_final outcome => (SOME (FinalFFI outcome), s)
        | FFI_return new_ffi new_bytes =>
            (NONE, s with ffi := new_ffi))
     else (SOME Error, s))
End

Definition nb_op_def:
  nb_op Op8 = 1:num ∧
  nb_op Op16 = 2 ∧
  nb_op OpW = 0 ∧
  nb_op Op32 = 4
End

Definition evaluate_def:
  (evaluate (Skip:'a panLang$prog,^s) = (NONE,s)) /\
  (evaluate (Dec v sh e prog, s) =
    case (eval s e) of
     | SOME value =>
        if sh = shape_of value then
          let (res,st) = evaluate (prog,s with locals := s.locals |+ (v,value)) in
          (res, st with locals := res_var st.locals (v, FLOOKUP s.locals v))
        else (NONE,s)
     | NONE => (SOME Error, s)) /\
  (evaluate (Assign Local v src,s) =
    case (eval s src) of
     | SOME value =>
        if is_valid_value s.locals v value
        then (NONE, s with locals := s.locals |+ (v,value))
        else (SOME Error, s)
     | NONE => (SOME Error, s)) /\
  (evaluate (Assign Global v src,s) =
    case (eval s src) of
     | SOME value =>
        if is_valid_value s.globals v value
        then (NONE, s with globals := s.globals |+ (v,value))
        else (SOME Error, s)
     | NONE => (SOME Error, s)) /\
  (evaluate (Store dst src,s) =
    case (eval s dst, eval s src) of
     | (SOME (ValWord addr), SOME value) =>
       (case mem_stores addr (flatten value) s.memaddrs s.memory of
         | SOME m => (NONE, s with memory := m)
         | NONE => (SOME Error, s))
     | _ => (SOME Error, s)) /\
  (evaluate (Store32 dst src,s) =
    case (eval s dst, eval s src) of
     | (SOME (ValWord adr), SOME (ValWord w)) =>
        (case mem_store_32 s.memory s.memaddrs s.be adr (w2w w) of
          | SOME m => (NONE, s with memory := m)
          | NONE => (SOME Error, s))
     | _ => (SOME Error, s)) /\
  (evaluate (StoreByte dst src,s) =
    case (eval s dst, eval s src) of
     | (SOME (ValWord adr), SOME (ValWord w)) =>
        (case mem_store_byte s.memory s.memaddrs s.be adr (w2w w) of
          | SOME m => (NONE, s with memory := m)
          | NONE => (SOME Error, s))
     | _ => (SOME Error, s)) /\
  (evaluate (ShMemLoad op vk v ad,s) =
    case eval s ad of
    | SOME (ValWord addr) =>
        (case lookup_kvar s vk v of
           SOME (ValWord _) => sh_mem_load vk v addr (nb_op op) s
         | _ => (SOME Error, s))
     | _ => (SOME Error, s)) /\
  (evaluate (ShMemStore op ad e,s) =
     case (eval s ad,eval s e) of
     | (SOME (ValWord addr), SOME (ValWord bytes)) => sh_mem_store bytes addr (nb_op op) s
     | _ => (SOME Error, s)) /\
  (evaluate (Seq c1 c2,s) =
     let (res,s1) = fix_clock s (evaluate (c1,s)) in
     if res = NONE then evaluate (c2,s1) else (res,s1)) /\
  (evaluate (If e c1 c2,s) =
    case (eval s e) of
     | SOME (ValWord w) =>
        evaluate (if w <> 0w then c1 else c2, s)  (* False is 0, True is everything else *)
     | _ => (SOME Error,s)) /\
  (evaluate (Break,s) = (SOME Break,s)) /\
  (evaluate (Continue,s) = (SOME Continue,s)) /\
  (evaluate (While e c,s) =
    case (eval s e) of
     | SOME (ValWord w) =>
       if (w <> 0w) then
       (if s.clock = 0 then (SOME TimeOut,empty_locals s) else
         let (res,s1) = fix_clock (dec_clock s) (evaluate (c,dec_clock s)) in
         case res of
          | SOME Continue => evaluate (While e c,s1)
          | NONE => evaluate (While e c,s1)
          | SOME Break => (NONE,s1)
          | _ => (res,s1))
        else (NONE,s)
     | _ => (SOME Error,s)) /\
  (evaluate (Return e,s) =
    case (eval s e) of
      | SOME value =>
         if size_of_sh_with_ctxt s.structs (shape_of value) <= 32
         then (SOME (Return value),empty_locals s)
         else (SOME Error,s)
      | _ => (SOME Error,s)) /\
  (evaluate (Raise eid e,s) =
    case (FLOOKUP s.eshapes eid, eval s e) of
      | (SOME sh, SOME value) =>
         if shape_of value = sh ∧
            size_of_sh_with_ctxt s.structs (shape_of value) <= 32
         then (SOME (Exception eid value),empty_locals s)
         else (SOME Error,s)
     | _ => (SOME Error,s)) /\
  (evaluate (Tick,s) =
    if s.clock = 0 then (SOME TimeOut,empty_locals s)
    else (NONE,dec_clock s)) /\
  (evaluate (Annot _ _,s) = (NONE, s)) /\
  (evaluate (Call caltyp fname argexps,s) =
    case OPT_MMAP (eval s) argexps of
     | SOME args =>
        (case lookup_code s.code fname args of
          | SOME (prog, newlocals) => if s.clock = 0 then (SOME TimeOut,empty_locals s)
           else
           let eval_prog = fix_clock ((dec_clock s) with locals := newlocals)
                                     (evaluate (prog, (dec_clock s) with locals:= newlocals)) in
           (case eval_prog of
              | (NONE,st) => (SOME Error,st)
              | (SOME Break,st) => (SOME Error,st)
              | (SOME Continue,st) => (SOME Error,st)
              | (SOME (Return retv),st) =>
                  (case caltyp of
                    | NONE      => (SOME (Return retv),empty_locals st)
                    | SOME (NONE, _) => (NONE, st with locals := s.locals)
                    | SOME (SOME (rk, rt),  _) =>
                       if is_valid_value (if rk = Local then s.locals else s.globals) rt retv
                       then (NONE, set_kvar rk rt retv (st with locals := s.locals))
                       else (SOME Error,st))
              | (SOME (Exception eid exn),st) =>
                  (case caltyp of
                    | NONE        => (SOME (Exception eid exn),empty_locals st)
                    | SOME (_, NONE) => (SOME (Exception eid exn),empty_locals st)
                    | SOME (_, (SOME (eid', evar, p))) =>
                      if eid = eid' then
                       case FLOOKUP s.eshapes eid of
                        | SOME sh =>
                            if shape_of exn = sh ∧ is_valid_value s.locals evar exn then
                              evaluate (p, set_var evar exn (st with locals := s.locals))
                            else (SOME Error,st)
                        | NONE => (SOME Error,st)
                      else (SOME (Exception eid exn), empty_locals st))
              | (res,st) => (res,empty_locals st))
         | _ => (SOME Error,s))
     | _ => (SOME Error,s))/\
  (evaluate (DecCall rt shape fname argexps prog1,s) =
    case OPT_MMAP (eval s) argexps of
     | SOME args =>
        (case lookup_code s.code fname args of
          | SOME (prog, newlocals) => if s.clock = 0 then (SOME TimeOut,empty_locals s)
           else
           let eval_prog = fix_clock ((dec_clock s) with locals := newlocals)
                                     (evaluate (prog, (dec_clock s) with locals:= newlocals)) in
           (case eval_prog of
              | (NONE,st) => (SOME Error,st)
              | (SOME Break,st) => (SOME Error,st)
              | (SOME Continue,st) => (SOME Error,st)
              | (SOME (Return retv),st) =>
                  if shape_of retv = shape then
                    let (res',st') = evaluate (prog1, set_var rt retv (st with locals := s.locals)) in
                      (res',st' with locals := res_var st'.locals (rt, FLOOKUP s.locals rt))
                  else
                    (SOME Error, st)
              | (res,st) => (res,empty_locals st))
           | _ => (SOME Error,s))
     | _ => (SOME Error,s)) /\
  (evaluate (ExtCall ffi_index ptr1 len1 ptr2 len2,s) =
   case (eval s ptr1, eval s len1, eval s ptr2, eval s len2) of
      | SOME (ValWord sz1),SOME (ValWord ad1),SOME (ValWord sz2),SOME (ValWord ad2) =>
        (case (read_bytearray sz1 (w2n ad1) (mem_load_byte s.memory s.memaddrs s.be),
               read_bytearray sz2 (w2n ad2) (mem_load_byte s.memory s.memaddrs s.be)) of
         | SOME bytes,SOME bytes2 =>
           (case call_FFI s.ffi (ExtCall (explode ffi_index)) bytes bytes2 of
            | FFI_final outcome => (SOME (FinalFFI outcome), empty_locals s)
            | FFI_return new_ffi new_bytes =>
                let nmem = write_bytearray sz2 new_bytes s.memory s.memaddrs s.be in
                 (NONE, s with <| memory := nmem; ffi := new_ffi |>))
         | _ => (SOME Error,s))
      | res => (SOME Error,s))
Termination
  wf_rel_tac `(inv_image (measure I LEX measure (prog_size (K 0)))
               (\(xs,^s). (s.clock,xs)))` >>
  rw[] >>
  gvs[set_var_def,upd_locals_def,dec_clock_def, UNCURRY_eq_pair,
      oneline fix_clock_def, AllCaseEqs()]
End

val evaluate_ind = theorem"evaluate_ind";


Theorem vshapes_args_rel_imp_eq_len_MAP:
  !vshapes args.
    LIST_REL (\vshape arg. SND vshape = shape_of arg)  vshapes args ==>
     LENGTH vshapes = LENGTH args /\ MAP SND vshapes = MAP shape_of args
Proof
  ho_match_mp_tac LIST_REL_ind >> rw []
QED

(*
Definition evaluate_main_def:
  (evaluate_main (Decl dname str,^s) = ARB) /\
  (evaluate_main (Func fname rettyp partyp prog,s) = ARB)
End
*)

Theorem evaluate_clock:
   !prog s r s'. (evaluate (prog,s) = (r,s')) ==>
                 s'.clock <= s.clock
Proof
  recInduct evaluate_ind >> rpt strip_tac >>
  qpat_x_assum ‘evaluate _ = _’ mp_tac >>
  rw[Once evaluate_def] >>
  gvs[AllCaseEqs(), UNCURRY_eq_pair,
      set_var_def, set_global_def, upd_locals_def, empty_locals_def, dec_clock_def,
      sh_mem_load_def,sh_mem_store_def, lookup_kvar_def, oneline fix_clock_def,
      set_kvar_def, SF DNF_ss]
QED

Theorem fix_clock_evaluate:
  fix_clock s (evaluate (prog,s)) = evaluate (prog,s)
Proof
  Cases_on `evaluate (prog,s)` >> fs [fix_clock_def] >>
  imp_res_tac evaluate_clock >>
  fs [GSYM NOT_LESS, state_component_equality]
QED

(* we save evaluate theorems without fix_clock *)
Theorem evaluate_ind[allow_rebind] =
  REWRITE_RULE [fix_clock_evaluate] evaluate_ind

Theorem evaluate_def[allow_rebind,compute] =
  REWRITE_RULE [fix_clock_evaluate] evaluate_def

(* observational semantics *)

Definition semantics_def:
  semantics ^s start =
   let prog = Call NONE start [] in
    if ∃k. case FST (evaluate (prog,s with clock := k)) of
            | SOME TimeOut => F
            | SOME (FinalFFI _) => F
            | SOME (Return _) => F
            | _ => T
    then Fail
    else
     case some res.
      ∃k t r outcome.
        evaluate (prog, s with clock := k) = (r,t) ∧
        (case r of
         | (SOME (FinalFFI e)) => outcome = FFI_outcome e
         | (SOME (Return _))   => outcome = Success
         | _ => F) ∧
        res = Terminate outcome t.ffi.io_events
      of
    | SOME res => res
    | NONE =>
      Diverge
         (build_lprefix_lub
           (IMAGE (λk. fromList
              (SND (evaluate (prog,s with clock := k))).ffi.io_events) UNIV))
End

(* declaration semantics *)

Definition evaluate_decls_def:
  evaluate_decls ^s [] =
    SOME s ∧
  evaluate_decls s (Name nm flds::ds) =
    (evaluate_decls s ds) ∧
  evaluate_decls s (Decl sh v e::ds) =
    (case eval (s with locals := FEMPTY) e of
      SOME res =>
        (if sh = shape_of res then
            evaluate_decls (s with globals := s.globals |+ (v,res)) ds
          else
            NONE)
    | NONE => NONE) ∧
  evaluate_decls s (Function fi::ds) =
    if EVERY ((is_wf_shape s.structs) o SND) fi.params
       /\ is_wf_shape s.structs fi.return then
      evaluate_decls (s with code := s.code |+ (fi.name,(fi.params,fi.body))) ds
    else NONE
End

Definition evaluate_stcnames_def:
  evaluate_stcnames ^s [] =
    SOME s ∧
  evaluate_stcnames s (Name nm flds::ds) =
    (let shs = MAP SND flds in
    if EVERY (is_wf_shape s.structs) shs then
      let info = <| fields := flds
                  ; size := size_of_sh_with_ctxt s.structs (Comb shs) |> in
        evaluate_stcnames (s with structs := (nm,info)::s.structs) ds
    else NONE) ∧
  evaluate_stcnames s (Decl sh v e::ds) =
    (evaluate_stcnames s ds) ∧
  evaluate_stcnames s (Function fi::ds) =
    (evaluate_stcnames s ds)
End

Definition semantics_decls_def:
  semantics_decls ^s start decls =
  case evaluate_decls s decls of
  | NONE => Fail
  | SOME s' =>
    case evaluate_decls s decls of
    | NONE => Fail
    | SOME s' => semantics s' start
End

val _ = map delete_binding ["evaluate_AUX_def", "evaluate_primitive_def"];

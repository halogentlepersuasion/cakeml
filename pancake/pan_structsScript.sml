(*
  Convert named structs to raw structs
*)
Theory pan_structs
Ancestors
  panLang backend_common
Libs
  preamble

val _ = numLib.prefer_num();

Datatype:
  context =
  <| structs : (stcname # (fldname # shape) list) list
   ; locals  : (varname # shape) list
   ; globals : (varname # shape) list
  |>
End

Definition compile_shape_def:
  (compile_shape sctxt One = One) ∧
  (compile_shape sctxt (Comb shapes) = Comb $ compile_shapes sctxt shapes) ∧
  (compile_shape sctxt (Named nm) =
    case dropWhile (\(n,fs). ~(n = nm)) sctxt of
    | (nm,flds)::sctxt' => Comb $ compile_shapes sctxt' $ MAP SND flds
    | _ => One (* should never happen *)) ∧
  (compile_shapes sctxt [] = []) ∧
  (compile_shapes sctxt (sh::shs) =
    compile_shape sctxt sh :: compile_shapes sctxt shs)
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
        | INL x => (FST x, INL $ SND x)
        | INR x => (FST x, INR $ SND x))’ >>
	rw[] >>
	disj1_tac >>
	irule LESS_LESS_EQ_TRANS >>
	irule_at Any LENGTH_dropWhile_LESS_EQ >>
  qmatch_asmsub_abbrev_tac `dropWhile ff` >>
  qexists `ff` >>
  rw[]
End

Definition alookupi_def:
  alookupi x [] = (NONE, 0) /\
  alookupi x ((k,v)::t) =
    if x = k then
      (SOME v, 0)
    else
      let (v, i) = alookupi x t in (v, 1 + i)
End

(* (new exp, old shape) *)
Definition compile_exp_def:
  (compile_exp ctxt (Const num) = (Const num, One)) ∧
  (compile_exp ctxt (Var Local v) =
    let sh =
      case ALOOKUP ctxt.locals v of
      | NONE => One (* should never happen *)
      | SOME sh => sh in
    (Var Local v, sh)) ∧
  (compile_exp ctxt (Var Global v) = 
    let sh =
      case ALOOKUP ctxt.globals v of
      | NONE => One (* should never happen *)
      | SOME sh => sh in
    (Var Global v, sh)) ∧
  (compile_exp ctxt (RStruct es) =
    let (es', shs) = compile_exps ctxt es in
    (RStruct es', Comb shs)) ∧
  (compile_exp ctxt (RField index e) =
    let (e', sh) = compile_exp ctxt e in
    let sh' =
      case sh of
      | Comb shs =>
        case LLOOKUP shs index of
        | SOME sh => sh
        | NONE => One (* should never happen *)
      | _ => One (* should never happen *) in
    (RField index e', sh')) ∧
  (compile_exp ctxt (NStruct nm eflds) =
    let es' =
      case ALOOKUP ctxt.structs nm of
      | NONE => [] (* should never happen *)
      | SOME flds => compile_fields ctxt flds eflds in
    (RStruct es', Named nm)) ∧
  (compile_exp ctxt (NField fld e) =
    let (e', sh) = compile_exp ctxt e in
    let (index, sh') =
      (case sh of
      | Named nm =>
        (case ALOOKUP ctxt.structs nm of
        | NONE => (0, One) (* should never happen *)
        | SOME flds =>
          (case alookupi fld flds of
          | (SOME sh, n) => (n, sh)
          | _ => (0, One) (* should never happen *)))
      | _ => (0, One) (* should never happen *)) in
    (RField index e', sh')) ∧
  (compile_exp ctxt (Load sh e) =
    (Load (compile_shape ctxt.structs sh) (FST $ compile_exp ctxt e), sh)) ∧
  (compile_exp ctxt (LoadByte e) =
    (LoadByte (FST $ compile_exp ctxt e), One)) ∧
  (compile_exp ctxt (Load32 e) =
    (Load32 (FST $ compile_exp ctxt e), One)) ∧
  (compile_exp ctxt (Op bop es) =
    (Op bop (FST $ compile_exps ctxt es), One)) ∧
  (compile_exp ctxt (Panop pop es) =
    (Panop pop (FST $ compile_exps ctxt es), One)) ∧
  (compile_exp ctxt (Cmp cmp e1 e2) =
    (Cmp cmp (FST $ compile_exp ctxt e1) (FST $ compile_exp ctxt e2), One)) ∧
  (compile_exp ctxt (Shift sh e n) =
    (Shift sh (FST $ compile_exp ctxt e) n, One)) ∧
  (compile_exp ctxt (BaseAddr) = (BaseAddr, One)) ∧
  (compile_exp ctxt (TopAddr) = (TopAddr, One)) ∧
  (compile_exp ctxt (BytesInWord) = (BytesInWord, One)) ∧
  (compile_exps ctxt [] = ([],[])) ∧
  (compile_exps ctxt (e::es) =
      let (e', sh) = compile_exp ctxt e in
      let (es', shs) = compile_exps ctxt es in
      ((e'::es'), (sh::shs))) ∧
  (compile_fields ctxt [] _ = []) ∧
  (compile_fields ctxt ((fld,sh)::flds) eflds =
    case ALOOKUP eflds fld of
    | NONE => [] (* should never happen *)
    | SOME exp =>
      let (e', sh) = compile_exp ctxt exp in
      e'::compile_fields ctxt flds eflds)
      (* e'::compile_fields ctxt flds (ADELKEY fld eflds)) *)
Termination
  (* wf_rel_tac `measure (\x. case x of
                           | INL x => exp_size ARB $ SND x
                           | INR(INL x) => list_size (exp_size ARB) $ SND x
                           | INR(INR x) => list_size (exp_size ARB o SND) $ SND $ SND x)` *)
  cheat
End

Definition compile_def:
  (compile ctxt (Dec v s e p) =
    Dec v
      (compile_shape ctxt.structs s)
      (FST $ compile_exp ctxt e)
      (compile (ctxt with locals := (v,s)::ctxt.locals) p)) ∧
  (compile ctxt (Assign vk v e) =
    Assign vk v (FST $ compile_exp ctxt e)) ∧
  (compile ctxt (Store ad v) =
    Store (FST $ compile_exp ctxt ad) (FST $ compile_exp ctxt v)) ∧
  (compile ctxt (Store32 ad v) =
    Store32 (FST $ compile_exp ctxt ad) (FST $ compile_exp ctxt v)) ∧
  (compile ctxt (StoreByte dest src) =
    StoreByte (FST $ compile_exp ctxt dest) (FST $ compile_exp ctxt src)) ∧
  (compile ctxt (Seq p p') =
    Seq (compile ctxt p) (compile ctxt p')) ∧
  (compile ctxt (If e p p') =
    If (FST $ compile_exp ctxt e) (compile ctxt p) (compile ctxt p')) ∧
  (compile ctxt (While e p) =
    While (FST $ compile_exp ctxt e) (compile ctxt p)) ∧
  (compile ctxt (Call rtyp f es) =
    let cexps = FST $ compile_exps ctxt es in
      case rtyp of
      | NONE => Call NONE f cexps
      | SOME (tl, hdl) =>
        Call (SOME (tl,
            case hdl of
            | NONE => NONE
            | SOME (eid, evar, p) =>
              SOME (eid, evar, compile ctxt p)))
          f cexps) ∧
  (compile ctxt (DecCall v s f es p) =
    DecCall v
      (compile_shape ctxt.structs s) f
      (FST $ compile_exps ctxt es)
      (compile (ctxt with locals := (v,s)::ctxt.locals) p)) ∧
  (compile ctxt (ExtCall f ptr1 len1 ptr2 len2) =
    ExtCall f
      (FST $ compile_exp ctxt ptr1)
      (FST $ compile_exp ctxt len1)
      (FST $ compile_exp ctxt ptr2)
      (FST $ compile_exp ctxt len2)) ∧
  (compile ctxt (Return rt) =
    Return (FST $ compile_exp ctxt rt)) ∧
  (compile ctxt (Raise eid excp) =
    Raise eid (FST $ compile_exp ctxt excp)) ∧
  (compile ctxt (ShMemStore op r ad) =
   ShMemStore op (FST $ compile_exp ctxt r) (FST $ compile_exp ctxt ad)) ∧
  (compile ctxt (ShMemLoad op vk r ad) =
   ShMemLoad op vk r (FST $ compile_exp ctxt ad)) ∧
  (compile _ p = p)
End

Definition compile_decs_def:
  (compile_decs ctxt [] = ([],ctxt)) ∧
  (compile_decs ctxt (Decl sh v e::ds) =
    let (ds', ctxt') = compile_decs (ctxt with globals := (v,sh)::ctxt.globals) ds in
    (Decl (compile_shape ctxt.structs sh) v (FST $ compile_exp ctxt e) ::ds',
      ctxt')) ∧
  (compile_decs ctxt (Function fi::ds) =
    let (ds', ctxt') = compile_decs ctxt ds in
    let ctxt'' = ctxt' with locals := fi.params in
    (Function (fi with body := compile ctxt'' fi.body) ::ds',
      ctxt')) ∧
  (compile_decs ctxt (Name nm flds::ds) =
    compile_decs ctxt ds)
End

Definition get_names_def:
  (get_names ctxt [] = ctxt) ∧
  (get_names ctxt (Name nm flds::ds) =
    get_names (ctxt with structs := (nm,flds)::ctxt.structs) ds) ∧
  (get_names ctxt (_::ds) =
    get_names ctxt ds)
End

Definition compile_top_def:
  compile_top decs =
    let ctxt = <| structs := []; locals := []; globals := [] |> in
    FST $ compile_decs (get_names ctxt decs) decs
End

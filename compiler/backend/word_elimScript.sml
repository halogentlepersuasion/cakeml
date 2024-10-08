(*
  Implementation for wordLang dead-code elimination.

  Analyses code to give a next-step function as a num_set num_map.
  Uses flat_elim functions to close the next-step function and give a set of
    reachable functions.
  Removes unreachable functions from the code.
*)

open preamble sptreeTheory spt_closureTheory wordLangTheory

val _ = new_theory "word_elim";


Definition find_word_loc_def:
    (find_word_loc (name:num, _, _) = name)
End

Definition find_word_ref_def:
    (find_word_ref (MustTerminate p) = find_word_ref p) ∧
    (find_word_ref (Call ret target _ handler) = union
        (case target of | NONE => LN | SOME n => (insert n () LN))
            (union
                (case ret of
                    | NONE => LN
                    | SOME (_,_,ret_handler,l1,_) =>
                        insert l1 () (find_word_ref (ret_handler)))
                (case handler of
                    | NONE => LN
                    | SOME (_,ex_handler,_,_) => find_word_ref (ex_handler)))
    ) ∧
    (find_word_ref (Seq p1 p2) = union (find_word_ref p1) (find_word_ref p2)) ∧
    (find_word_ref (If _ _ _ p1 p2) =
        union (find_word_ref p1) (find_word_ref p2)) ∧
    (find_word_ref (LocValue _ n) = insert n () LN) ∧
    (find_word_ref _ = LN)
End

val find_word_ref_ind = theorem "find_word_ref_ind";

Definition analyse_word_code_def:
    (analyse_word_code [] = LN:num_set num_map) ∧
    (analyse_word_code ((n, args, prog)::t) =
        insert n (find_word_ref prog) (analyse_word_code t))
End

Definition remove_word_code_def:
    remove_word_code reachable l =
        FILTER (\ x . IS_SOME (lookup (FST x) reachable)) l
End

Definition remove_word_prog_def:
    remove_word_prog (n:num) code =
        let t = analyse_word_code code in
        let reachable = closure_spt (insert n () (LN:num_set)) t in
        remove_word_code reachable code
End


val _ = export_theory();

(*
  This is an example of applying the translator to the Hood Melville
  Queue algorithm from Chris Okasaki's book.
*)
open HolKernel Parse boolLib bossLib; val _ = new_theory "HoodMelvilleQueue";

open listTheory arithmeticTheory ml_translatorLib ListProgTheory;

val _ = translation_extends "ListProg";

val _ = Parse.hide"state";

(* implementation *)

Datatype:
  status =
     Idle
   | Reversing num ('a list) ('a list) ('a list) ('a list)
   | Appending num ('a list) ('a list)
   | Finished ('a list)
End

Datatype:
  queue = QUEUE num ('a list) ('a status) num ('a list)
End

Definition exec_def:
  exec s = case s of
    Reversing ok (x::f) f' (y::r) r' => Reversing (ok+1) f (x::f') r (y::r')
  | Reversing ok [] f' [y] r' => Appending ok f' (y::r')
  | Appending 0 f' r' => Finished r'
  | Appending ok (x::f') r' => Appending (ok-1) f' (x::r')
  | s => s
End
val r = translate exec_def;

Definition invalidate_def:
  invalidate s = case s of
    Reversing ok f f' r r' => Reversing (ok-1) f f' r r'
  | Appending 0 f' (x::r') => Finished r'
  | Appending ok f' r' => Appending (ok-1) f' r'
  | s => s
End
val r = translate invalidate_def;

Definition exec2_def:
  exec2 (QUEUE lenf f state lenr r) =
    case exec (exec state) of
      Finished newf => QUEUE lenf newf Idle lenr r
    | newstate => QUEUE lenf f newstate lenr r
End
val r = translate exec2_def;

Definition check_def:
  check (QUEUE lenf f state lenr r) =
    if lenr <= lenf
       then exec2 (QUEUE lenf f state lenr r)
       else let newstate = Reversing 0 f [] r [] in
            exec2 (QUEUE (lenf+lenr) f newstate 0 [])
End
val r = translate check_def;

Definition empty_def:
  empty = QUEUE 0 [] Idle 0 []
End
val r = translate empty_def;

Definition is_empty_def:
  is_empty lenf _ _ _ _ = (lenf = 0:num)
End
val r = translate is_empty_def;

Definition snoc_def:
  snoc (QUEUE lenf f state lenr r) x =
    check (QUEUE lenf f state (lenr+1) (x::r))
End
val r = translate snoc_def;

Definition head_def:
  head (QUEUE _ (x::_) _ _ _) = x
End
val r = translate head_def;

Definition tail_def:
  tail (QUEUE lenf (x::f) state lenr r) =
    check (QUEUE (lenf-1) f (invalidate state) lenr r)
End
val r = translate tail_def;

(* verification proof

Definition base_def:
  base lf lenf lenr r g q =
    (lenr = LENGTH r) /\ (lenf = lf) /\ (q = g ++ REVERSE r)
End

Definition oper_def:
  oper lenf f lenr r g q d n m p =
    base (2 * m + 1 - p) lenf lenr r g q /\
    (n + d = 2 * p + 2 * lenr + 2) /\
    (m = LENGTH f + p) /\
    isPREFIX f q
End

Definition reve_def:
  reve f f' f'' r' r'' g ok n m p =
    (g = REVERSE (TAKE ok f') ++ f'' ++ REVERSE r'' ++ r') /\
    (n = LENGTH f') /\
    (m = LENGTH f'' + n) /\
    (n = LENGTH r') /\
    (m + 1 = LENGTH r'' + n)
End

Definition appe_def:
  appe f f' r' g ok n m p =
    (g = REVERSE (TAKE ok f') ++ r') /\
    (LENGTH f' + n = 2 * m + 1) /\
    (LENGTH r' = n) /\
    (ok + n + p = 2 * m + 1) /\
    m <= n /\ n <= 2 * m + 1
End

Definition prop_def:
  prop c d (QUEUE lenf f s lenr r) q =
    case s of
      Idle => base (LENGTH f) lenf lenr r f q /\ lenr <= lenf
    | Finished f' => c /\ base (LENGTH f') lenf lenr r f' q /\ lenr <= lenf
    | Reversing ok f'' f' r'' r' => ?n m p g.
        oper lenf f lenr r g q d n m p /\ reve f f' f'' r' r'' g ok n m p
    | Appending ok f' r' => ?n m p g.
        oper lenf f lenr r g q d n m p /\ appe f f' r' g ok n m p
End

Definition queue_inv_def:
  queue_inv q q' = prop F 0 q' q
End

*)

val _ = export_theory();

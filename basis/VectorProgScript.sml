(*
  Module about the built-in 'a vector.
*)
open preamble ml_translatorLib ml_translatorTheory ml_progLib
     ListProgTheory basisFunctionsLib;
open mlvectorTheory;

val _ = new_theory"VectorProg"

val _ = set_grammar_ancestry ["ast", "regexp_compiler", "ml_translator"]
val _ = translation_extends "ListProg";

val _ = ml_prog_update (open_module "Vector");

val () = generate_sigs := true;

val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc ["'a"] "vector" (Atapp [Atvar "'a"] (Short "vector"))`` I);

val _ = trans "fromList" ``regexp_compiler$Vector``;
val _ = trans "length" ``regexp_compiler$length``;
val _ = trans "sub" ``regexp_compiler$sub``;

val _ = next_ml_names := ["tabulate"];
val result = translate tabulate_def;

val _ = ml_prog_update open_local_block;
val result = translate toList_aux_def;
val _ = ml_prog_update open_local_in_block;

val _ = next_ml_names := ["toList"];
val result = translate toList_def;

val _ = next_ml_names := ["update"];
val result = translate update_def;

val _ = next_ml_names := ["concat"];
val result = translate concat_def;

val _ = next_ml_names := ["map"];
val result = translate map_def;
val _ = next_ml_names := ["mapi"];
val result = translate mapi_def;

val _ = ml_prog_update open_local_block;
val result = translate foldli_aux_def;
val foldli_aux_side_def = theorem"foldli_aux_side_def"
val _ = ml_prog_update open_local_in_block;

val _ = next_ml_names := ["foldli"];
val result = translate foldli_def;
val foldli_side_def = definition"foldli_1_side_def";

Triviality foldli_aux_side_thm:
  !f e vec n len. n + len = length vec ==> foldli_aux_side f e vec n len
Proof
  Induct_on`len` \\ rw[Once foldli_aux_side_def]
QED

val foldli_side_thm = Q.prove(
  `foldli_1_side f e vec`,
  rw[foldli_side_def,foldli_aux_side_thm]) |> update_precondition;

val _ = ml_prog_update open_local_block;
val result = translate foldl_aux_def;
val foldl_aux_side_def = theorem"foldl_aux_side_def"
val _ = ml_prog_update open_local_in_block;

val _ = next_ml_names := ["foldl"];
val result = translate foldl_def;
val foldl_side_def = definition"foldl_1_side_def";

Triviality foldl_aux_side_thm:
  !f e vec n len. n + len = length vec ==> foldl_aux_side f e vec n len
Proof
  Induct_on `len` \\ rw [Once foldl_aux_side_def]
QED

val foldl_side_thm = Q.prove(
  `!f e vec. foldl_1_side f e vec`,
  rw [foldl_side_def, foldl_aux_side_thm]) |> update_precondition;

val _ = ml_prog_update open_local_block;
val result = translate foldri_aux_def;
val foldri_aux_side_def = theorem"foldri_aux_side_def";
val _ = ml_prog_update open_local_in_block;

val _ = next_ml_names := ["foldri"];
val result = translate foldri_def;
val foldri_side_def = definition"foldri_1_side_def";

Triviality foldri_aux_side_thm:
  !f e vec len. len <= length vec ==> foldri_aux_side f e vec len
Proof
  Induct_on `len` \\ rw [Once foldri_aux_side_def]
QED

val foldri_side_thm = Q.prove(
  `!f e vec. foldri_1_side f e vec`,
  rw [foldri_side_def, foldri_aux_side_thm] ) |> update_precondition

val _ = ml_prog_update open_local_block;
val result = translate foldr_aux_def;
val foldr_aux_side_def = theorem"foldr_aux_side_def";
val _ = ml_prog_update open_local_in_block;

val _ = next_ml_names := ["foldr"];
val result = translate foldr_def;
val foldr_side_def = definition"foldr_1_side_def";

Triviality foldr_aux_side_thm:
  !f e vec len. len <= length vec ==> foldr_aux_side f e vec len
Proof
  Induct_on `len` \\ rw[Once foldr_aux_side_def]
QED

val foldr_side_thm = Q.prove(
  `!f e vec. foldr_1_side f e vec`,
  rw [foldr_side_def, foldr_aux_side_thm] ) |> update_precondition

val _ = ml_prog_update open_local_block;
val result = translate findi_aux_def;
val findi_aux_side_def = theorem"findi_aux_side_def"
val _ = ml_prog_update open_local_in_block;

val _ = next_ml_names := ["findi"];
val result = translate findi_def;
val findi_side_def = definition"findi_side_def"

Triviality findi_aux_side_thm:
  !f vec n len. n + len = length vec ==> findi_aux_side f vec n len
Proof
  Induct_on `len` \\ rw [Once findi_aux_side_def]
QED

val findi_side_thm = Q.prove (
  `!f vec. findi_side f vec`,
  rw [findi_side_def, findi_aux_side_thm] ) |> update_precondition

val _ = ml_prog_update open_local_block;
val result = translate find_aux_def;
val find_aux_side_def = theorem"find_aux_side_def"
val _ = ml_prog_update open_local_in_block;

val _ = next_ml_names := ["find"];
val result = translate find_def;
val find_side_def = definition"find_1_side_def"

Triviality find_aux_side_thm:
  !f vec n len. n + len = length vec ==> find_aux_side f vec n len
Proof
  Induct_on `len` \\ rw [Once find_aux_side_def]
QED

val find_side_thm = Q.prove (
  `!f vec. find_1_side f vec`,
  rw [find_side_def, find_aux_side_thm]) |> update_precondition

val _ = ml_prog_update open_local_block;
val result = translate exists_aux_def;
val exists_aux_side_def = theorem"exists_aux_side_def";
val _ = ml_prog_update open_local_in_block;

val _ = next_ml_names := ["exists"];
val result = translate exists_def;
val exists_side_def = definition"exists_1_side_def";

Triviality exists_aux_side_thm:
  !f vec n len. n + len = length vec ==> exists_aux_side f vec n len
Proof
  Induct_on `len` \\ rw [Once exists_aux_side_def]
QED

val exists_side_thm = Q.prove (
  `!f vec. exists_1_side f vec`,
  rw [exists_side_def, exists_aux_side_thm]) |> update_precondition

val _ = ml_prog_update open_local_block;
val result = translate all_aux_def;
val all_aux_side_def = theorem"all_aux_side_def";
val _ = ml_prog_update open_local_in_block;

val _ = next_ml_names := ["all"];
val result = translate all_def;
val all_side_def = definition"all_1_side_def";

Triviality all_aux_side_thm:
  !f vec n len. n + len = length vec ==> all_aux_side f vec n len
Proof
  Induct_on `len` \\ rw[Once all_aux_side_def]
QED

val all_side_thm = Q.prove (
  `!f vec. all_1_side f vec`,
  rw [all_side_def, all_aux_side_thm]) |> update_precondition

val _ = ml_prog_update open_local_block;
val result = translate collate_aux_def;
val collate_aux_side_def = theorem"collate_aux_side_def";
val _ = ml_prog_update open_local_in_block;

val _ = next_ml_names := ["collate"];
val result = translate collate_def;
val collate_side_def = definition"collate_1_side_def";

Triviality collate_aux_side_thm:
  !f vec1 vec2 n ord len. n + len =
    (if length vec1 < length vec2
      then length vec1
    else length vec2) ==>
        collate_aux_side f vec1 vec2 n ord len
Proof
  Induct_on `len` \\ rw[Once collate_aux_side_def]
QED

val collate_side_thm = Q.prove (
  `!f vec1 vec2. collate_1_side f vec1 vec2`,
  rw[collate_side_def, collate_aux_side_thm] ) |> update_precondition

val _ = ml_prog_update close_local_blocks;
val _ = ml_prog_update (close_module NONE);

val _ = export_theory ()

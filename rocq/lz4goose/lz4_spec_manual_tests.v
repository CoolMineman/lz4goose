From lz4goose Require Import prelude.
From lz4goose Require Import lz4_spec.

Lemma var_int_test1 :
var_int_parse [W8 33] = (true, 33%nat, 1%nat).
Proof. reflexivity. Qed.

Lemma var_int_test2 :
var_int_parse [W8 33; W8 0] = (true, 33%nat, 1%nat).
Proof. reflexivity. Qed.

Lemma var_int_test3 :
var_int_parse [W8 255; W8 10] = (true, 265%nat, 2%nat).
Proof. reflexivity. Qed.

Lemma var_int_test4 :
var_int_parse [W8 255; W8 10; W8 4] = (true, 265%nat, 2%nat).
Proof. reflexivity. Qed.

(* Lemma parse0 :
let (success, lz4) := lz4_parse_cont 0%nat [] in
success = true.
Proof.
  reflexivity.
Qed. *)

(* Lemma parse1 :
let (success, lz4) := lz4_parse [W8 16; W8 0] in
success = true /\ lz4 = Literal [W8 0] (Terminate 0%nat).
Proof.
  split.
  - reflexivity.
  - reflexivity.
Qed. *)

Lemma decompress1 :
let (success, lz4) := lz4_byte_decompress [W8 16; W8 0] in
success = true /\ lz4 = [W8 0].
Proof.
  split; reflexivity.
Qed.

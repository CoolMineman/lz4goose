From lz4goose Require Import prelude.

From New.golang.theory Require Import pkg.
From New.proof Require Import std.

Require Import Coq.Arith.PeanoNat.

(* Require Import New.code.lz4goose.rle.
Require Import New.generatedproof.lz4goose.rle. *)

Inductive rle_ops :=
| Terminate
| Rep (rep v: w8) (next: rle_ops).

Fixpoint rle_parse (bs: list w8) : (bool * rle_ops) :=
match bs with
| [] => (true, Terminate)
| b1 :: b2 :: bs' =>
  let (rec_s, rec_val) := rle_parse bs' in
  match rec_s with
  | true => (true, Rep b1 b2 rec_val)
  | false => (false, Terminate)
  end
| _ :: _ => (false, Terminate)
end.

Fixpoint rle_unparse (ops: rle_ops) : list w8 :=
match ops with
| Terminate => []
| Rep rep v next => rep :: v :: (rle_unparse next)
end.

Lemma rle_parse_emp (xs: list w8) : rle_parse xs = (true, Terminate) -> xs = [].
Proof.
  intros H.
  unfold rle_parse in H.
  destruct xs.
  - trivial.
  - case_match.
    + discriminate.
    + case_match. case_match.
      ++ discriminate H.
      ++ discriminate H.
Qed.

Lemma rle_parse_roundtrip (bs: list w8) (ops: rle_ops) :
rle_parse(bs) = (true, ops) -> rle_unparse(ops) = bs.
Proof.
  intros H.
  generalize dependent bs.
  induction ops.
  - unfold rle_unparse. intros bs H. rewrite eq_comm. apply rle_parse_emp. apply H.
  - intros bs H. destruct bs.
    + discriminate H.
    + destruct bs.
      ++ unfold rle_parse in H. discriminate.
      ++ unfold rle_parse in H. case_match. case_match.
        +++ inversion H. fold rle_parse in H0. rewrite H5 in H0.
          apply IHops in H0. unfold rle_unparse. fold rle_unparse. rewrite H0.
          done.
        +++ discriminate.
Qed.

(* Lemma rle_parse_roundtrip2 (bs: list w8) (ops: rle_ops) :
rle_unparse(ops) = bs -> rle_parse(bs) = (true, ops).
Proof.
  intros H.
  generalize dependent bs.
  induction ops.
  - intros bs H. simpl in H. rewrite <- H. reflexivity.
  - intros bs H. unfold rle_unparse in H. fold rle_unparse in H. destruct bs.
    ++ discriminate H.
    ++ destruct bs.
      +++ discriminate H.
      +++ apply cons_eq_inj in H as [Hrep H]. apply cons_eq_inj in H as [Hv H].
        apply IHops in H. unfold rle_parse. fold rle_parse. rewrite H. rewrite Hv. rewrite Hrep.
        reflexivity.
Qed. *)

(* Fixpoint rle_join (a b: rle_ops) : rle_ops :=
match a with
| Terminate => b
| Rep rep v next => Rep rep v (rle_join next b)
end.

Lemma rle_byte_join (xs ys: list w8) (xop yop: rle_ops) :
(rle_parse xs = (true, xop) /\ rle_parse ys = (true, yop)) -> rle_parse (xs ++ ys) = (true, rle_join xop yop).
Proof.
  intros [Hx Hy].
  apply rle_parse_roundtrip2.
  apply rle_parse_roundtrip in Hx.
  apply rle_parse_roundtrip in Hy.
  rewrite <- Hx.
  rewrite <- Hy.
  generalize dependent xs.
  induction xop.
  - unfold rle_join. unfold rle_unparse. rewrite app_nil_l. reflexivity.
  - unfold rle_join. simpl. fold rle_join. intros xs Hx.
    destruct xs. { discriminate. } destruct xs. { discriminate. }
    apply cons_eq_inj in Hx as [Hrep Hx]. apply cons_eq_inj in Hx as [Hv Hx].
    apply IHxop in Hx. rewrite Hx. reflexivity.
Qed. *)

Fixpoint rle_decomp (ops: rle_ops) :=
match ops with
| Terminate => []
| Rep rep v next => repeat v (uint.nat rep) ++ rle_decomp(next)
end.

Fixpoint rle_byte_decomp (rls: list w8) : (bool * (list w8)) :=
  match rls with
  | [] => (true, [])
  | r_len :: r_v :: rls' =>
    let (rec_s, rec_val) := rle_byte_decomp rls' in
    match rec_s with
    | true => (true, (repeat r_v (uint.nat r_len)) ++ rec_val)
    | false => (false, [])
    end
  | _ :: _ => (false, [])
  end.

Definition rle_logical_byte_decomp (bs: list w8) : (bool * (list w8)) :=
let (p_s, p_v) := (rle_parse bs) in
match p_s with
| true => (true, rle_decomp p_v)
| false => (false, [])
end.

Lemma rle_byte_decomp_soundness (bs xs: list w8) :
rle_logical_byte_decomp bs = (true, xs) -> rle_byte_decomp bs = (true, xs).
Proof.
  intros H2.
  unfold rle_logical_byte_decomp in H2. case_match. case_match.
  - unfold rle_byte_decomp. apply rle_parse_roundtrip in H. inversion H2. destruct H2.
    generalize dependent bs.
    generalize dependent xs.
    induction r.
    + intros xs Hxs. intros bs Hbs. unfold rle_unparse in Hbs. rewrite <- Hbs. reflexivity.
    + intros xs Hxs. intros bs Hbs. unfold rle_unparse in Hbs. fold rle_unparse in Hbs.
      destruct bs. { discriminate Hbs. } destruct bs. { discriminate Hbs. }
      apply cons_eq_inj in Hbs as [Hrep Hbs]. apply cons_eq_inj in Hbs as [Hv Hbs].
      unfold rle_decomp in Hxs. fold rle_decomp in Hxs. assert (rle_decomp r = skipn (uint.nat rep) xs).
      { rewrite <- Hxs. replace (uint.nat rep) with (length (repeat v (uint.nat rep))) at 1. { rewrite drop_app_length. reflexivity. }
        { apply repeat_length. }
      }
      specialize IHr with (drop (uint.nat rep) xs) bs. apply IHr in H.
      ++ rewrite H. unfold rle_decomp. rewrite Hv. rewrite Hrep. reflexivity.
      ++ apply Hbs.
  - discriminate H2.
Qed.

Fixpoint rle_comp (xs: list w8) : rle_ops :=
match xs with
| [] => Terminate
| x :: xs' => match rle_comp xs' with
  | Rep rep x2 next => match ((uint.nat x) =? (uint.nat x2))%nat && (uint.nat rep <? 255%nat)%nat with
    | true => Rep ((W8 ((uint.nat rep) + 1%nat))) x next
    | false => Rep (W8 1) x (Rep rep x2 next)
    end
  | next => Rep (W8 1) x next
  end
end.

Lemma rle_comp_soundness (xs: list w8) :
rle_decomp(rle_comp(xs)) = xs.
Proof.
  induction xs.
  - reflexivity.
  - unfold rle_comp. case_match.
    + fold rle_comp in H. rewrite H in IHxs. unfold rle_decomp in IHxs. rewrite <- IHxs. reflexivity.
    + fold rle_comp in H. rewrite H in IHxs. case_match.
      ++ apply andb_prop in H0.
        destruct H0 as [H_eq H_lt].
        apply Nat.eqb_eq in H_eq.
        apply Nat.ltb_lt in H_lt.
        unfold W8. unfold rle_decomp. fold rle_decomp. rewrite <- IHxs.
        replace (uint.nat (word.of_Z (uint.nat rep + 1%nat))) with (S (uint.nat rep))%nat by word.
        unfold repeat. simpl. unfold repeat. replace a with v by word. reflexivity.
      ++ unfold rle_decomp. fold rle_decomp. rewrite <- IHxs. reflexivity.
Qed.

Lemma rle_unparse_eq (a b: rle_ops) :
(rle_unparse a = rle_unparse b) -> a = b.
Proof.
  intros H.
  generalize dependent b.
  induction a.
  - intros b H. unfold rle_unparse in H. destruct b.
    + reflexivity.
    + discriminate.
  - intros b H. unfold rle_unparse in H. fold rle_unparse in H.
    destruct b. { discriminate H. } unfold rle_unparse in H.
    apply cons_eq_inj in H as [Hrep H]. apply cons_eq_inj in H as [Hv H].
    fold rle_unparse in H. apply IHa in H. rewrite H. rewrite Hv. rewrite Hrep. reflexivity.
Qed.

Lemma rle_parse_unparse (ops: rle_ops) :
rle_parse(rle_unparse ops) = (true, ops).
Proof.
  induction ops.
  - reflexivity.
  - unfold rle_unparse. fold rle_unparse. unfold rle_parse. fold rle_parse.
    rewrite IHops. reflexivity.
Qed.

Lemma rle_total_soundness (xs: list w8) :
rle_byte_decomp (rle_unparse (rle_comp xs)) = (true, xs).
Proof.
  apply rle_byte_decomp_soundness.
  unfold rle_logical_byte_decomp.
  case_match. case_match.
  - apply rle_parse_roundtrip in H.
    apply rle_unparse_eq in H.
    rewrite H. rewrite rle_comp_soundness.
    reflexivity.
  - rewrite rle_parse_unparse in H. discriminate H.
Qed.

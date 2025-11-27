From lz4goose Require Import prelude.
From lz4goose Require Import lz4_spec.

Require Import Coq.Arith.PeanoNat.
Require Import coqutil.Z.bitblast.
Require Import coqutil.Z.Lia.

Fixpoint var_int_unparse (v: nat) : list w8 :=
match (v <? 255)%nat with
| false =>
  match v with
  | S v' => [W8 255%nat] ++ (var_int_unparse (v' - 254)%nat)
  | _ => [] (* impossible *)
  end
| true => [W8 v]
end.

Fixpoint lz4_unparse (seq: lz4_seq) : list w8 :=
match seq with
| LitTerm lit matchlen =>
  match (15 <=? length lit)%nat with
  | true => (W8 ((Nat.shiftl 15%nat 4%nat) + matchlen)%nat) :: (var_int_unparse (length lit - 15)%nat) ++ lit
  | false => (W8 ((Nat.shiftl (length lit) 4%nat) + matchlen)%nat) :: lit
  end
| LitMatchCopy lit offset matchlen next =>
  let b0 := ((Nat.shiftl (Nat.land (length lit) 15%nat) 4%nat)%nat + (Nat.land matchlen 15%nat)%nat)%nat in
  let bs1 : list w8 :=
    match (length lit >=? 15)%nat with
    | true => var_int_unparse (length lit - 15)%nat
    | false => []
    end
  in
  let bs2 :=
    match (matchlen >=? 15)%nat with
    | true => var_int_unparse (matchlen - 15)%nat
    | false => []
    end
  in
  [W8 b0] ++ bs1 ++ [W8 (Nat.land (uint.nat offset) 255)] ++ [W8 (Nat.shiftr (uint.nat offset) 8)] ++ bs2 ++ (lz4_unparse next)
end.

(*
https://github.com/lz4/lz4/blob/dev/doc/lz4_Block_format.md#implementation-notes
Interpreting MB as the older power of 2 definition
*)
Fixpoint valid_to_decompress (seq: lz4_seq) : Prop :=
match seq with
| LitTerm lit matchlen => (length lit) < 4194304 /\ matchlen <= 15
| LitMatchCopy lit offset matchlen next => (length lit) < 4194304 /\ matchlen < 4194304 /\ valid_to_decompress next
end.

Lemma var_int_roundtrip (n: nat) (bs: list w8) (bs': list w8) :
(* (var_int_parse(bs) = (true, n, ((length bs) - (length bs'))%nat) <-> var_int_unparse(n) ++ bs' = bs). *)
(var_int_unparse(n) ++ bs' = bs -> var_int_parse(bs) = (true, n, ((length bs) - (length bs'))%nat)).
Proof.
(* split.
- intros H.
  generalize dependent n.
  generalize dependent bs'.
  induction bs.
  + intros bs' n H. discriminate H.
  + intros bs' n H. unfold var_int_parse in H. case_match.
    * fold var_int_parse in H. case_match. case_match. case_match.
      -- inversion H. assert (n0 = ((length bs) - (length bs')))%nat as Hn0 by word. admit.
      -- inversion H.
    * unfold var_int_unparse. inversion H. rewrite Nat.eqb_neq in H0.
      assert (uint.nat a < 255)%nat as Ha by word. rewrite <- Nat.ltb_lt in Ha.
      simpl.
      destruct (uint.nat a).
        -- admit.
        -- rewrite Ha. *)
- intros H.
  generalize dependent n.
  generalize dependent bs'.
  induction bs.
  + intros bs' n H. unfold var_int_unparse in H. destruct n.
    * discriminate H.
    * case_match; discriminate H.
  + intros bs' n H.
    unfold var_int_parse. case_match.
    * fold var_int_parse. unfold var_int_unparse in H. destruct n.
      -- simpl in H. inversion H. rewrite <- H2 in H0. discriminate H0.
      -- fold var_int_unparse in H. case_match.
        ++ inversion H. rewrite <- H3 in H0. rewrite Nat.eqb_eq in H0. rewrite Nat.ltb_lt in H1. word.
        ++ inversion H. assert (length bs = length bs) as Hlen by reflexivity.
          rewrite <- H4 in Hlen at 1. rewrite length_app in Hlen.
          rewrite H4. apply IHbs in H4. rewrite H4. rewrite Nat.ltb_nlt in H1. rewrite length_cons.
          repeat f_equal; try word.
    * rewrite Nat.eqb_neq in H0. unfold var_int_unparse in H. destruct n.
      -- simpl in H. inversion H. simpl. f_equal; word.
      -- case_match.
        ++ inversion H. simpl. rewrite Nat.ltb_lt in H1. repeat f_equal; try word.
        ++ inversion H. word.
Qed.

Lemma var_int_roundtrip' (n: nat) (bs: list w8) (skip: nat) :
(var_int_parse(bs) = (true, n, skip) -> var_int_unparse(n) ++ (skipn skip bs) = bs).
Proof.
  intros H.
  generalize dependent n.
  generalize dependent skip.
  induction bs.
  - intros skip n H. discriminate H.
  - intros skip n H. unfold var_int_parse in H. case_match.
    + fold var_int_parse in H. case_match. case_match. case_match.
      * admit.
      * inversion H.
    + admit.
Admitted.

Lemma lz4_parse_roundtrip (bs: list w8) (seq: lz4_seq) :
valid_to_decompress seq -> (lz4_parse(bs) = (true, seq) <-> lz4_unparse(seq) = bs).
Proof.
  intros Hv.
  split.
  {
    intros H. induction seq.
    - unfold lz4_unparse. unfold lz4_parse in H. destruct bs.
      + discriminate H.
      + case_match. case_match. case_match.
       * admit.
       * discriminate H.
    - admit.
  }
  {
    intros H. rewrite <- H. clear H.
    induction seq.
    - unfold lz4_unparse. case_match.
      + unfold valid_to_decompress in Hv.
        destruct Hv as [Hlit_lt Hml_lt].
        unfold lz4_parse. assert ((Nat.shiftr (uint.nat (W8 (Nat.shiftl 15 4 + matchlen)%nat)) 4) = 15%nat)%nat as H15.
        {
          simpl. word.
        }
        rewrite H15. replace (15 =? 15)%nat with true by reflexivity.
        remember (var_int_unparse (length lit - 15) ++ lit) as bs2.
        symmetry in Heqbs2.
        pose proof Heqbs2 as Heqbs2'.
        apply var_int_roundtrip in Heqbs2.
        rewrite Heqbs2.
        apply leb_complete in H.
        replace (length lit - 15 + 15)%nat with (length lit) by word.
        rewrite drop_drop.
        assert (length bs2 = length bs2) as Hlen by reflexivity.
        rewrite <- Heqbs2' in Hlen at 1.
        rewrite length_app in Hlen.
        assert (length lit <= length bs2)%nat by word.
        replace (length bs2 - length lit + length lit)%nat with (length bs2) by word.
        rewrite drop_all. rewrite <- Heqbs2'. admit.
      + apply leb_complete_conv in H. unfold lz4_parse. unfold valid_to_decompress in Hv.
        destruct Hv as [_ Hv].
        (* assert (Nat.shiftr (uint.nat (W8 (Nat.shiftl (length lit) 4 + matchlen)%nat)) 4 < 15)%nat. {
          simpl. word.
        } *)
        assert (Nat.shiftr (uint.nat (W8 (Nat.shiftl (length lit) 4 + matchlen)%nat)) 4 = length lit)%nat. {
          simpl. word.
        }
        case_match. case_match.
        * rewrite Nat.eqb_eq in H2. lia.
        * inversion H1. rewrite H0. replace (Nat.land (uint.nat (W8 (Nat.shiftl (length lit) 4 + matchlen)%nat)) 15)%nat with matchlen.
          ++ simpl. rewrite drop_0. rewrite drop_all. rewrite firstn_all. reflexivity.
          ++ assert (15 = Nat.ones 4)%nat as H15 by reflexivity. rewrite H15. rewrite Nat.land_ones.
            unfold W8. admit.
    - unfold valid_to_decompress in Hv. destruct Hv as [Hlit_lt [Hmlen_lt Hv]].
      fold valid_to_decompress in Hv. apply IHseq in Hv.
      unfold lz4_unparse. fold lz4_unparse. unfold "++" at 1. unfold lz4_parse. fold var_int_parse. simpl. case_match. case_match.
      + admit.
      + inversion H. admit.
        Search (drop (length _) _ ).
        Search drop _ (drop _ _ ). 
  }
Admitted.
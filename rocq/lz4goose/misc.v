From lz4goose Require Import prelude.
Require Import PeanoNat.

Lemma lookup_len_is_none {A : Type} (l : list A) (x : A) :
(l !! length l) = None.
Proof.
  induction l.
  - reflexivity.
  - unfold lookup. unfold list_lookup. simpl. apply IHl.
Qed.


Lemma take_eq_cons_greed {A : Type} (l : list A) (l2: list A) (a: A) (i: nat) :
take i l ++ a :: l2 = l -> take (S i) l ++ l2 = l.
Proof.
  revert l.
  induction i as [|i IHi]; intros l H; simpl in *.
  - destruct l as [|x xs]; simpl in *; inversion H; reflexivity.
  - destruct l as [|x xs]; simpl in *; inversion H.
    f_equal.
    apply IHi.
    rewrite H1.
    apply H1.
Qed.

Lemma take_eq_cons_greed2 {A : Type} (l : list A) (l2 : list A) (a : A) (i : nat) :
  take i l ++ a :: l2 = l ->
  l !! i = Some a.
Proof.
  revert l.
  induction i as [|i IHi]; intros l H; simpl in *.
  - destruct l as [|x xs]; simpl in *; inversion H; reflexivity.
  - destruct l as [|x xs]; simpl in *; inversion H.
    apply IHi. rewrite H1. rewrite H1. reflexivity.
Qed.

Lemma take_S {A} (l : list A) (v: A) :
  ∀ (n: nat), (n < length l)%nat -> take (S (n)) (<[n:=v]> l) = take n l ++ [v].
Proof.
  induction l.
  - intros n H. simpl in H. lia.
  - intros n H. rewrite insert_take_drop. { lia. } destruct n.
    + simpl. rewrite take_0. trivial.
    + simpl. f_equal. simpl in H. apply Nat.succ_lt_mono in H. apply IHl in H as H2. rewrite <- H2.
      rewrite insert_take_drop. { lia. } reflexivity.
Qed.



Search (take _ _).
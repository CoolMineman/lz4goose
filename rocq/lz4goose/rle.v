From lz4goose Require Import prelude.

From New.golang.theory Require Import pkg.
From New.proof Require Import std.
Require Import New.code.lz4goose.rle.
Require Import New.generatedproof.lz4goose.rle.


Fixpoint rle_rep (rls: list w8) (xs: list w8) : Prop :=
  match rls with
  | [] => xs = []
  | r_len :: r_v :: xs' => (repeat r_v (uint.nat r_len) = (firstn (uint.nat r_len) xs)) /\
    (rle_rep xs' (skipn (uint.nat r_len) xs))
  | _ :: _ => False
  end.



Fixpoint rle_decomp (rls: list w8) : (bool * (list w8)) :=
  match rls with
  | [] => (true, [])
  | r_len :: r_v :: rls' =>
    let (rec_s, rec_val) := rle_decomp rls' in
    match rec_s with
    | true => (true, (repeat r_v (uint.nat r_len)) ++ rec_val)
    | false => (false, [])
    end
  | _ :: _ => (false, [])
  end.

Example rle_rep_test : rle_rep ([W8 1] ++ [W8 1]) [W8 1].
done.
Qed.

Example rle_decomp_test : rle_decomp ([W8 1] ++ [W8 1]) = (true, [W8 1]).
reflexivity.
Qed.

Example rle_decomp_fail_test : rle_decomp ([W8 1]) = (false, []).
reflexivity.
Qed.

Example rle_rep_test2 : not(rle_rep ([W8 1] ++ [W8 1]) [W8 2]).
intros H.
simpl in H. destruct H. discriminate H.
Qed.

Lemma rle_comp_exists : ∀ (xs: list w8), ∃(comp: list w8), rle_decomp comp = (true, xs).
Proof.
  intros xs. induction xs.
    - exists []. reflexivity.
    - destruct IHxs as [comp Hcomp].
      exists ([W8 1] ++ [a] ++ comp). unfold rle_decomp. unfold rle_decomp in Hcomp.
      simpl. replace (uint.nat (W8 1)) with 1%nat by word.
      simpl. rewrite Hcomp. reflexivity.
Qed.

Lemma rle_join: ∀ (rl xs rl2 xs2: list w8), rle_decomp rl = (true, xs) /\ rle_decomp rl2 = (true, xs2) -> rle_decomp (rl ++ rl2) = (true, xs ++ xs2).
Proof.
  intros rl xs rl2 xs2.
  induction rl.
  - simpl. intros [H1 H2]. inversion H1. inversion H2. rewrite app_nil_l. apply H3.
  - induction rl.
    + intros [H H2]. discriminate H.
    + intros [Hrl Hrl2]. unfold rle_decomp in Hrl. simpl in Hrl.
Admitted. 

Lemma rle_comp_end : ∀ (rls xs: list w8), (∃(comp: list w8), rle_decomp (rls ++ comp) = (true, xs)) -> rle_decomp rls = (true, xs).
Proof.
Admitted.

Section wps.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit rle := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf rle := build_get_is_pkg_init_wf.

Check own_slice.

(*

*)

Lemma le_thingy (a b c: Z) :
  (a < b /\ b ≤ c) -> a < b.
Proof.
  word.
Qed.

Lemma wp_DecompressRle (s_src s_dst: slice.t) (q: dfrac) (src dst: list w8) :
{{{
  is_pkg_init rle ∗
  "Hsrc" ∷ s_src ↦*{q} src ∗
  "Hdst" ∷ s_dst ↦* dst ∗
  "%Hvalid" ∷ ⌜∃(expected: list w8), rle_decomp src = (true, expected)⌝ ∗
  "%Hsrc_len" ∷ ⌜length src < 17000⌝
}}}
    @! rle.DecompressRle #s_dst #s_src
{{{ (r: w64), RET #r; ⌜
  let (d_s, d_vs) := (rle_decomp src) in
    d_s = true /\ r = W64 (length d_vs) /\ firstn (length d_vs) dst = d_vs
  ⌝
}}}.
Proof.
  wp_start as "H". iNamed "H".
  wp_auto.
  destruct Hvalid as [xs Hvalid].
  iAssert (∃ (i out: w64),
    "i" ∷ i_ptr ↦ i ∗
    "out" ∷ out_ptr ↦ out ∗
    "%Hi_le" ∷ ⌜uint.nat i <= length src⌝ ∗
    "%H_rep" ∷ ⌜let (_, xs') := rle_decomp (skipn (uint.nat i) src) in (firstn (uint.nat out) dst) ++ xs' = xs⌝
  )%I with "[$i $out]" as "IH".
  {
    iPureIntro. unfold W64. replace (uint.nat (word.of_Z 0)) with 0%nat by word.
    simpl. replace (drop 0 src) with src by reflexivity.
    rewrite Hvalid. split.
    { word. }
    { trivial. }
  }
  wp_for.
  iNamed "IH".
  wp_auto.
  wp_if_destruct.
  - iDestruct (own_slice_len with "[$Hsrc]") as "%Hsrc_len2".
    wp_bind (![_] (slice.elem_ref _ _ _))%E.
    iApply (wp_load_slice_elem' with "[Hsrc]").
    {
      word.
    }
    {
      iFrame. iPureIntro. destruct src.
        - simpl rle_decomp in Hvalid. inversion Hvalid as [Hxs].
          rewrite drop_nil in H_rep. simpl in H_rep.
          rewrite app_nil_r in H_rep. rewrite <- Hxs in H_rep.
          destruct Hsrc_len2 as [Hsrc_len_a Hsrc_len_b].
          simpl in Hi_le. assert (uint.Z i = 0) as H0 by word.
          rewrite H0 in l. simpl in Hsrc_len_a.
          assert (uint.Z (slice.len_f s_src) = 0) by word.
          assert (0 < 0) as Hfalse by word.
          discriminate Hfalse.
        - admit.
    }
    iModIntro. iIntros "Hsrc". wp_auto.
    admit.
  - wp_finish. iPureIntro. rewrite Hvalid. split.
    + trivial.
    +  split.
      ++ admit.
      ++ assert 

Admitted.

End wps.

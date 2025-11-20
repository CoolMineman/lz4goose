From lz4goose Require Import prelude.

From New.golang.theory Require Import pkg.
From New.proof Require Import std.
Require Import New.code.lz4goose.rle.
Require Import New.generatedproof.lz4goose.rle.
Require Import Coq.Init.Nat.
From lz4goose Require Import rle_pure.
From lz4goose Require Import misc.

Section wps.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit rle := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf rle := build_get_is_pkg_init_wf.

Lemma parse_unparse_succeeds (r r2: rle_ops) :
not (rle_parse (rle_unparse r) = (false, r2)).
intros H.
assert (∃(r3: rle_ops), rle_parse (rle_unparse r) = (true, r3)).
- exists r. apply rle_parse_roundtrip2. reflexivity.
- destruct H0. rewrite H in H0. discriminate H0.
Qed.

Lemma wp_DecompressRle (s_src s_dst: slice.t) (q: dfrac) (src dst: list w8) :
{{{
  is_pkg_init rle ∗
  "Hsrc" ∷ s_src ↦*{q} src ∗
  "Hdst" ∷ s_dst ↦* dst ∗
  "%Hvalid" ∷ ⌜
    ∃(expected: list w8),
    rle_logical_byte_decomp src = (true, expected) /\
    length expected < 17000 /\ length expected <= length dst
  ⌝
}}}
    @! rle.DecompressRle #s_dst #s_src
{{{ (dst': list w8) (b: bool) (r: w64), RET (#r, #b);
  "Hsrc" ∷ s_src ↦*{q} src ∗
  "Hdst" ∷ s_dst ↦* dst' ∗
  "%Hvalid" ∷ ⌜∃(expected: list w8),
    rle_logical_byte_decomp src = (true, expected) /\
    r = W64 (length expected) /\
    firstn (uint.nat r) dst' = expected
  ⌝
}}}.
Proof.
  wp_start as "H". iNamed "H". destruct Hvalid as [expected Hvalid].
  destruct Hvalid as [Hvalid [Hmax Hdst_lt]].
  unfold rle_logical_byte_decomp in Hvalid. case_match. case_match.
  - inversion Hvalid as [Hr]. clear Hvalid. apply rle_parse_roundtrip in H. rewrite <- H. clear H0 b.
    wp_auto.
    iAssert (∃ (i out: w64) (dst: list w8),
      "i" ∷ i_ptr ↦ i ∗
      "out" ∷ out_ptr ↦ out ∗
      "Hdst" ∷ s_dst ↦* dst ∗
      "%Hdst_l" ∷ ⌜length expected ≤ length dst⌝ ∗
      "%Hi_le" ∷ ⌜uint.nat i <= length src⌝ ∗
      "%Hi_ge" ∷ ⌜0 ≤ sint.Z i⌝ ∗
      "%H_out" ∷ ⌜(length dst >= uint.nat out)%nat⌝ ∗
      "%H_out_ge" ∷ ⌜(0 ≤ sint.Z out)⌝ ∗
      "%H_rep" ∷ ⌜
        ∃(r': rle_ops),
        let (success, xs') := rle_logical_byte_decomp (rle_unparse r') in
        (firstn (uint.nat out) dst) ++ xs' = expected /\ success = true /\
        src = (firstn (uint.nat i) src) ++ (rle_unparse r')
      ⌝
    )%I with "[$i $out $Hdst]" as "IH". {
      iPureIntro. repeat split; try word. exists r. case_match. unfold rle_logical_byte_decomp in H0. case_match.
      case_match.
      - inversion H. repeat split; try trivial.
        + replace (uint.nat (W64 0)) with 0%nat by word. simpl. rewrite H3 in H1. apply rle_parse_roundtrip in H1.
          inversion H0. rewrite <- H1 in H3. apply rle_unparse_eq in H3. rewrite <- H3. apply Hr.
        + inversion H0. reflexivity. 
      - apply parse_unparse_succeeds in H1. lia.
    }
    wp_for. iNamed "IH". wp_auto. destruct H_rep as [r' H_rep]. case_match. destruct H_rep as [Hexp [Hb Hsrc]].
    iDestruct (own_slice_len with "[$Hsrc]") as "%Hsrc_len2". destruct Hsrc_len2 as [Hsrc_len2 Hsrc_len3].
    destruct r'.
    + (* Terminate *) 
      wp_if_destruct.
      * exfalso. rewrite app_nil_r in Hsrc. assert (uint.nat i < sint.nat (slice.len_f s_src)) by word.
        rewrite <- Hsrc_len2 in H. rewrite Hsrc in H.
        assert (length (take (uint.nat i) (rle_unparse r)) <= uint.nat i)%nat. { apply firstn_le_length. } lia.
      * wp_finish. iFrame. iPureIntro. exists (rle_decomp r). repeat split.
        ++ unfold rle_logical_byte_decomp. case_match. case_match.
          +++ apply rle_parse_roundtrip in H. apply rle_unparse_eq in H. rewrite H. reflexivity.
          +++ apply parse_unparse_succeeds in H. lia.
        ++ simpl in H0. unfold rle_logical_byte_decomp in H0. inversion H0. rewrite <- Hexp. rewrite <- H1.
          rewrite app_nil_r. rewrite firstn_length_le. { word. } word.
        ++ simpl in H0. inversion H0. rewrite <- H1 in Hexp. rewrite app_nil_r in Hexp. apply Hexp.
    + (* Rep r v r' *)
      unfold rle_unparse in Hsrc. fold rle_unparse in Hsrc.
      symmetry in Hsrc. apply take_eq_cons_greed2 in Hsrc as Hsrc1.
      apply take_eq_cons_greed in Hsrc. apply take_eq_cons_greed2 in Hsrc as Hsrc2.
      apply take_eq_cons_greed in Hsrc. unfold rle_unparse in H0. fold rle_unparse in H0.
      unfold rle_logical_byte_decomp in H0. simpl in H0. fold rle_parse in H0.
      rewrite rle_parse_unparse in H0. unfold rle_decomp in H0. fold rle_decomp in H0. inversion H0.
      wp_if_destruct.
      * wp_if_destruct.
        ** apply lookup_lt_Some in Hsrc2. rewrite Hsrc_len2 in Hsrc2. word.
        ** wp_bind (![_] (slice.elem_ref _ _ _))%E.
          iApply (wp_load_slice_elem' with "[Hsrc]").
          { apply Hi_ge. } { iFrame. iPureIntro. replace (sint.nat i) with (uint.nat i) by word. apply Hsrc1. }
          iModIntro. iIntros "Hsrc".
          wp_auto.
          wp_bind (![_] (slice.elem_ref _ _ _))%E.
          iApply (wp_load_slice_elem' with "[Hsrc]").
          { word. } { iFrame. iPureIntro. replace (sint.nat (word.add i (W64 1))) with (S(uint.nat i)) by word. apply Hsrc2. }
          iModIntro. iIntros "Hsrc".
          wp_auto.
          iAssert (∃ (j out: w64) (dst: list w8),
            "j" ∷ j_ptr ↦ j ∗
            "Hdst" ∷ s_dst ↦* dst ∗
            "%Hdst_l" ∷ ⌜length (rle_decomp r) ≤ length dst⌝ ∗
            "out" ∷ out_ptr ↦ out ∗
            "%Hi_le" ∷ ⌜uint.nat j <= uint.nat rep⌝ ∗
            "%Hi_ge" ∷ ⌜0 ≤ sint.Z j⌝ ∗
            "%H_out" ∷ ⌜(length dst >= uint.nat out)%nat⌝ ∗
            "%H_out_ge" ∷ ⌜(0 ≤ sint.Z out)⌝ ∗
            "%H_rep" ∷ ⌜
              take (uint.nat out) dst ++ (repeat v ((uint.nat rep) - (uint.nat j))) ++ rle_decomp r' = rle_decomp r
            ⌝
          )%I with "[$j $out $Hdst]" as "IH". {
            iFrame. iPureIntro. repeat split; try word.
            replace (uint.nat rep - uint.nat (W64 0))%nat with (uint.nat rep) by word. apply Hexp.
          }
          wp_for. iNamed "IH". wp_auto.
          wp_if_destruct.
          {
            iDestruct (own_slice_len with "[$Hdst]") as "%Hdst_len2". destruct Hdst_len2 as [Hdst_len2 Hdst_len3].
            wp_if_destruct.
            - exfalso. remember (uint.nat rep) as repn. destruct repn. { word. }
              assert (sint.nat (slice.len_f s_dst) ≤ uint.nat out0) as Hout_lt by word. rewrite <- Hdst_len2 in Hout_lt.
              assert (uint.nat out0 = length dst1) as Hout by word. rewrite <- Hout in Hdst_l0.
              assert (length (rle_decomp r) > uint.nat out0). {
                rewrite <- H_rep. repeat rewrite list.length_app. rewrite take_ge. { word. }
                replace (S repn - uint.nat j)%nat with (S (repn - uint.nat j)%nat) by word.
                unfold repeat. rewrite <- Hout. unfold length. word.
              }
              word.
            - wp_bind ((slice.elem_ref _ _ _) <-[_] _)%E.
              iApply (wp_store_slice_elem' with "[Hdst]"). { iFrame. iPureIntro. split; word. }
              iModIntro. iIntros "Hdst". wp_auto. wp_for_post. iFrame. iPureIntro. repeat split; try rewrite length_insert; try word. 
              * replace (uint.nat (word.add out0 (W64 1))) with (S (sint.nat out0)) by word. rewrite take_S. { word. }
                rewrite <- H_rep. remember (uint.nat rep - uint.nat j)%nat as reps. destruct reps.
                  + word.
                  + replace (uint.nat (word.add j (W64 1)))%nat with (S (uint.nat j))%nat by word.
                    replace (uint.nat rep - S (uint.nat j))%nat with reps by word. rewrite <- app_assoc. unfold repeat.
                    rewrite cons_middle. replace (sint.nat out0) with (uint.nat out0) by word. reflexivity.
          }
          {
            wp_for_post. iFrame. iPureIntro. repeat split; try word.
            exists r'. unfold rle_logical_byte_decomp. (* TODO: Make a parse unparse eq lemma *)
            case_match. case_match. case_match.
            - repeat split.
              + inversion H. inversion H1. apply rle_parse_roundtrip in H7. apply rle_unparse_eq in H7. rewrite H7.
                replace (uint.nat rep - uint.nat j)%nat with 0%nat in H_rep by word. simpl in H_rep. apply H_rep.
              + inversion H. trivial.
              + replace (uint.nat (word.add i (W64 2))) with (S (S (uint.nat i))) by word. symmetry. apply Hsrc.
            - apply parse_unparse_succeeds in H1. lia.
          }
      * apply lookup_lt_Some in Hsrc1. rewrite Hsrc_len2 in Hsrc1. word.
  - discriminate Hvalid.
Qed.

End wps.


From lz4goose Require Import prelude.

From New.golang.theory Require Import pkg.
From New.proof Require Import std.
Require Import New.code.lz4goose.testing.
Require Import New.generatedproof.lz4goose.testing.
(* From lz4goose Require Import functional_init. *)

Section wps.
(* Context `{!heapGS Σ}.
Context `{!globalsGS Σ} {go_ctx:GoContext}. *)
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit testing := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf testing := build_get_is_pkg_init_wf.

Lemma wp_TwoPlusTwo :
{{{ is_pkg_init testing }}}
    @! testing.TwoPlusTwo #()
{{{ (r: w64), RET #r; ⌜r = 4⌝ }}}.
Proof.
    wp_start. wp_finish.
Qed.

End wps.

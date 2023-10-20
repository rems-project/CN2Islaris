(*Automatically generated Islaris spec and proof from CN *)

Require Import isla.aarch64.aarch64.
Require Import fromCN.array_read.O2.instructions.instrs.


Section iris.

Context `{!islaG Σ} `{!threadG}.

Definition get1_spec : iProp Σ :=
  c_call
    128
    (λ args sp RET,
      ∃ (pairStart : list (bv 64)),
      let pair_p := args !!! 0%nat in
      bv_unsigned pair_p ↦ₘ∗ pairStart ∗
      ⌜2 = length pairStart⌝ ∗
      ⌜bv_unsigned pair_p + 16 < 2 ^ 52⌝ ∗
      ⌜((bv_unsigned pair_p mod 8) = 0)⌝ ∗
      ⌜((bv_unsigned sp mod 8) = 0)⌝ ∗
      RET (λ rets,
        ∃ (pairEnd : list (bv 64)),
        let ret := (rets !!! 0%nat) in
        bv_unsigned pair_p ↦ₘ∗ pairEnd ∗
        ⌜2 = length pairEnd⌝ ∗
        ⌜bv_unsigned pair_p + 16 < 2 ^ 52⌝ ∗
        ⌜(pairStart = pairEnd)⌝ ∗
        ⌜(bv_unsigned ret = (bv_unsigned (pairEnd !!! 1%nat)))⌝ ∗
        True))%I.

Arguments get1_spec /.

Lemma get1:
  instr 0x210120 (Some a210120) -∗
  instr 0x210124 (Some a210124) -∗
  instr_body 0x210120 get1_spec.
Proof.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  apply list_lookup_total_correct in H6.
  rewrite -bv_eq -H6.
  f_equal.
  bv_solve.
Qed.

End iris.

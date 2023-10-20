(*Automatically generated Islaris spec and proof from CN *)

Require Import isla.aarch64.aarch64.
Require Import fromCN.array_write.O0.instructions.instrs.


Section iris.

Context `{!islaG Σ} `{!threadG}.

Definition write1_spec : iProp Σ :=
  c_call
    128
    (λ args sp RET,
      ∃ (pairStart : list (bv 64)),
      let pair_p := args !!! 0%nat in
      let value := args !!! 1%nat in
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
        ⌜((bv_unsigned (pairEnd !!! 1%nat)) = bv_unsigned value)⌝ ∗
        True))%I.

Arguments write1_spec /.

Lemma write1:
  instr 0x210120 (Some a210120) -∗
  instr 0x210124 (Some a210124) -∗
  instr 0x210128 (Some a210128) -∗
  instr 0x21012c (Some a21012c) -∗
  instr 0x210130 (Some a210130) -∗
  instr 0x210134 (Some a210134) -∗
  instr 0x210138 (Some a210138) -∗
  instr 0x21013c (Some a21013c) -∗
  instr_body 0x210120 write1_spec.
Proof.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  all: bv_simplify.
  all: have ->: Z.to_nat ((bv_wrap 52 (bv_unsigned b0 + 8) - bv_unsigned b0) `div` 8) = 1%nat; [bv_solve|].
  - destruct pairStart as [|?[|??]]; [done|done|eauto].
  - rewrite list_lookup_total_insert; [bv_solve|bv_solve].
Qed.

End iris.

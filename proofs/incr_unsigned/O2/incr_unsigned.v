(*Automatically generated Islaris spec and proof from CN *)

Require Import isla.aarch64.aarch64.
Require Import fromCN.examples.incr_unsigned.O2.instructions.instrs.


Section iris.

Context `{!islaG Σ} `{!threadG}.

Definition main_spec : iProp Σ :=
  c_call
    128
    (λ args sp RET,
      ⌜((bv_unsigned sp mod 8) = 0)⌝ ∗
      RET (λ rets,
        let ret := (rets !!! 0%nat) in
        ⌜(bv_unsigned ret = 1)⌝ ∗
        True))%I.

Arguments main_spec /.

Definition incr_spec : iProp Σ :=
  c_call
    128
    (λ args sp RET,
      let i := args !!! 0%nat in
      ⌜(bv_unsigned i < ((2 ^ 64)%Z - 1)%Z)⌝ ∗
      ⌜((bv_unsigned sp mod 8) = 0)⌝ ∗
      RET (λ rets,
        let ret := (rets !!! 0%nat) in
        ⌜(bv_unsigned ret = (bv_unsigned i + 1)%Z)⌝ ∗
        True))%I.

Arguments incr_spec /.

Lemma main:
  instr 0x210128 (Some a210128) -∗
  instr 0x21012c (Some a21012c) -∗
  instr_body 0x210128 main_spec.
Proof.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
Qed.

Lemma incr:
  instr 0x210120 (Some a210120) -∗
  instr 0x210124 (Some a210124) -∗
  instr_body 0x210120 incr_spec.
Proof.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
Qed.

End iris.

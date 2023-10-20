(*Automatically generated Islaris spec and proof from CN *)

Require Import isla.aarch64.aarch64.
Require Import fromCN.incr_mem_sub.O0.instructions.instrs.


Section iris.

Context `{!islaG Σ} `{!threadG}.

Definition main_spec : iProp Σ :=
  c_call
    256
    (λ args sp RET,
      ⌜((bv_unsigned sp mod 8) = 0)⌝ ∗
      RET (λ rets,
        let ret := (rets !!! 0%nat) in
        ⌜(bv_unsigned ret = 0)⌝ ∗
        True))%I.

Arguments main_spec /.

Definition incr_spec : iProp Σ :=
  c_call
    128
    (λ args sp RET,
      ∃ (iStart : bv 64),
      let i := args !!! 0%nat in
      bv_unsigned i ↦ₘ iStart ∗
      ⌜bv_unsigned i  < 2 ^ 52⌝ ∗
      ⌜(bv_unsigned iStart < ((2 ^ 64)%Z - 1)%Z)⌝ ∗
      ⌜((bv_unsigned i mod 8) = 0)⌝ ∗
      ⌜((bv_unsigned sp mod 8) = 0)⌝ ∗
      RET (λ rets,
        ∃ (iEnd : bv 64),
        let ret := (rets !!! 0%nat) in
        bv_unsigned i ↦ₘ iEnd ∗
        ⌜(bv_unsigned ret = bv_unsigned iEnd)⌝ ∗
        ⌜(bv_unsigned iEnd = (bv_unsigned iStart + 1)%Z)⌝ ∗
        True))%I.

Arguments incr_spec /.

Lemma main:
  instr 0x21014c (Some a21014c) -∗
  instr 0x210150 (Some a210150) -∗
  instr 0x210154 (Some a210154) -∗
  instr 0x210158 (Some a210158) -∗
  instr 0x21015c (Some a21015c) -∗
  instr 0x210160 (Some a210160) -∗
  instr 0x210164 (Some a210164) -∗
  instr 0x210168 (Some a210168) -∗
  instr 0x21016c (Some a21016c) -∗
  instr 0x210170 (Some a210170) -∗
  instr 0x210174 (Some a210174) -∗
  instr 0x210178 (Some a210178) -∗
  instr 0x21017c (Some a21017c) -∗
  instr 0x210180 (Some a210180) -∗
  instr 0x210184 (Some a210184) -∗
  □ instr_pre 0x210120 incr_spec -∗
  instr_body 0x21014c main_spec.
Proof.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
Qed.

Lemma incr:
  instr 0x210120 (Some a210120) -∗
  instr 0x210124 (Some a210124) -∗
  instr 0x210128 (Some a210128) -∗
  instr 0x21012c (Some a21012c) -∗
  instr 0x210130 (Some a210130) -∗
  instr 0x210134 (Some a210134) -∗
  instr 0x210138 (Some a210138) -∗
  instr 0x21013c (Some a21013c) -∗
  instr 0x210140 (Some a210140) -∗
  instr 0x210144 (Some a210144) -∗
  instr 0x210148 (Some a210148) -∗
  instr_body 0x210120 incr_spec.
Proof.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
Qed.

End iris.

(*Automatically generated Islaris spec and proof from CN *)

Require Import isla.aarch64.aarch64.
Require Import fromCN.conditional.O2.instructions.instrs.


Section iris.

Context `{!islaG Σ} `{!threadG}.

Definition incr_twice_neq_zero_spec : iProp Σ :=
  c_call
    128
    (λ args sp RET,
      let i := args !!! 0%nat in
      ⌜(bv_unsigned i < ((2 ^ 64)%Z - 2)%Z)⌝ ∗
      ⌜((bv_unsigned sp mod 8) = 0)⌝ ∗
      RET (λ rets,
        let ret := (rets !!! 0%nat) in
        ⌜(bv_unsigned ret = (if (bv_unsigned i =? 0) then (bv_unsigned i + 1)%Z else (bv_unsigned i + 2)%Z))⌝ ∗
        True))%I.

Arguments incr_twice_neq_zero_spec /.

Lemma incr_twice_neq_zero:
  instr 0x210120 (Some a210120) -∗
  instr 0x210124 (Some a210124) -∗
  instr 0x210128 (Some a210128) -∗
  instr 0x21012c (Some a21012c) -∗
  instr_body 0x210120 incr_twice_neq_zero_spec.
Proof.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  - have: bv_unsigned b0 ≠ 0; [bv_simplify H4; bv_solve|shelve].
  - have: bv_unsigned b0 = 0; [bv_simplify H4; bv_solve|shelve].
  Unshelve.
  all: destruct (bv_unsigned b0 =? 0) eqn:b0Eq.
  all: rewrite -?not_true_iff_false Z.eqb_eq in b0Eq; bv_solve.
Qed.

End iris.

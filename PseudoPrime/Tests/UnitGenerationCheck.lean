/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Part1ProductCheck

/-! # Regression boundaries of finite LLS unit-generation checks

These kernel computations cover the cap transition, representative residue structures, target
bounds, and deliberately invalid generator or divisor data. The rejection cases preserve the
checks that make divisor coverage sound; no search result or external factorization is trusted.

Keep this regression module outside finite certificate imports. Adding or editing tests or proof
dependencies here must not invalidate the expensive certificate blocks.
-/

@[expose] public section

namespace PseudoPrime.Tests

/-- The original product data and submitted divisor mask cover this modulus.
Proof: kernel computation. Role: preserve the finite checker regression boundary. -/
theorem unitCoverage_good_5 :
    LLS.unitGenerationCoverCheck 5 (LLS.part1PrimeCap 5) (Nat.log2 5 + 1) 258 5 = true := by
  decide +kernel

/-- The original product data and submitted divisor mask cover this modulus.
Proof: kernel computation. Role: preserve the finite checker regression boundary. -/
theorem unitCoverage_good_8 :
    LLS.unitGenerationCoverCheck 8 (LLS.part1PrimeCap 8) (Nat.log2 8 + 1) 34865283 8194 = true := by
  decide +kernel

/-- The original product data and submitted divisor mask cover this modulus.
Proof: kernel computation. Role: preserve the finite checker regression boundary. -/
theorem unitCoverage_good_704 :
    LLS.unitGenerationCoverCheck 704 (LLS.part1PrimeCap 704) (Nat.log2 704 + 1) 9277164229635
        3222704130 =
      true := by
  decide +kernel

/-- The original product data and submitted divisor mask cover this modulus.
Proof: kernel computation. Role: preserve the finite checker regression boundary. -/
theorem unitCoverage_good_705 :
    LLS.unitGenerationCoverCheck 705 (LLS.part1PrimeCap 705) (Nat.log2 705 + 1) 9552042661634
        282286726217731 =
      true := by
  decide +kernel

/-- The original product data and submitted divisor mask cover this modulus.
Proof: kernel computation. Role: preserve the finite checker regression boundary. -/
theorem unitCoverage_good_2048 :
    LLS.unitGenerationCoverCheck 2048 (LLS.part1PrimeCap 2048) (Nat.log2 2048 + 1) 34897923 40962 =
      true := by
  decide +kernel

/-- The original product data and submitted divisor mask cover this modulus.
Proof: kernel computation. Role: preserve the finite checker regression boundary. -/
theorem unitCoverage_good_2520 :
    LLS.unitGenerationCoverCheck 2520 (LLS.part1PrimeCap 2520) (Nat.log2 2520 + 1)
        713079987039861748794125 83026744340354871298 =
      true := by
  decide +kernel

/-- The original product data and submitted divisor mask cover this modulus.
Proof: kernel computation. Role: preserve the finite checker regression boundary. -/
theorem unitCoverage_good_2999 :
    LLS.unitGenerationCoverCheck 2999 (LLS.part1PrimeCap 2999) (Nat.log2 2999 + 1) 191889 2999 =
      true := by
  decide +kernel

/-- Invalid certificate data is rejected by the executable coverage checker.
Proof: kernel computation. Role: preserve the finite checker regression boundary. -/
theorem unitCoverage_reject_composite :
    LLS.unitGenerationCoverCheck 5 19 (Nat.log2 5 + 1) 264 5 = false :=
  of_decide_eq_true rfl

/-- Invalid certificate data is rejected by the executable coverage checker.
Proof: kernel computation. Role: preserve the finite checker regression boundary. -/
theorem unitCoverage_reject_nonunit_generator :
    LLS.unitGenerationCoverCheck 5 19 (Nat.log2 5 + 1) 18088194 5 = false :=
  of_decide_eq_true rfl

/-- Invalid certificate data is rejected by the executable coverage checker.
Proof: kernel computation. Role: preserve the finite checker regression boundary. -/
theorem unitCoverage_reject_cap : LLS.unitGenerationCoverCheck 5 1 (Nat.log2 5 + 1) 258 5 = false :=
  of_decide_eq_true rfl

/-- Invalid certificate data is rejected by the executable coverage checker.
Proof: kernel computation. Role: preserve the finite checker regression boundary. -/
theorem unitCoverage_reject_missing_products :
    LLS.unitGenerationCoverCheck 5 19 (Nat.log2 5 + 1) 0 5 = false :=
  of_decide_eq_true rfl

/-- Invalid certificate data is rejected by the executable coverage checker.
Proof: kernel computation. Role: preserve the finite checker regression boundary. -/
theorem unitCoverage_reject_unit_divisor :
    LLS.unitGenerationCoverCheck 5 19 (Nat.log2 5 + 1) 0 12289 = false :=
  of_decide_eq_true rfl

/-- Invalid certificate data is rejected by the executable coverage checker.
Proof: kernel computation. Role: preserve the finite checker regression boundary. -/
theorem unitCoverage_reject_nondivisor :
    LLS.unitGenerationCoverCheck 5 19 (Nat.log2 5 + 1) 258 8194 = false :=
  of_decide_eq_true rfl

/-- Invalid certificate data is rejected by the executable coverage checker.
Proof: kernel computation. Role: preserve the finite checker regression boundary. -/
theorem unitCoverage_reject_shallow_mask :
    LLS.unitGenerationCoverCheck 8 19 (Nat.log2 8 + 1) 34865283 2 = false :=
  of_decide_eq_true rfl

/-- Invalid certificate data is rejected by the executable coverage checker.
Proof: kernel computation. Role: preserve the finite checker regression boundary. -/
theorem unitCoverage_reject_empty_mask :
    LLS.unitGenerationCoverCheck 5 19 (Nat.log2 5 + 1) 258 0 = false :=
  of_decide_eq_true rfl

/-- The lower finite cap applies immediately below the transition.
Proof: kernel computation. Role: preserve the finite checker regression boundary. -/
theorem part1_cap_below_705 : LLS.part1PrimeCap 704 = 19 :=
  of_decide_eq_true rfl

/-- The upper finite cap applies at the transition.
Proof: kernel computation. Role: preserve the finite checker regression boundary. -/
theorem part1_cap_at_705 : LLS.part1PrimeCap 705 = 43 :=
  of_decide_eq_true rfl

/-- Padding starts exactly at the first modulus outside the target range.
Proof: kernel computation. Role: preserve the finite checker regression boundary. -/
theorem part1_padding_from_3000 : LLS.part1ProductLeaf 2949 #[] #[] 51 = true :=
  of_decide_eq_true rfl

/-- Out-of-range padding needs no submitted code or divisor data.
Proof: kernel computation. Role: preserve the finite checker regression boundary. -/
theorem part1_padding_start_3000 : LLS.part1ProductLeaf 3000 #[] #[] 0 = true :=
  of_decide_eq_true rfl

/-- The final in-range modulus still rejects missing product coverage.
Proof: kernel computation. Role: preserve the finite checker regression boundary. -/
theorem part1_last_modulus_checked : LLS.part1ProductLeaf 2999 #[0] #[2999] 0 = false := by
  decide +kernel

end PseudoPrime.Tests

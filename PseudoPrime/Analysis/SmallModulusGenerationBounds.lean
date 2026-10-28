/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.UnitGenerationBalanced
public import PseudoPrime.LLS.ParityRationalWitnessProfiles
public import PseudoPrime.LLS.SmallModulusGenerationBounds2

/-! # Transferring finite generation certificates to the parity profile

Proper subgroups omit an eligible prime from every valid generation tree.
The analytic profile exceeds seven for q ≥ 3 and eighty-one for q ≥ 8,
so uniform integer caps suffice for the finite small-modulus extension.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For q ≥ 3, the parity profile square is at least seven.
Use log 3 > 1 and nonnegative log-log to bound its positive root.
This accommodates the smallest finite generation certificates. -/
theorem parity_square_ge_seven {q : ℕ} (hq : 3 ≤ q) :
    (7 : ℝ) ≤ (Real.log q + (42589 / 7000 : ℝ) * Real.log (Real.log q) + 77 / 25) ^ 2 := by
  have h3 : (1 : ℝ) < Real.log 3 :=
    (Real.lt_log_iff_exp_lt (by norm_num only : (0 : ℝ) < 3)).mpr Real.exp_one_lt_three
  have hlog := Real.log_le_log (by norm_num only : (0 : ℝ) < 3) (Nat.cast_le.mpr hq)
  have hL : 1 ≤ Real.log q := le_of_lt (h3.trans_le hlog)
  have hz := Real.log_nonneg hL
  have hroot : 3 ≤ Real.log q + (42589 / 7000 : ℝ) * Real.log (Real.log q) + 77 / 25 := by
    linarith only [hL, hz]
  nlinarith only [sq_nonneg (Real.log q + (42589 / 7000 : ℝ) * Real.log (Real.log q) + 77 / 25 - 3),
    hroot]

end PseudoPrime.Analysis

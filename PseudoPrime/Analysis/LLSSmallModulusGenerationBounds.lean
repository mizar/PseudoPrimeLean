/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.UnitGenerationBalanced
public import PseudoPrime.LLS.ParityRationalWitnessProfiles
public import PseudoPrime.Analysis.SmallModulusGenerationBounds

/-! # Transferring finite generation certificates to the parity profile

Proper subgroups omit an eligible prime from every valid generation tree.
The analytic profile exceeds seven for q ≥ 3 and eighty-one for q ≥ 8,
so uniform integer caps suffice for the finite small-modulus extension.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For q ≥ 8, the parity profile square is at least eighty-one.
Use log 8 > 2 and log 2's rational lower bound to obtain root at least nine.
This permits a common integer prime cap for all remaining small moduli. -/
theorem parity_square_ge_eighty_one {q : ℕ} (hq : 8 ≤ q) :
    (81 : ℝ) ≤ (Real.log q + (42589 / 7000 : ℝ) * Real.log (Real.log q) + 77 / 25) ^ 2 := by
  have hlog := Real.log_le_log (by norm_num only : (0 : ℝ) < 8) (Nat.cast_le.mpr hq)
  have h8 : (2 : ℝ) < Real.log 8 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_gt_d9]
  have hL : 2 ≤ Real.log q := le_of_lt (h8.trans_le hlog)
  have hz := Real.log_le_log (by norm_num only : (0 : ℝ) < 2) hL
  have hroot : 9 ≤ Real.log q + (42589 / 7000 : ℝ) * Real.log (Real.log q) + 77 / 25 := by
    linarith only [hL, hz, Real.log_two_gt_d9]
  nlinarith only [sq_nonneg (Real.log q + (42589 / 7000 : ℝ) * Real.log (Real.log q) + 77 / 25 - 9),
    hroot]

end PseudoPrime.Analysis

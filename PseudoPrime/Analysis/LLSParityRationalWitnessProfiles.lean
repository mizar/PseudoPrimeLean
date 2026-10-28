/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RationalTheorem11S1Subgroup
public import PseudoPrime.LLS.RationalProfileContracts
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactorParitySplitBounds
public import PseudoPrime.LLS.ParityRationalWitnessProfiles2

/-! # Parity-improved rational Part 1 profile from 3000 -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For L ≥ 8, the new parity profile square is strictly below the former
Part 1 profile square. The logarithm of L exceeds two, so the decrease in its coefficient
outweighs the increased constant. This removes the former tuple on its whole eligible domain. -/
theorem parity_shift_sq_lt_original {L : ℝ} (hL : 8 ≤ L) :
    (L + (42589 / 7000 : ℝ) * Real.log L + 77 / 25) ^ 2 <
      (L + (1791 / 250 : ℝ) * Real.log L + 499 / 250) ^ 2 := by
  have hlog := Real.log_le_log (by norm_num only : (0 : ℝ) < 8) hL
  have h8 : (2 : ℝ) < Real.log 8 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_gt_d9]
  have hroot :
    L + (42589 / 7000 : ℝ) * Real.log L + 77 / 25 <
      L + (1791 / 250 : ℝ) * Real.log L + 499 / 250 := by
    linarith only [hlog, h8]
  apply
    (sq_lt_sq₀
        (show 0 ≤ L + (42589 / 7000 : ℝ) * Real.log L + 77 / 25 by linarith only [hL, hlog, h8])
        (show 0 ≤ L + (1791 / 250 : ℝ) * Real.log L + 499 / 250 by
          linarith only [hL, hlog, h8])).mpr
  exact hroot

end PseudoPrime.Analysis

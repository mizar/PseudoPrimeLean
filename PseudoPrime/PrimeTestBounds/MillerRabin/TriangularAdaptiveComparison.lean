/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularAdaptiveEnvelope

/-! # Strict comparison for the adaptive triangular envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For `5 * 10 ^ 10 ≤ log n < 6 * 10 ^ 10`, the adaptive triangular cutoff is
strictly below the preceding mean-selected envelope. The earlier branches are bounded
below by `(2 / 5) * log n ^ 2`, while the new radius is at most `5 / 8).
This proves the adaptive candidate improves the actual envelope on the interval. -/
theorem triangularAdaptive_lt_mean {n : ℕ} (hL : (50000000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n < 60000000000) : triangularAdaptiveSelected n < meanSelected n := by
  have h30 : (30000000000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h40 : (40000000000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h45 : (45000000000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h70 : (70000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h80 : (80000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h100 : Real.log n < 100000000000 := by linarith only [hU]
  have hN := large_of_log63 h63
  have hs : 0 < Real.log n ^ 2 := sq_pos_of_pos (by linarith only [hL])
  have hB : (4145 / 10000 : ℝ) * Real.log n ^ 2 ≤ tunedFiniteSelected n := by
    rw [tunedFinite_eq_high_window h40 h100]
    nlinarith only [hs]
  have hc := highCoeff_lower_of_finite h70 h100 hB
  have hprev : (2 / 5 : ℝ) * Real.log n ^ 2 ≤ highWindowExtended n := by
    rw [highWindowExtended_eq_of_log_lt (by linarith only [hU]), highWindowSelected,
      ite_eq_right (not_lt.mpr hN),
      ite_eq_right (by linarith only [hU] : ¬(80000000000 : ℝ) ≤ Real.log n),
      ite_eq_right (not_le_of_gt hU), ite_eq_left h45]
    exact le_min (by nlinarith only [hc, hs]) le_rfl
  have hu := high_log_twice_ge_22 h70
  have hpair := pairedAlpha_ge_653 hu
  have hfac := (factorialAlpha_bounds hu).1
  have hpair2 : (2 / 5 : ℝ) ≤ (pairedAlpha (2 * Real.log (Real.log n))) ^ 2 := by
    nlinarith only [hpair, sq_nonneg (pairedAlpha (2 * Real.log (Real.log n)) - 653 / 1000)]
  have hfac2 : (2 / 5 : ℝ) ≤ (factorialAlpha (2 * Real.log (Real.log n))) ^ 2 := by
    nlinarith only [hfac, sq_nonneg (factorialAlpha (2 * Real.log (Real.log n)) - 647 / 1000)]
  have hp : (2 / 5 : ℝ) * Real.log n ^ 2 ≤ pairedSelected n := by
    rw [pairedSelected, ite_eq_left h70]
    exact le_min hprev (mul_le_mul_of_nonneg_right hpair2 hs.le)
  have hf : (2 / 5 : ℝ) * Real.log n ^ 2 ≤ factorialSelected n := by
    rw [factorialSelected, ite_eq_left h80]
    exact le_min hp (mul_le_mul_of_nonneg_right hfac2 hs.le)
  have hm : (2 / 5 : ℝ) * Real.log n ^ 2 ≤ meanSelected n := by
    rw [meanSelected, ite_eq_left h80]
    exact le_min hf (by nlinarith only [hs])
  have ha := triangularAdaptiveRadius_bounds h30
  have ha2 :=
    pow_le_pow_left₀ (show 0 ≤ triangularAdaptiveRadius (Real.log n) by linarith only [ha.1])
      (triangularAdaptiveRadius_le_5_8 hL) 2
  have had := mul_le_mul_of_nonneg_right ha2 hs.le
  have hnew :
    triangularAdaptiveSelected n ≤
      (triangularAdaptiveRadius (Real.log n)) ^ 2 * Real.log n ^ 2 := by
    rw [triangularAdaptiveSelected, ite_eq_left h30]
    exact min_le_right _ _
  nlinarith only [hnew, had, hm, hs]

end PseudoPrime.PrimeTestBounds.MillerRabin

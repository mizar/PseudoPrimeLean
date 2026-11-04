/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.HighVariableEnvelope
public import PseudoPrime.PrimeTestBounds.MillerRabin.HighWindowExtendedComparison
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSeededTunedAbsorption

/-! # Strict improvement of the variable paired envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For `22 ≤ U ≤ 24`, the paired radius coefficient is at most `33 / 50`. Clearing the positive
denominator gives a rational upper bound sufficient for a strict comparison with `7 / 16`. -/
theorem pairedAlpha_le_33_50 {U : ℝ} (hL : 22 ≤ U) (hU : U ≤ 24) : pairedAlpha U ≤ 33 / 50 := by
  have hd : 0 < (3 / 2 : ℝ) * U + 339 / 500 := by linarith only [hL]
  dsimp only [pairedAlpha]
  apply (div_le_iff₀ hd).mpr
  linarith only [hU]

/-- On `70000 ≤ log n ≤ 100000`, the variable paired envelope is strictly smaller than the full
previous extended envelope. The previous finite and Gaussian branches are bounded below by
`(7 / 16) * log n ^ 2`, while the new radius coefficient is at most `33 / 50`. -/
theorem pairedSelected_lt_previous {n : ℕ} (hL : (70000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 100000) : pairedSelected n < highWindowExtended n := by
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h240 : (240 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hN := large_of_log63 h63
  have hn : 1 < n := (by norm_num only : 1 < 3000).trans_le hN
  have h12 : (126409 / 10000 : ℝ) < Real.log n := by linarith only [hL]
  have h30 : Real.log n < 30000000000 := by linarith only [hU]
  have h40 : Real.log n < 40000000000 := by linarith only [hU]
  have hs : 0 < Real.log n ^ 2 := sq_pos_of_pos (by linarith only [hL])
  have hB : (7 / 16 : ℝ) * Real.log n ^ 2 ≤ tunedFiniteSelected n := by
    rw [← tunedFinite_eq_selected hn, tunedFinite_eq_sharp_of_log hn h12, sharp_eq_selected hn,
      sharpSelected_eq_seeded hN h240 h30]
    have hh := seededSharp_quadratic_lower h63
    nlinarith only [hh, hs]
  have hold := highCoeff_lower_7_16_of_finite hL h40 hB
  have hold' : (7 / 16 : ℝ) * Real.log n ^ 2 ≤ highWindowExtended n := by
    have h120 : Real.log n < 120000000000 := by linarith only [hU]
    rw [highWindowExtended_eq_of_log_lt h120, highWindowSelected, ite_eq_right (not_lt.mpr hN),
      ite_eq_right (by linarith only [hU] : ¬(80000000000 : ℝ) ≤ Real.log n),
      ite_eq_right (by linarith only [hU] : ¬(60000000000 : ℝ) ≤ Real.log n),
      ite_eq_right (by linarith only [hU] : ¬(45000000000 : ℝ) ≤ Real.log n),
      ite_eq_right (by linarith only [hU] : ¬(38000000000 : ℝ) ≤ Real.log n)]
    exact hold
  have hlog : Real.log (Real.log n) < 12 := by
    have hh :=
      Real.log_le_log (show (0 : ℝ) < Real.log n by linarith only [hL])
        (show Real.log n ≤ (2 : ℝ) ^ 17 by nlinarith only [hU])
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith only [hh, Real.log_two_lt_d9]
  have hα0 := pairedAlpha_ge_653 (high_log_twice_ge_22 hL)
  have hα := pairedAlpha_le_33_50 (high_log_twice_ge_22 hL) (by linarith only [hlog])
  have hαsq : (pairedAlpha (2 * Real.log (Real.log n))) ^ 2 ≤ (33 / 50 : ℝ) ^ 2 := by
    exact pow_le_pow_left₀ (by linarith only [hα0]) hα 2
  have hnew :
    pairedSelected n ≤ (pairedAlpha (2 * Real.log (Real.log n))) ^ 2 * Real.log n ^ 2 := by
    rw [pairedSelected, ite_eq_left hL]
    exact min_le_right _ _
  have hmul := mul_le_mul_of_nonneg_right hαsq hs.le
  nlinarith only [hnew, hold', hmul, hs]

end PseudoPrime.PrimeTestBounds.MillerRabin

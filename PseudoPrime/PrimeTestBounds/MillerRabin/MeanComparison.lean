/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.MeanEnvelope
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Strict improvement of the coefficient 427 / 1000 envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For `10 ^ 7 ≤ log n ≤ 2 * 10 ^ 7`, the coefficient `427 / 1000` makes the
mean-selected cutoff strictly smaller than the preceding factorial-selected cutoff.
Bound each previous branch from below and compare the variable coefficients at an
explicit logarithmic endpoint. This certifies a nonempty improvement interval. -/
theorem meanSelected_lt_factorial {n : ℕ} (hL : (10000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 20000000) : meanSelected n < factorialSelected n := by
  have h70 : (70000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h80 : (80000 : ℝ) ≤ Real.log n := by linarith only [hL]
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
  have hold := highCoeff_lower_7_16_of_finite h70 h40 hB
  have hold' : (7 / 16 : ℝ) * Real.log n ^ 2 ≤ highWindowExtended n := by
    have h120 : Real.log n < 120000000000 := by linarith only [hU]
    rw [highWindowExtended_eq_of_log_lt h120, highWindowSelected, ite_eq_right (not_lt.mpr hN),
      ite_eq_right (by linarith only [hU] : ¬(80000000000 : ℝ) ≤ Real.log n),
      ite_eq_right (by linarith only [hU] : ¬(60000000000 : ℝ) ≤ Real.log n),
      ite_eq_right (by linarith only [hU] : ¬(45000000000 : ℝ) ≤ Real.log n),
      ite_eq_right (by linarith only [hU] : ¬(38000000000 : ℝ) ≤ Real.log n)]
    exact hold
  have hlog16 : (16 : ℝ) ≤ Real.log (10000000 : ℝ) := by
    have hc :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 10000000 24 16 16 17 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat] at hc
    exact hc
  have hu : (32 : ℝ) ≤ 2 * Real.log (Real.log n) := by
    have hh := Real.log_le_log (by norm_num only : (0 : ℝ) < 10000000) hL
    linarith only [hlog16, hh]
  have ha32 : (817 / 1250 : ℝ) ≤ factorialAlpha 32 := by
    dsimp only [factorialAlpha]
    norm_num only
  have ha := ha32.trans (factorialAlpha_mono (by norm_num only : (22 : ℝ) ≤ 32) hu)
  have hpair := factorialAlpha_lt_paired (U := 2 * Real.log (Real.log n)) (by linarith only [hu])
  have haf : (427 / 1000 : ℝ) < (factorialAlpha (2 * Real.log (Real.log n))) ^ 2 := by
    nlinarith only [ha, sq_nonneg (factorialAlpha (2 * Real.log (Real.log n)) - 817 / 1250)]
  have hap : (427 / 1000 : ℝ) < (pairedAlpha (2 * Real.log (Real.log n))) ^ 2 := by
    have hh := (sq_lt_sq₀ (by linarith only [ha]) (by linarith only [ha, hpair])).mpr hpair
    linarith only [haf, hh]
  have hmulf := mul_lt_mul_of_pos_right haf hs
  have hmulp := mul_lt_mul_of_pos_right hap hs
  have hold'' : (427 / 1000 : ℝ) * Real.log n ^ 2 < highWindowExtended n := by
    nlinarith only [hold', hs]
  have hpair' : (427 / 1000 : ℝ) * Real.log n ^ 2 < pairedSelected n := by
    rw [pairedSelected, ite_eq_left h70]
    exact lt_min hold'' hmulp
  have hf : (427 / 1000 : ℝ) * Real.log n ^ 2 < factorialSelected n := by
    rw [factorialSelected, ite_eq_left h80]
    exact lt_min hpair' hmulf
  have hnew : meanSelected n ≤ (427 / 1000 : ℝ) * Real.log n ^ 2 := by
    rw [meanSelected, ite_eq_left h80]
    exact min_le_right _ _
  exact hnew.trans_lt hf

end PseudoPrime.PrimeTestBounds.MillerRabin

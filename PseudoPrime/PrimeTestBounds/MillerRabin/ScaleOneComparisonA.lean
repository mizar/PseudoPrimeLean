/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.ScaleOneEnvelopeA
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Strict improvement of the previous pointwise envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At scale 14000000 the previous continuous coefficient exceeds 0.3.
Rational logarithm certificates give a lower bound for the dual-scale radius. -/
theorem scaleOne_old_floorA : (3 / 10 : ℝ) < smoothCoeff 14000000 := by
  have hl4 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 4 2 32 1 2 = true from by decide +kernel)).1
  have hu :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 14000000 23 32 16 17 = true from by
          decide +kernel)).2
  norm_num only [Rat.cast_ofNat] at hl4 hu
  have hshift : (39 : ℝ) ≤ smoothDual_shift 14000000 := by
    unfold smoothDual_shift
    have hm := le_max_right (0 : ℝ) (36 + Real.log 4 - 2 * Real.log 14000000)
    linarith only [hm, hl4, hu]
  have hs : 0 ≤ (1456 + 13 / 10000000 : ℝ) / Real.sqrt 14000000 :=
    div_nonneg (by norm_num only) (Real.sqrt_nonneg _)
  have hr : (39 / 68 : ℝ) ≤ smoothDual_radius 14000000 := by
    unfold smoothDual_radius
    apply (le_div_iff₀ (by norm_num only)).2
    linarith only [hshift, hs]
  have hsquare := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 39 / 68) hr 2
  have hm : smoothDual_radius 14000000 ^ 2 ≤ smoothCoeff 14000000 := le_max_left _ _
  nlinarith only [hsquare, hm]

/-- On the stated interval, every branch of the preceding pointwise selection is
at least 0.3 times the squared scale. -/
theorem scaleOne_old_lowerA {n : ℕ} (hL : (10000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 14000000) : (3 / 10 : ℝ) * Real.log n ^ 2 ≤ smoothSelected n := by
  have h80 : (80000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h81 : (81000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h5 : (5000000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hG : ¬(200000000 : ℝ) ≤ Real.log n := by linarith only [hU]
  have hs : 0 ≤ Real.log n ^ 2 := sq_nonneg _
  have hm : (3 / 10 : ℝ) ≤ dualMeanSeriesCoeff (Real.log n) := by
    rw [dualMeanSeriesCoeff, ite_eq_left h81, dualSeriesCoeff]
    rw [ite_eq_right hG, ite_eq_right (by linarith only [hU]), ite_eq_right (by linarith only [hU]),
      ite_eq_right (by linarith only [hU]), ite_eq_right (by linarith only [hU]), ite_eq_left h5]
    norm_num only [min_eq_left (show (2 / 5 : ℝ) ≤ 4187 / 10000 by norm_num only)]
  have hc : (3 / 10 : ℝ) ≤ smoothCoeff (Real.log n) := by
    have ha := smoothCoeff_anti h5 hU
    linarith only [scaleOne_old_floorA, ha]
  have hseries : (3 / 10 : ℝ) ≤ smoothSeriesCoeff (Real.log n) := by
    rw [smoothSeriesCoeff, ite_eq_left h5, smoothCandidateCoeff, ite_eq_right hG]
    exact le_min hm hc
  rw [smoothSelected, ite_eq_left h80, dualSelected, ite_eq_left h80,
    reducedSelected_eq_mean_window hL (by linarith only [hU])]
  apply le_min
  · apply le_min
    · nlinarith only [hs]
    · exact mul_le_mul_of_nonneg_right hm hs
  · exact mul_le_mul_of_nonneg_right hseries hs

/-- The scale-one stage A selection strictly improves the entire preceding selection
on the stated interval; its certified Gaussian coefficient is less than 0.3. -/
theorem scaleOneSelectedA_lt_smooth {n : ℕ} (hL : (10000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 14000000) : scaleOneSelectedA n < smoothSelected n := by
  have h25 : (25000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hs : 0 < Real.log n ^ 2 := sq_pos_of_pos (by linarith only [hL])
  have ha := scaleOne_gaussian_slope (Real.log n) h25
  have hsq := pow_le_pow_left₀ (by linarith only [ha.1] : 0 ≤ adaptiveGaussianA (Real.log n)) ha.2 2
  have hc : (21 / 10 : ℝ) * adaptiveGaussianA (Real.log n) ^ 2 < 3 / 10 := by nlinarith only [hsq]
  have hlt := mul_lt_mul_of_pos_right hc hs
  rw [scaleOneSelectedA, ite_eq_left h25]
  exact (min_le_right _ _).trans_lt (hlt.trans_le (scaleOne_old_lowerA hL hU))

end PseudoPrime.PrimeTestBounds.MillerRabin

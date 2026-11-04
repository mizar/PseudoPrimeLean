/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianAdaptiveCumulative

/-! # Strict high-range comparison with the preceding envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Above two trillion, every sharp candidate is at least the final triangular coefficient. -/
theorem gaussianPrev_sharp_lower {n : ℕ} (hL : (2000000000000 : ℝ) ≤ Real.log n) :
    (1411811 / 5000000 : ℝ) * Real.log n ^ 2 ≤ sharpSelectedEnvelope n := by
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h12 : (12373 / 1000 : ℝ) < Real.log n := by linarith only [hL]
  have hN := large_of_log63 h63
  have hn : 1 < n := (by norm_num only : 1 < 3000).trans_le hN
  have hq : (1411811 / 5000000 : ℝ) * Real.log n ^ 2 ≤ (15 / 32 : ℝ) * Real.log n ^ 2 :=
    mul_le_mul_of_nonneg_right (by norm_num only) (sq_nonneg _)
  have hb : (1411811 / 5000000 : ℝ) * Real.log n ^ 2 ≤ lowFiniteWitness n := by
    rw [lowFinite_eq_selected hn, lowFiniteSelected_eq_refined hn h12]
    have h := refined_high_quadratic_lower hn hL
    nlinarith only [h, sq_nonneg (Real.log n)]
  rw [← sharp_eq_selected hn]
  apply sharp_lower_of_candidates hN hb
  · intro _
    exact hq.trans (gaussianLowFamily_quadratic_lower h63).le
  · intro _
    exact hq.trans (seededSharp_quadratic_lower h63).le
  · intro i hi
    fin_cases i <;>
      first
      | exact le_rfl
      |
        (norm_num only [triangularProfile, triangularP0466, triangularP042, triangularP0333,
           triangularP030, triangularP029, triangularP0284, triangularP02829, triangularP02823622];
         nlinarith only [sq_nonneg (Real.log n)])

/-- Above two trillion, the tuned triangular candidates retain the final coefficient
as a lower bound. -/
theorem gaussianPrev_tuned_lower {n : ℕ} (hL : (2000000000000 : ℝ) ≤ Real.log n) :
    (1411811 / 5000000 : ℝ) * Real.log n ^ 2 ≤
      tunedHighMin (Real.log n) (tunedFiniteSelected n) := by
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hN := large_of_log63 h63
  have hn : 1 < n := (by norm_num only : 1 < 3000).trans_le hN
  have h12 : (126409 / 10000 : ℝ) < Real.log n := by linarith only [hL]
  have hb : (1411811 / 5000000 : ℝ) * Real.log n ^ 2 ≤ tunedFiniteSelected n := by
    rw [← tunedFinite_eq_selected hn, tunedFinite_eq_sharp_of_log hn h12, sharp_eq_selected hn]
    exact gaussianPrev_sharp_lower hL
  apply tunedHigh_lower hb
  intro i hi
  fin_cases i <;>
    first
    | ( change (1411811 / 5000000 : ℝ) * Real.log n ^ 2 ≤ (28289 / 100000 : ℝ) * Real.log n ^ 2
        nlinarith only [sq_nonneg (Real.log n)])
    |
      (norm_num only [triangularTunedProfile, triangularP04603, triangularP04145, triangularP03315,
         triangularP02992, triangularP02891, triangularP028399, triangularP028289];
       nlinarith only [sq_nonneg (Real.log n)])

/-- The earlier mean-selected envelope is at least the final triangular coefficient
on the high range. -/
theorem gaussianPrev_mean_lower {n : ℕ} (hL : (2000000000000 : ℝ) ≤ Real.log n) :
    (1411811 / 5000000 : ℝ) * Real.log n ^ 2 ≤ meanSelected n := by
  have h70 : (70000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h80 : (80000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h600 : (600000000000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hwin :=
    highWindow_lower_of_tuned (show (80000000000 : ℝ) ≤ Real.log n by linarith only [hL])
      (show (1411811 / 5000000 : ℝ) ≤ 173 / 500 by norm_num only) (gaussianPrev_tuned_lower hL)
  have hprev : (1411811 / 5000000 : ℝ) * Real.log n ^ 2 ≤ highWindowExtended n := by
    rw [highWindowExtended, ite_eq_left h600]
    exact le_min hwin (by nlinarith only [sq_nonneg (Real.log n)])
  have hu := high_log_twice_ge_22 h70
  have ha := pairedAlpha_ge_653 hu
  have hf := (factorialAlpha_bounds hu).1
  have hp : (1411811 / 5000000 : ℝ) * Real.log n ^ 2 ≤ pairedWitnessBound n := by
    dsimp only [pairedWitnessBound]
    have hsq := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 653 / 1000) ha 2
    nlinarith only [mul_le_mul_of_nonneg_right hsq (sq_nonneg (Real.log n))]
  have hfac : (1411811 / 5000000 : ℝ) * Real.log n ^ 2 ≤ factorialWitnessBound n := by
    dsimp only [factorialWitnessBound]
    have hsq := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 647 / 1000) hf 2
    nlinarith only [mul_le_mul_of_nonneg_right hsq (sq_nonneg (Real.log n))]
  rw [meanSelected, ite_eq_left h80, factorialSelected, ite_eq_left h80, pairedSelected,
    ite_eq_left h70]
  exact le_min (le_min (le_min hprev hp) hfac) (by nlinarith only [sq_nonneg (Real.log n)])

/-- The adaptive triangular envelope is at least its sharper three-factor floor
on the high range. -/
theorem gaussianPrev_triangular_lower {n : ℕ} (hL : (2000000000000 : ℝ) ≤ Real.log n) :
    (1411811 / 5000000 : ℝ) * Real.log n ^ 2 ≤ triangularAdaptiveSelected n := by
  have h30 : (30000000000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h182 : (1820000000000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hfloor : triangularAdaptiveFloor (Real.log n) = 1411811 / 5000000 := by
    rw [triangularAdaptiveFloor, ite_eq_left h182]
  have hs :
    Real.sqrt (triangularAdaptiveFloor (Real.log n)) ≤ triangularAdaptiveRadius (Real.log n) :=
    le_max_left _ _
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
  rw [Real.sq_sqrt
      (by
        rw [hfloor]; norm_num only),
    hfloor] at hsq
  rw [triangularAdaptiveSelected, ite_eq_left h30]
  exact le_min (gaussianPrev_mean_lower hL) (mul_le_mul_of_nonneg_right hsq (sq_nonneg _))

/-- At every logarithmic scale at least two trillion, the Gaussian-selected cutoff is strictly
below the preceding complete triangular envelope. Compare the certified Gaussian coefficient
with the common lower bound for every earlier candidate. -/
theorem gaussianAdaptive_lt_triangular {n : ℕ} (hL : (2000000000000 : ℝ) ≤ Real.log n) :
    gaussianAdaptiveSelected n < triangularAdaptiveSelected n := by
  have hs : 0 < Real.log n ^ 2 := sq_pos_of_pos (by linarith only [hL])
  have hc := adaptiveGaussian_coefficient_lt (Real.log n) hL
  have hb := mul_lt_mul_of_pos_right hc hs
  have he :
    gaussianAdaptiveSelected n ≤
      ((21 / 10 : ℝ) * adaptiveGaussianA (Real.log n) ^ 2) * Real.log n ^ 2 := by
    rw [gaussianAdaptiveSelected, ite_eq_left hL]
    exact min_le_right _ _
  exact he.trans_lt (hb.trans_le (gaussianPrev_triangular_lower hL))

end PseudoPrime.PrimeTestBounds.MillerRabin

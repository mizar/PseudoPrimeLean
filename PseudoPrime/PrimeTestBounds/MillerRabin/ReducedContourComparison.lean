/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.ReducedContourEnvelope

/-! # Strict comparisons for the reduced-contour selection -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Before the triangular entrance all later guards are inactive, leaving the mean selection. -/
theorem fixedImproved_eq_mean_before_triangular {n : ℕ} (hL : Real.log n < 30000000000) :
    fixedImprovedSelected n = meanSelected n := by
  have hG : Real.log n < 2000000000000 := by linarith only [hL]
  have htri : triangularAdaptiveSelected n = meanSelected n := by
    rw [triangularAdaptiveSelected, ite_eq_right (not_le_of_gt hL)]
  have hg : gaussianAdaptiveSelected n = meanSelected n := by
    rw [gaussianAdaptiveSelected_eq hG, htri]
  have hp (f : TriangularProfile) : fixedProfileSelected f n = gaussianAdaptiveSelected n := by
    rw [fixedProfileSelected, ite_eq_right (by linarith only [hL, f.entry])]
  rw [fixedImprovedSelected, hp, hp, hp, min_self, min_self, hg]

/-- The reduced series strictly improves the preceding full selection on the mean window.
The earlier comparison identifies the old mean branch, and the new coefficient is smaller. -/
theorem reducedSelected_lt_mean_window {n : ℕ} (hL : (10000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 20000000) : reducedSelected n < fixedImprovedSelected n := by
  have h80 : (80000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hs : 0 < Real.log n ^ 2 := sq_pos_of_pos (by linarith only [hL])
  have hm := meanSelected_lt_factorial hL hU
  rw [meanSelected, ite_eq_left h80] at hm
  have hf : (427 / 1000 : ℝ) * Real.log n ^ 2 < factorialSelected n := by
    exact (min_lt_iff.mp hm).resolve_left (lt_irrefl _)
  have he : meanSelected n = (427 / 1000 : ℝ) * Real.log n ^ 2 := by
    rw [meanSelected, ite_eq_left h80, min_eq_right hf.le]
  have hold : fixedImprovedSelected n = (427 / 1000 : ℝ) * Real.log n ^ 2 := by
    rw [fixedImproved_eq_mean_before_triangular (by linarith only [hU]), he]
  have hr : reducedSeriesCoeff (Real.log n) = 1057 / 2500 := by
    unfold reducedSeriesCoeff
    rw [ite_eq_right (by linarith only [hU]), ite_eq_right (by linarith only [hU]),
      ite_eq_right (by linarith only [hU]), ite_eq_right (by linarith only [hU]),
      ite_eq_right (by linarith only [hU])]
  rw [reducedSelected, ite_eq_left h80]
  apply (min_le_right _ _).trans_lt
  rw [hr, hold]
  nlinarith only [hs]

/-- Before the triangular entrance, the earlier selection is at least two fifths of the
squared scale. The existing finite, high-window, and variable-branch lower bounds suffice. -/
theorem fixedImproved_lower_before_triangular {n : ℕ} (hL : (200000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n < 30000000000) : (2 / 5 : ℝ) * Real.log n ^ 2 ≤ fixedImprovedSelected n := by
  have h70 : (70000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h80 : (80000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h240 : (240 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hN := large_of_log63 h63
  have hn : 1 < n := (by norm_num only : 1 < 3000).trans_le hN
  have h12 : (126409 / 10000 : ℝ) < Real.log n := by linarith only [hL]
  have h40 : Real.log n < 40000000000 := by linarith only [hU]
  have hs : 0 < Real.log n ^ 2 := sq_pos_of_pos (by linarith only [hL])
  have hB : (7 / 16 : ℝ) * Real.log n ^ 2 ≤ tunedFiniteSelected n := by
    rw [← tunedFinite_eq_selected hn, tunedFinite_eq_sharp_of_log hn h12, sharp_eq_selected hn,
      sharpSelected_eq_seeded hN h240 hU]
    have hh := seededSharp_quadratic_lower h63
    nlinarith only [hh, hs]
  have hold := highCoeff_lower_7_16_of_finite h70 h40 hB
  have hold' : (2 / 5 : ℝ) * Real.log n ^ 2 ≤ highWindowExtended n := by
    have h120 : Real.log n < 120000000000 := by linarith only [hU]
    rw [highWindowExtended_eq_of_log_lt h120, highWindowSelected, ite_eq_right (not_lt.mpr hN),
      ite_eq_right (by linarith only [hU] : ¬(80000000000 : ℝ) ≤ Real.log n),
      ite_eq_right (by linarith only [hU] : ¬(60000000000 : ℝ) ≤ Real.log n),
      ite_eq_right (by linarith only [hU] : ¬(45000000000 : ℝ) ≤ Real.log n),
      ite_eq_right (by linarith only [hU] : ¬(38000000000 : ℝ) ≤ Real.log n)]
    nlinarith only [hold, hs]
  rw [fixedImproved_eq_mean_before_triangular hU]
  exact fixedMean_lower h80 (by norm_num only) hold'

/-- Every fixed reduced-contour branch strictly improves the preceding full selection
between the first fixed entrance and the early Gaussian entrance. -/
theorem reducedSelected_lt_fixed_window {n : ℕ} (hL : (200000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n < 30000000000) : reducedSelected n < fixedImprovedSelected n := by
  have hm := fixedImproved_lower_before_triangular hL hU
  have hs : 0 < Real.log n ^ 2 := sq_pos_of_pos (by linarith only [hL])
  have hc : reducedSeriesCoeff (Real.log n) ≤ 39 / 100 := by
    have hh := reducedSeries_antitone hL
    norm_num only [reducedSeriesCoeff, show ¬(30000000000 : ℝ) ≤ 200000000 by norm_num,
      show ¬(5000000000 : ℝ) ≤ 200000000 by norm_num,
      show ¬(1000000000 : ℝ) ≤ 200000000 by norm_num, show ¬(500000000 : ℝ) ≤ 200000000 by norm_num,
      show (200000000 : ℝ) ≤ 200000000 by norm_num, ite_true, ite_false] at hh
    exact hh
  have h80 : (80000 : ℝ) ≤ Real.log n := by linarith only [hL]
  rw [reducedSelected, ite_eq_left h80]
  apply (min_le_right _ _).trans_lt
  have hh := mul_le_mul_of_nonneg_right hc (le_of_lt hs)
  nlinarith only [hh, hm, hs]

/-- On the early Gaussian window, every preceding candidate is at least the original
triangular three-factor floor. Compare the mean and triangular branches separately. -/
theorem fixedImproved_lower_earlyGaussian {n : ℕ} (hL : (30000000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n < 38000000000) :
    (28237 / 100000 : ℝ) * Real.log n ^ 2 ≤ fixedImprovedSelected n := by
  have h70 : (70000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h80 : (80000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hN := large_of_log63 h63
  have hs : 0 < Real.log n ^ 2 := sq_pos_of_pos (by linarith only [hL])
  have h40 : Real.log n < 40000000000 := by linarith only [hU]
  have hB : (7 / 16 : ℝ) * Real.log n ^ 2 ≤ tunedFiniteSelected n := by
    rw [tunedFinite_eq_early_window hL h40]
    nlinarith only [hs]
  have hold := highCoeff_lower_7_16_of_finite h70 h40 hB
  have hprev : (2 / 5 : ℝ) * Real.log n ^ 2 ≤ highWindowExtended n := by
    have h120 : Real.log n < 120000000000 := by linarith only [hU]
    rw [highWindowExtended_eq_of_log_lt h120, highWindowSelected, ite_eq_right (not_lt.mpr hN),
      ite_eq_right (by linarith only [hU] : ¬(80000000000 : ℝ) ≤ Real.log n),
      ite_eq_right (by linarith only [hU] : ¬(60000000000 : ℝ) ≤ Real.log n),
      ite_eq_right (by linarith only [hU] : ¬(45000000000 : ℝ) ≤ Real.log n),
      ite_eq_right (not_le_of_gt hU)]
    nlinarith only [hold, hs]
  have hm := fixedMean_lower h80 (by norm_num only : (2 / 5 : ℝ) ≤ 2 / 5) hprev
  have hfloor : triangularAdaptiveFloor (Real.log n) = 28237 / 100000 := by
    rw [triangularAdaptiveFloor, ite_eq_right (by linarith only [hU])]
  have hroot :
    Real.sqrt (triangularAdaptiveFloor (Real.log n)) ≤ triangularAdaptiveRadius (Real.log n) :=
    le_max_left _ _
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hroot 2
  rw [Real.sq_sqrt
      (by
        rw [hfloor]; norm_num only),
    hfloor] at hsq
  have htri : (28237 / 100000 : ℝ) * Real.log n ^ 2 ≤ triangularAdaptiveSelected n := by
    rw [triangularAdaptiveSelected, ite_eq_left hL]
    exact le_min (by nlinarith only [hm, hs]) (mul_le_mul_of_nonneg_right hsq (sq_nonneg _))
  have hg : gaussianAdaptiveSelected n = triangularAdaptiveSelected n :=
    gaussianAdaptiveSelected_eq (by linarith only [hU])
  have hp (f : TriangularProfile) (hf : (50000000000 : ℝ) ≤ f.T) :
    fixedProfileSelected f n = gaussianAdaptiveSelected n := by
    rw [fixedProfileSelected, ite_eq_right (by linarith only [hU, hf])]
  have hp1 := hp improvedProfile03869 (by norm_num only [improvedProfile03869])
  have hp2 := hp improvedProfile03552 (by norm_num only [improvedProfile03552])
  have hp3 := hp improvedProfile03134 (by norm_num only [improvedProfile03134])
  rw [fixedImprovedSelected, hp1, hp2, hp3, min_self, min_self, hg]
  exact htri

/-- The early Gaussian candidate strictly improves the entire preceding selection
between its entrance and the first high-window entrance. -/
theorem reducedSelected_lt_earlyGaussian {n : ℕ} (hL : (30000000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n < 38000000000) : reducedSelected n < fixedImprovedSelected n := by
  have hold := fixedImproved_lower_earlyGaussian hL hU
  have hs : 0 < Real.log n ^ 2 := sq_pos_of_pos (by linarith only [hL])
  have hc := earlyGaussian_coeff_upper (Real.log n) hL
  have h80 : (80000 : ℝ) ≤ Real.log n := by linarith only [hL]
  rw [reducedSelected, ite_eq_left h80]
  apply (min_le_right _ _).trans_lt
  rw [reducedSeriesCoeff, ite_eq_left hL]
  have hh := mul_lt_mul_of_pos_right hc hs
  exact hh.trans_le hold

end PseudoPrime.PrimeTestBounds.MillerRabin

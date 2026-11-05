/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.JointSurplusCumulative
public import PseudoPrime.PrimeTestBounds.MillerRabin.ScaleOneComparisonA

/-! # Strict comparisons for the global surplus envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- On the stated interval, the joint selection strictly improves the entire preceding
public minimum. Its earlier adaptive Gaussian branch is identified explicitly. -/
theorem jointSelected_lt_scaleOneA {n : ℕ} (hL : (10000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 14000000) : jointSelected n < scaleOneSelectedA n := by
  have h25 : (25000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hn : 3000 ≤ n := large_of_log63 h63
  have hs : 0 < Real.log n ^ 2 := sq_pos_of_pos (by linarith only [hL])
  have ha := scaleOne_gaussian_slope (Real.log n) h25
  have hsq := pow_le_pow_left₀ (by linarith only [ha.1] : 0 ≤ adaptiveGaussianA (Real.log n)) ha.2 2
  have hc : (21 / 10 : ℝ) * adaptiveGaussianA (Real.log n) ^ 2 < 3 / 10 := by nlinarith only [hsq]
  have hold :
    ((21 / 10 : ℝ) * adaptiveGaussianA (Real.log n) ^ 2) * Real.log n ^ 2 < smoothSelected n :=
    (mul_lt_mul_of_pos_right hc hs).trans_le (scaleOne_old_lowerA hL hU)
  have heq :
    scaleOneSelectedA n =
      ((21 / 10 : ℝ) * adaptiveGaussianA (Real.log n) ^ 2) * Real.log n ^ 2 := by
    rw [scaleOneSelectedA, ite_eq_left h25, min_eq_right hold.le]
  have hnew : jointSurplusGlobal (Real.log n) ≤ jointSurplusCutoff 155 29 (Real.log n) :=
    (min_le_right _ _).trans (min_le_right _ _)
  rw [jointSelected, ite_eq_right (not_lt.mpr hn), heq]
  exact (min_le_right _ _).trans_lt (hnew.trans_lt (jointSurplus_lt_adaptive h25))

/-- From 3000 onward the joint selection equals the preceding smooth selection intersected with
    the global surplus bound. The older scale-one candidate is strictly dominated when enabled. -/
theorem jointSelected_eq_smooth_min (n : ℕ) (hn : 3000 ≤ n) :
    jointSelected n = min (smoothSelected n) (jointSurplusGlobal (Real.log n)) := by
  rw [jointSelected, ite_eq_right (not_lt.mpr hn)]

/-- The global surplus bound also absorbs the scale-one history cap, so the joint cumulative
    envelope is the minimum of the earlier smooth cumulative envelope and the global bound. -/
theorem jointCumulative_eq_smooth_min (N : ℕ) :
    jointCumulative N = min (smoothCumulative N) (jointSurplusGlobal (Real.log N)) := by rfl

/-- The earlier scale-one cumulative cap is absorbed by the global bound. -/
theorem jointCumulative_eq_scaleOne_min (N : ℕ) :
    jointCumulative N = min (scaleOneCumulativeA N) (jointSurplusGlobal (Real.log N)) := by
  have hcap : jointSurplusGlobal (Real.log N) ≤ scaleOneCapA (Real.log N) := by
    by_cases h : (25000 : ℝ) ≤ Real.log N
    · have hc : jointSurplusGlobal (Real.log N) ≤ jointSurplusCutoff 155 29 (Real.log N) :=
        (min_le_right _ _).trans (min_le_right _ _)
      have ha := hc.trans (jointSurplus_lt_adaptive h).le
      unfold scaleOneCapA
      apply ha.trans
      apply le_max_of_le_right
      nlinarith only [ha]
    · have hn := Real.log_natCast_nonneg N
      have hs : Real.log N ^ 2 ≤ (25000 : ℝ) ^ 2 := by nlinarith only [hn, h]
      have hb : jointSurplusGlobal (Real.log N) ≤ (4 / 9 : ℝ) * Real.log N ^ 2 := min_le_left _ _
      unfold scaleOneCapA
      have hh : (4 / 9 : ℝ) * Real.log N ^ 2 ≤ (4 / 9 : ℝ) * (25000 : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hs (by norm_num only)
      exact (hb.trans hh).trans (le_max_left _ _)
  rw [jointCumulative, scaleOneCumulativeA, min_assoc, min_eq_right hcap]

end PseudoPrime.PrimeTestBounds.MillerRabin

/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.ImprovedWitnessEnvelope

/-! # Continuous strict gains of the guarded MR envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For n>1 and 11.44<log n<120, the improved envelope is strictly smaller
than the compatible envelope. Compare C4 with the shifted or two-step branch continuously. -/
theorem improved_strict_low {n : ℕ} (hn : 1 < n) (hL : 286 / 25 < Real.log n)
    (hU : Real.log n < 120) : improvedWitnessEnvelope n < selectedWitnessEnvelope n := by
  have hN := midscale_large_of_log (Nat.zero_lt_of_lt hn) (by linarith only [hL])
  have h3 : ¬n < 3000 := not_lt.mpr hN
  have h2 : ¬n < 2047 := not_lt.mpr ((by norm_num only : 2047 ≤ 3000).trans hN)
  have hbase : (45 / 4 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hb := improved_le_fourStep hbase
  simp only [selectedWitnessEnvelope, ite_eq_right h2, ite_eq_right h3,
    ite_eq_right (not_le.mpr hL)]
  by_cases h : Real.log n < 23 / 2
  · rw [ite_eq_left h]
    exact
      hb.trans_lt
        ((LLS.PaperStatements.endpoint_fourStep_le_two hbase).trans_lt
          (LLS.PaperStatements.endpoint_twoStep_lt_shifted hbase (by linarith only [h])))
  · rw [ite_eq_right h, ite_eq_left hU]
    exact
      hb.trans_lt
        (LLS.PaperStatements.endpoint_fourStep_lt_two
          (by linarith only [le_of_not_gt h] : (1147 / 100 : ℝ) ≤ Real.log n) hU.le)

/-- For n>1 and 120<=log n<S1, the improved envelope is strictly smaller
than the compatible envelope. G1 improves its Gamma branch and stays below the fixed
35000 branch. -/
theorem improved_strict_gamma {n : ℕ} (hn : 1 < n) (hL : 120 ≤ Real.log n)
    (hS : Real.log n < gammaSharpFixedSwitch) :
    improvedWitnessEnvelope n < selectedWitnessEnvelope n := by
  have hN := midscale_large_of_log (Nat.zero_lt_of_lt hn) (by linarith only [hL])
  have h3 : ¬n < 3000 := not_lt.mpr hN
  have h2 : ¬n < 2047 := not_lt.mpr ((by norm_num only : 2047 ≤ 3000).trans hN)
  have h61 : ¬Real.log n ≤ 286 / 25 := by linarith only [hL]
  have h11 : ¬Real.log n < 23 / 2 := by linarith only [hL]
  have h240 : Real.log n ≤ 240 := by linarith only [hS, gammaSharpFixedSwitch_bounds.2]
  have hb := improved_le_sharp (by linarith only [hL] : (100 : ℝ) ≤ Real.log n)
  simp only [selectedWitnessEnvelope, ite_eq_right h2, ite_eq_right h3, ite_eq_right h61,
    ite_eq_right h11, ite_eq_right (not_lt.mpr hL)]
  by_cases h : Real.log n ≤ gammaFixedSwitch
  · rw [ite_eq_left h]
    exact hb.trans_lt (gammaSharp_lt_refined hL h240)
  · rw [ite_eq_right h, ite_eq_left h240]
    exact hb.trans_lt (gammaSharp_lt_fixed (by linarith only [hL]) hS)

/-- For n>1, log n>240 and n below the original decimal threshold, the selected
clipped Gaussian bound is strictly below the compatible envelope. Compare both Gaussian regimes. -/
theorem gaussianSelected_lt_old {n : ℕ} (hn : 1 < n) (hL : 240 < Real.log n)
    (hNold : n < 10 ^ 9565217391305) :
    Analysis.gaussianFloorSelected (Real.log n) < selectedWitnessEnvelope n := by
  have hN := midscale_large_of_log (Nat.zero_lt_of_lt hn) (by linarith only [hL])
  have h3 : ¬n < 3000 := not_lt.mpr hN
  have h2 : ¬n < 2047 := not_lt.mpr ((by norm_num only : 2047 ≤ 3000).trans hN)
  have h61 : ¬Real.log n ≤ 286 / 25 := by linarith only [hL]
  have h11 : ¬Real.log n < 23 / 2 := by linarith only [hL]
  have h120 : ¬Real.log n < 120 := by linarith only [hL]
  have hS : ¬Real.log n ≤ gammaFixedSwitch := by linarith only [hL, gammaFixedSwitch_bounds.2]
  simp only [selectedWitnessEnvelope, ite_eq_right h2, ite_eq_right h3, ite_eq_right h61,
    ite_eq_right h11, ite_eq_right h120, ite_eq_right hS, ite_eq_right (not_le.mpr hL),
    gaussianMRWitnessEnvelope, ite_eq_right (not_le.mpr hNold)]
  by_cases h300 : 300 ≤ Real.log n
  · rw [ite_eq_left h300, gaussianMRRefinedEnvelope_eq h300]
    have hs := Analysis.gaussianFloor50_lt_refined h300
    have hmin :
      Analysis.gaussianFloorSelected (Real.log n) ≤
        Analysis.gaussianFloorBound true (Real.log n) := by
      rw [← Analysis.gaussianFloor_min_eq_selected (by linarith only [hL])]
      exact min_le_right _ _
    exact hmin.trans_lt hs
  · rw [ite_eq_right h300, gaussianMRPrefixEnvelope_eq hL.le]
    exact Analysis.floorSelected_lt_six hL.le

/-- For n>1, log n>240 and n below the original decimal threshold, the improved
envelope is strictly smaller. Project the clipped Gaussian candidate and its continuous
strict gain. -/
theorem improved_strict_gaussian {n : ℕ} (hn : 1 < n) (hL : 240 < Real.log n)
    (hNold : n < 10 ^ 9565217391305) : improvedWitnessEnvelope n < selectedWitnessEnvelope n := by
  exact
    (improved_le_gaussian (by linarith only [hL] : (63 : ℝ) ≤ Real.log n)).trans_lt
      (gaussianSelected_lt_old hn hL hNold)

end PseudoPrime.PrimeTestBounds.MillerRabin

/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaCheckpoint1000Refined

/-! # Sharper Gamma credit from the existing ten-node prefix -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The logarithm at 100 is at least 921/200. Kernel-check the existing Taylor evaluator.
This retains the negative logarithm correction in the seed boundary estimate. -/
theorem sharp_log100 : (921 / 200 : ℝ) ≤ Real.log 100 := by
  have hc : Analysis.rationalLogIntervalCheck 100 7 20 (921 / 200) (2303 / 500) = true := by
    decide +kernel
  simpa only [Rat.cast_ofNat, Rat.cast_div] using (Analysis.rationalLogIntervalCheck_sound hc).1

/-- The logarithm at 900 is at least 3401/500. Kernel-check the existing Taylor evaluator.
The analytic difference endpoint is not an Euler-prefix quadrature node. -/
theorem sharp_log900 : (3401 / 500 : ℝ) ≤ Real.log 900 := by
  have hc : Analysis.rationalLogIntervalCheck 900 10 16 (3401 / 500) (6803 / 1000) = true := by
    decide +kernel
  simpa only [Rat.cast_ofNat, Rat.cast_div] using (Analysis.rationalLogIntervalCheck_sound hc).1

/-- The logarithm of 10/9 is at most 105361/1000000.
Kernel-check the eight-term Taylor interval for the one-sided psi difference bound. -/
theorem sharp_log_ratio : Real.log (10 / 9 : ℝ) ≤ 105361 / 1000000 := by
  have hc :
    Analysis.rationalLogIntervalCheck (10 / 9) 0 8 (2634 / 25000) (105361 / 1000000) = true := by
    decide +kernel
  simpa only [Rat.cast_ofNat, Rat.cast_div] using (Analysis.rationalLogIntervalCheck_sound hc).2

/-- Under RH, the smoothed Mangoldt sum at 100 is at most 9151/100.
Retain the corrected logarithmic upper bound and the rational log anchor. -/
theorem sharp_smoothed100 (hRH : RiemannHypothesis) :
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 100 ≤ (9151 / 100 : ℝ) := by
  have h := logWeightedMangoldtSum_le_rational_corrected hRH (by norm_num only : (1 : ℝ) < 100)
  have hs : Real.sqrt (100 : ℝ) ≤ 10 := Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  linarith only [h, hs, sharp_log100]

/-- Under RH, the smoothed Mangoldt sum at 900 is at most 88847/100.
Retain the corrected logarithmic upper bound and the rational log anchor. -/
theorem sharp_smoothed900 (hRH : RiemannHypothesis) :
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 900 ≤ (88847 / 100 : ℝ) := by
  have h := logWeightedMangoldtSum_le_rational_corrected hRH (by norm_num only : (1 : ℝ) < 900)
  have hs : Real.sqrt (900 : ℝ) ≤ 30 := Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  linarith only [h, hs, sharp_log900]

/-- Under RH, psi(1000)>=906. Apply the one-sided difference between 900 and 1000
using a negative error cap at 900 and the certified logarithm ratio.
No input or prime-power enumeration is introduced. -/
theorem sharp_psi1000 (hRH : RiemannHypothesis) : (906 : ℝ) ≤ Chebyshev.psi 1000 := by
  apply
    psi_lower_of_one_sided_log_cap (x := 900) (U := -1153 / 100) (V := 16) (R := 105361 / 1000000)
      (by norm_num only) (by norm_num only)
  · linarith only [sharp_smoothed900 hRH]
  · linarith only [checkpoint1000_smoothed_lower hRH]
  · norm_num only
  · convert sharp_log_ratio using 1
    norm_num only
  · norm_num only

/-- Under RH, the signed seed boundary at 100 is at least 1156/125.
Keep both negative products and substitute the sharpened smoothed-sum bound. -/
theorem sharp_seed_boundary (hRH : RiemannHypothesis) :
    (1156 / 125 : ℝ) ≤ gammaEulerBoundaryTail 100 := by
  have h :=
    gamma_euler_boundary_tail_lower gamma_seed100_weight_upper (by norm_num only)
      gamma_seed100_psi_upper gamma_seed100_slope_lower (by norm_num only)
      (gamma_logWeightedMangoldtSum_nonneg (by norm_num only : (0 : ℝ) < 100))
      (sharp_smoothed100 hRH) gamma_seed100_main_lower
  linarith only [h]

/-- Under RH, the signed boundary at 1000 is at most 1013/125.
Use the new psi lower bound and the existing ten-node weight, slope and main coefficients. -/
theorem sharp_target_boundary (hRH : RiemannHypothesis) :
    gammaEulerBoundaryTail 1000 ≤ (1013 / 125 : ℝ) := by
  have h :=
    gamma_euler_boundary_tail_upper (by norm_num only : (0 : ℝ) ≤ 435675 / 1000000000)
      checkpoint1000_weight_lower (by norm_num only : (0 : ℝ) ≤ 906) (sharp_psi1000 hRH)
      checkpoint1000_slope_upper (by norm_num only) (by norm_num only : (0 : ℝ) ≤ 984)
      (checkpoint1000_smoothed_lower hRH) checkpoint1000_main_upper
  linarith only [h]

/-- Under RH, every Gamma prefix with cutoff b>=1000 is at least 423/100.
Transport the existing seed through sharper signed boundaries and unchanged error caps,
then use prefix monotonicity. No new node data or finite input enumeration is used. -/
theorem gamma_prefix1000_sharp (hRH : RiemannHypothesis) {b : ℝ} (hb : 1000 ≤ b) :
    (423 / 100 : ℝ) ≤ ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  have h :=
    gamma_euler_prefix_lower_from_seed100 (b := 1000) (E := 21 / 250) hRH (by norm_num only)
      (sharp_seed_boundary hRH) (sharp_target_boundary hRH)
      (by linarith only [gammaEulerTailErrorBudget_le_seed100, checkpoint1000_error_upper])
  have hc :
    (423 / 100 : ℝ) ≤
      ∑ m ∈ Finset.Ioc 0 ⌊(1000 : ℝ)⌋₊, Analysis.gammaResolventMangoldtWeight m := by
    linarith only [h]
  have hm :=
    Analysis.gamma_euler_prefix_lower_mono (c := 423 / 100) (Nat.floor_mono hb)
      (by
        norm_num only [Rat.cast_div, Rat.cast_ofNat]
        simpa only [Nat.floor_ofNat] using hc)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hm
  exact hm

end PseudoPrime.LLS

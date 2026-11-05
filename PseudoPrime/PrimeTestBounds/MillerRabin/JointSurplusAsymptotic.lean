/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.JointSurplusDominance

/-! # Asymptotic coefficient of the joint Gaussian surplus bound -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The older adaptive Gaussian slope tends to its main coefficient as the logarithmic
    scale tends to infinity. Both reciprocal correction terms vanish. -/
theorem adaptiveGaussianA_tendsto :
    Filter.Tendsto adaptiveGaussianA Filter.atTop
      (nhds ((20115621 / 25000000 : ℝ) / (10971611 / 5000000))) := by
  have hs : Filter.Tendsto (fun x : ℝ ↦ (Real.sqrt x)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  have hi : Filter.Tendsto (fun x : ℝ ↦ x⁻¹) Filter.atTop (nhds 0) := tendsto_inv_atTop_zero
  have hc :
    Filter.Tendsto (fun _ : ℝ ↦ (20115621 / 25000000 : ℝ)) Filter.atTop
      (nhds (20115621 / 25000000 : ℝ)) :=
    tendsto_const_nhds
  have h :=
    ((hc.add (hs.const_mul ((61 / 100 : ℝ) * (28794111 / 12500000)))).add
          (hi.const_mul (39 : ℝ))).div_const
      (10971611 / 5000000 : ℝ)
  convert h using 1 <;> norm_num only [mul_zero, add_zero, zero_div]
  funext x
  dsimp only [adaptiveGaussianA]
  ring

/-- Every clipped Gaussian surplus cutoff is bounded below by its leading quadratic term.
    The positive residual and square-root term are retained in the root budget inequality. -/
theorem jointSurplusCutoff_asymptotic_lower {L rho R : ℝ} (hL : 0 ≤ L) (hrho : 0 ≤ rho)
    (hR : 0 < R) :
    ((21 / 10 : ℝ) * ((20115621 / 25000000) / (10971611 / 5000000)) ^ 2) * L ^ 2 ≤
      jointSurplusCutoff rho R L := by
  have hb := jointSurplus_budget hrho hR hL
  have hs := Real.sqrt_nonneg (jointSurplusRadius rho R L)
  have hl : 0 ≤ ((20115621 / 25000000 : ℝ) / (10971611 / 5000000)) * L :=
    mul_nonneg (by norm_num only) hL
  have hr :
    ((20115621 / 25000000 : ℝ) / (10971611 / 5000000)) * L ≤ jointSurplusRadius rho R L := by
    nlinarith only [hb, hs, hR]
  have hp := pow_le_pow_left₀ hl hr 2
  unfold jointSurplusCutoff
  nlinarith only [hp]

/-- The normalized global surplus bound tends to the Gaussian main coefficient.
    Its root budget supplies the lower bound, and the earlier adaptive Gaussian cutoff
    supplies an upper bound with the same limit. -/
theorem jointSurplusGlobal_ratio_tendsto :
    Filter.Tendsto (fun L : ℝ ↦ jointSurplusGlobal L / L ^ 2) Filter.atTop
      (nhds ((21 / 10 : ℝ) * ((20115621 / 25000000) / (10971611 / 5000000)) ^ 2)) := by
  have hu := (adaptiveGaussianA_tendsto.pow 2).const_mul (21 / 10 : ℝ)
  have hl :
    Filter.Tendsto (fun _ : ℝ ↦ (21 / 10 : ℝ) * ((20115621 / 25000000) / (10971611 / 5000000)) ^ 2)
      Filter.atTop (nhds ((21 / 10 : ℝ) * ((20115621 / 25000000) / (10971611 / 5000000)) ^ 2)) :=
    tendsto_const_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with L hL
    have hbase :
      ((21 / 10 : ℝ) * ((20115621 / 25000000) / (10971611 / 5000000)) ^ 2) * L ^ 2 ≤
        (4 / 9 : ℝ) * L ^ 2 := by
      apply mul_le_mul_of_nonneg_right (by norm_num only) (sq_nonneg L)
    have h1 :=
      jointSurplusCutoff_asymptotic_lower hL.le (by norm_num only : (0 : ℝ) ≤ 130)
        (by norm_num only : (0 : ℝ) < 30)
    have h2 :=
      jointSurplusCutoff_asymptotic_lower hL.le (by norm_num only : (0 : ℝ) ≤ 155)
        (by norm_num only : (0 : ℝ) < 29)
    apply (le_div_iff₀ (sq_pos_of_pos hL)).2
    exact le_min hbase (le_min h1 h2)
  · filter_upwards [Filter.eventually_ge_atTop (25000 : ℝ)] with L hL
    have hs : 0 < L ^ 2 := sq_pos_of_pos (by linarith only [hL])
    have hc : jointSurplusGlobal L ≤ jointSurplusCutoff 155 29 L :=
      (min_le_right _ _).trans (min_le_right _ _)
    apply (div_le_iff₀ hs).2
    exact hc.trans (jointSurplus_lt_adaptive hL).le

end PseudoPrime.PrimeTestBounds.MillerRabin

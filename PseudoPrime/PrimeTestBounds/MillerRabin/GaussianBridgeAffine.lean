/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianWitnessCutoff
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianLogPolyCurvature
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Affine scale for the Gaussian concavity interval -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The affine square-root scale used to compare the K131 kernel with the
Gaussian cutoff on the concavity interval. -/
@[expose]
noncomputable def gaussianBridgeScale (L : ℝ) : ℝ :=
  519674 / 1000000 * L - 123 / 10

private theorem bridge_exp_le {L : ℝ} (hL : 9055 / 4 ≤ L) :
    Real.exp (-(L / 11000) ^ 2) ≤ (77440000 / 80719721 : ℝ) := by
  have hs := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 9055 / 4) hL 2
  have hu : ((9055 / 4 : ℝ) / 11000) ^ 2 ≤ (L / 11000) ^ 2 := by nlinarith only [hs]
  rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
  have ht := Real.sum_le_exp_of_nonneg (sq_nonneg (L / 11000)) 2
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one, pow_zero, pow_one, div_one, zero_add] at ht
  nlinarith only [ht, hu]

/-- From log `9055 / 4` onward the square of the affine K131 scale is
strictly below the Gaussian witness cutoff. The reciprocal exponential bound
reduces the comparison to a quadratic with positive nonconstant coefficients. -/
theorem gaussian_bridge_scale_sq_lt {L : ℝ} (hL : 9055 / 4 ≤ L) :
    gaussianBridgeScale L ^ 2 < gaussianWitnessCutoff L := by
  have hp : 0 ≤ L := by linarith only [hL]
  have hs := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 9055 / 4) hL 2
  have he :=
    mul_le_mul_of_nonneg_left (bridge_exp_le hL) (show 0 ≤ (53 / 4 : ℝ) * L by linarith only [hp])
  rw [gaussianCutoff_eq_quadratic (show 663 ≤ L by linarith only [hL]), gaussianBridgeScale]
  nlinarith only [he, hs, hL]

/-- The endpoints of the logarithm interval map to the two rational endpoints
of the K131 concavity interval. -/
theorem gaussian_bridge_scale_mem {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) :
    gaussianBridgeScale L ∈ Set.Icc (465644807 / 400000 : ℝ) (1036273 / 250) := by
  unfold gaussianBridgeScale
  exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

/-- A rejecting base below the squared K131 scale lies within the Gaussian
cutoff on the entire half-line starting at log `9055 / 4`. -/
theorem gaussian_bridge_bound {L a : ℝ} (hL : 9055 / 4 ≤ L) (ha : a ≤ gaussianBridgeScale L ^ 2) :
    a ≤ gaussianWitnessCutoff L := by exact ha.trans (gaussian_bridge_scale_sq_lt hL).le

/-- The two radius endpoints suffice for the strict K131 gap on the whole
logarithmic interval once the expanded comparison has nonpositive curvature. -/
theorem gaussian_bridge_gap_pos {G : ℝ → ℝ} {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000)
    (hconc : ConcaveOn ℝ (Set.Icc (465644807 / 400000 : ℝ) (1036273 / 250)) G)
    (hleft : 1 / 200 < G (465644807 / 400000)) (hright : 1 / 200 < G (1036273 / 250)) :
    1 / 200 < G (gaussianBridgeScale L) := by
  have hy := gaussian_bridge_scale_mem hL
  have he := hy.1.trans hy.2
  exact
    (lt_min hleft hright).trans_le
      (hconc.min_le_of_mem_Icc (Set.left_mem_Icc.mpr he) (Set.right_mem_Icc.mpr he) hy)

end PseudoPrime.PrimeTestBounds.MillerRabin

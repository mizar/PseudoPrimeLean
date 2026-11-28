/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialTaylorRatio
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianLogPolyCurvature
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianBridgeAffine
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Bernstein
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Exponential majorant for the dominant K131 curvature term -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Degree-seventeen upper polynomial for the exponential at rate 19/16.
The tail allowance uses the largest Taylor ratio on the interval from zero to three. -/
@[expose]
noncomputable def k131ExpUpper (u : ℝ) : ℝ :=
  (∑ k ∈ Finset.range 17, ((19 / 16 : ℝ) * u) ^ k / (k.factorial : ℝ)) +
    ((19 / 16 : ℝ) * u) ^ 17 / (17 : ℕ).factorial / (1 - (57 / 16 : ℝ) / 18)

/-- The K131 polynomial majorizes the exponential on the normalized interval. -/
theorem k131_exp_le_upper {u : ℝ} (hu : u ∈ Set.Icc 0 3) :
    Real.exp ((19 / 16 : ℝ) * u) ≤ k131ExpUpper u := by
  unfold k131ExpUpper
  apply Analysis.exp_le_taylor_ratio (q := (57 / 16 : ℝ) / 18) (n := 17)
  · linarith only [hu.1]
  · norm_num only
  · norm_num only
  · linarith only [hu.2]

private theorem k131_exp_constant_lt : Real.exp (133 / 8) < (2 : ℝ) ^ 24 := by
  have he : (133 / 8 : ℝ) < (24 : ℕ) * Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have h := Real.exp_lt_exp.mpr he
  rw [Real.exp_natCast_mul, Real.exp_log (by norm_num only : (0 : ℝ) < 2)] at h
  exact h

/-- The dominant curvature check can use the polynomial majorant
instead of the exponential. It then bounds the normalized contribution by minus one. -/
theorem k131_dominant_curvature_lt {y : ℝ} (hy : 0 < y)
    (hlog : (2 * Real.log y : ℝ) ∈ Set.Icc 14 17) (Q : Polynomial ℝ)
    (hsign : Q.eval (2 * Real.log y) + (2 : ℝ) ^ 24 * k131ExpUpper (2 * Real.log y - 14) ≤ 0) :
    logPowerPoly (-(19 / 8 : ℝ)) Q y < -1 := by
  have hu : (2 * Real.log y - 14 : ℝ) ∈ Set.Icc 0 3 :=
    ⟨by linarith only [hlog.1], by linarith only [hlog.2]⟩
  have hp : y ^ (19 / 8 : ℝ) < (2 : ℝ) ^ 24 * k131ExpUpper (2 * Real.log y - 14) := by
    rw [Real.rpow_def_of_pos hy,
      show Real.log y * (19 / 8 : ℝ) = 133 / 8 + (19 / 16) * (2 * Real.log y - 14) by ring,
      Real.exp_add]
    exact
      (mul_lt_mul_of_pos_right k131_exp_constant_lt (Real.exp_pos _)).trans_le
        (mul_le_mul_of_nonneg_left (k131_exp_le_upper hu) (by norm_num only))
  unfold logPowerPoly
  rw [Real.rpow_neg hy.le, inv_mul_eq_div]
  apply (div_lt_iff₀ (Real.rpow_pos_of_pos hy _)).mpr
  linarith only [hsign, hp]

/-- The entire affine-radius interval lies in the logarithmic domain used
by the K131 coefficient certificates. -/
theorem k131_radius_log_mem {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) :
    2 * Real.log (gaussianBridgeScale L) ∈ Set.Icc 14 17 := by
  have hy := gaussian_bridge_scale_mem hL
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 465644807 / 400000) (j := 10) (n := 12) (lo := 7)
        (hi := 8) (by decide +kernel)).1
  have hhi :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1036273 / 250) (j := 12) (n := 12) (lo := 8)
        (hi := 17 / 2) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlo hhi
  have hpos : 0 < gaussianBridgeScale L :=
    (by norm_num only : (0 : ℝ) < 465644807 / 400000).trans_le hy.1
  exact
    ⟨by linarith only [hlo, Real.log_le_log (by norm_num only) hy.1], by
      linarith only [hhi, Real.log_le_log hpos hy.2]⟩

/-- The first Bernstein row delivers the dominant curvature bound once the
expanded coefficients of the corrected polynomial are enclosed by that row. -/
theorem k131_dominant_of_bernstein {y : ℝ} (hy : 0 < y)
    (hlog : (2 * Real.log y : ℝ) ∈ Set.Icc 14 17) (Q : Polynomial ℝ)
    (c : Fin (k131BernsteinDegree 0 + 1) → ℝ) (hc : ∀ j, c j ≤ (k131BernsteinUpper 0 j : ℝ))
    (hrep :
      ∀ t : Set.Icc (0 : ℝ) 1,
        Q.eval (14 + 3 * (t : ℝ)) + (2 : ℝ) ^ 24 * k131ExpUpper (3 * (t : ℝ)) =
          ∑ j, c j * bernstein (k131BernsteinDegree 0) j t) :
    logPowerPoly (-(19 / 8 : ℝ)) Q y < -1 := by
  apply k131_dominant_curvature_lt hy hlog Q
  have hu : 2 * Real.log y - 14 ∈ Set.Icc (0 : ℝ) 3 :=
    ⟨by linarith only [hlog.1], by linarith only [hlog.2]⟩
  have hn :=
    k131_bernstein_interval_neg 0 (by norm_num only : (0 : ℝ) < 3) hu
      (fun u ↦ Q.eval (14 + u) + (2 : ℝ) ^ 24 * k131ExpUpper u) c hc
      (fun t ↦ by simpa only [sub_zero, zero_add] using hrep t)
  have he : 14 + (2 * Real.log y - 14) = 2 * Real.log y := by ring
  rw [he] at hn
  exact hn.le

end PseudoPrime.PrimeTestBounds.MillerRabin

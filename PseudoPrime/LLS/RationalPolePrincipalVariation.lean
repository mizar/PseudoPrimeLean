/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RationalPolePrincipalAbel
/-! # Numerical variation budget for the scaled fourth-pole principal weight -/

public section

namespace PseudoPrime.LLS.PaperStatements
/-- The weighted derivative factors into a scale constant and the unit kernel derivative. -/
theorem fourScaledWeight_weighted_deriv {x t : ℝ} (hx : 0 < x) (ht : 0 < t) (htx : t ≤ x) :
    t ^ (3 / 4 : ℝ) * |deriv (fourScaledWeight x) t| =
    (x ^ (3 / 4 : ℝ) / (x * Real.sqrt x)) *
      ((t / x) ^ (3 / 4 : ℝ) * |fourPoleWeightDeriv (t / x)|) := by
  rw [(fourScaledWeight_hasDerivAt hx ht htx).deriv]
  dsimp only [fourScaledWeightDeriv]
  rw [abs_div, abs_of_pos (mul_pos hx (Real.sqrt_pos.mpr hx)),
    Real.div_rpow ht.le hx.le]
  have hp := (Real.rpow_pos_of_pos hx (3 / 4 : ℝ)).ne'
  symm
  calc
    _ = (x ^ (3 / 4 : ℝ) * (x ^ (3 / 4 : ℝ))⁻¹) *
        (t ^ (3 / 4 : ℝ) * (|fourPoleWeightDeriv (t / x)| / (x * Real.sqrt x))) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hp, one_mul]

/-- Change variables from `[2,x]` to `[2/x,1]` in the absolute derivative integral. -/
theorem fourScaledWeight_variation_integral {x : ℝ} (hx : 2 ≤ x) :
    (∫ t : ℝ in (2 : ℝ)..x, t ^ (3 / 4 : ℝ) * |deriv (fourScaledWeight x) t|) =
    (x ^ (3 / 4 : ℝ) / Real.sqrt x) *
      ∫ u : ℝ in (2 / x)..1, u ^ (3 / 4 : ℝ) * |fourPoleWeightDeriv u| := by
  have hx0 : 0 < x := (by norm_num only : (0 : ℝ) < 2).trans_le hx
  rw [intervalIntegral.integral_congr (fun t ht ↦
    fourScaledWeight_weighted_deriv hx0 ((by norm_num only : (0 : ℝ) < 2).trans_le
      (by simpa only [Set.uIcc_of_le hx] using ht : t ∈ Set.Icc 2 x).1)
      (by simpa only [Set.uIcc_of_le hx] using ht : t ∈ Set.Icc 2 x).2)]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div
      (fun u : ℝ ↦ u ^ (3 / 4 : ℝ) * |fourPoleWeightDeriv u|) hx0.ne', div_self hx0.ne']
  simp only [smul_eq_mul]
  calc
    _ = (x * x⁻¹) * ((x ^ (3 / 4 : ℝ) / Real.sqrt x) *
        ∫ u : ℝ in (2 / x)..1, u ^ (3 / 4 : ℝ) * |fourPoleWeightDeriv u|) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hx0.ne', one_mul]


/-- The scaled endpoint plus weighted variation is below `2 x^(1/4)` for `x ≥ 2`. -/
theorem fourScaledWeight_variation_lt_two {x : ℝ} (hx : 2 ≤ x) :
    x ^ (3 / 4 : ℝ) * |fourScaledWeight x x| +
      (∫ t : ℝ in (2 : ℝ)..x, t ^ (3 / 4 : ℝ) * |deriv (fourScaledWeight x) t|) <
      2 * x ^ (1 / 4 : ℝ) := by
  have hx0 : 0 < x := (by norm_num only : (0 : ℝ) < 2).trans_le hx
  have hf : x ^ (3 / 4 : ℝ) / Real.sqrt x = x ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hx0]
    norm_num only
  have hm := intervalIntegral.integral_mono_interval
    (div_nonneg (by norm_num only : (0 : ℝ) ≤ 2) hx0.le)
    ((div_le_one hx0).mpr hx) (le_refl (1 : ℝ))
    ((MeasureTheory.ae_restrict_mem measurableSet_Ioc).mono (fun u hu ↦
      mul_nonneg (Real.rpow_nonneg hu.1.le (3 / 4 : ℝ)) (abs_nonneg _)))
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by norm_num only : (0 : ℝ) ≤ 1)).mpr fourPoleWeightDeriv_integral.1)
  rw [fourScaledWeight_variation_integral hx, hf]
  have hEnd : x ^ (3 / 4 : ℝ) * |fourScaledWeight x x| =
      x ^ (1 / 4 : ℝ) * |fourPoleWeight 1| := by
    dsimp only [fourScaledWeight]
    have hk : fourPoleKernelWeight 1 = fourPoleWeight 1 :=
      fourPoleKernelWeight_eq (by norm_num only : (0 : ℝ) < 1)
        (by norm_num only [Real.log_one] : Real.log (1 : ℝ) ≤ 28 / 25)
    rw [div_self hx0.ne', hk,
      abs_div, abs_of_nonneg (Real.sqrt_nonneg x)]
    calc
      _ = (x ^ (3 / 4 : ℝ) / Real.sqrt x) * |fourPoleWeight 1| := by ring
      _ = _ := by rw [hf]
  rw [hEnd]
  have he : (∫ u : ℝ in Set.Ioc 0 1,
      u ^ (3 / 4 : ℝ) * |deriv fourPoleKernelWeight u|) =
      ∫ u : ℝ in Set.Ioc 0 1, u ^ (3 / 4 : ℝ) * |fourPoleWeightDeriv u| := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    change u ^ (3 / 4 : ℝ) * |deriv fourPoleKernelWeight u| =
      u ^ (3 / 4 : ℝ) * |fourPoleWeightDeriv u|
    rw [(fourPoleKernelWeight_hasDerivAt hu.1
      ((Real.log_nonpos hu.1.le hu.2).trans_lt (by norm_num only))).deriv]
  have hk : fourPoleKernelWeight 1 = fourPoleWeight 1 :=
    fourPoleKernelWeight_eq (by norm_num only) (by norm_num only [Real.log_one])
  have hvar := fourPoleKernelWeight_variation_lt_two
  rw [he, hk] at hvar
  rw [intervalIntegral.integral_of_le (by norm_num only : (0 : ℝ) ≤ 1)] at hm
  calc
    _ ≤ x ^ (1 / 4 : ℝ) *
        (|fourPoleWeight 1| +
          ∫ u in Set.Ioc 0 1, u ^ (3 / 4 : ℝ) * |fourPoleWeightDeriv u|) := by
      nlinarith only [mul_le_mul_of_nonneg_left hm
        (Real.rpow_nonneg hx0.le (1 / 4 : ℝ))]
    _ < 2 * x ^ (1 / 4 : ℝ) := by
      nlinarith only [mul_lt_mul_of_pos_left hvar
        (Real.rpow_pos_of_pos hx0 (1 / 4 : ℝ))]


/-- Under RH, the finite principal sum differs from its integral on `[2,x]` by
at most `26 x^(1/4) + 20/sqrt x`. The interval below two is not included here. -/
theorem fourScaledWeight_error_le (hRH : RiemannHypothesis) {x : ℝ} (hx : 2 ≤ x) :
    |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        ArithmeticFunction.vonMangoldt n * fourScaledWeight x n) -
      (∫ t : ℝ in (2 : ℝ)..x, fourScaledWeight x t)| ≤
      26 * x ^ (1 / 4 : ℝ) + 20 / Real.sqrt x := by
  have h := fourScaledWeight_principal_error hRH hx
  have hv := fourScaledWeight_variation_lt_two hx
  nlinarith only [h, hv]

end PseudoPrime.LLS.PaperStatements

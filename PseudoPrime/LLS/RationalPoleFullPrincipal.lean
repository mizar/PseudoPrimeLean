/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RationalPoleFullMoments

/-! # Numerical full principal error and cutoff gap -/

public section

namespace PseudoPrime.LLS.PaperStatements

/-- On the positive full support, the weighted derivative of the scaled actual weight
is bounded by the scaled logarithmic-moment majorant. -/
theorem fourScaledWeight_full_deriv_le {x t : ℝ} (hx : 0 < x) (ht : 0 < t)
    (htx : t ≤ Real.exp (28 / 25 : ℝ) * x) :
    t ^ (3 / 4 : ℝ) * |deriv (fourScaledWeight x) t| ≤
      (x ^ (3 / 4 : ℝ) / (x * Real.sqrt x)) *
        ((t / x) ^ (3 / 4 : ℝ) * fourPoleVariationMajorant (t / x)) := by
  have hu := div_pos ht hx
  have hl : Real.log (t / x) ≤ 28 / 25 := (Real.log_le_iff_le_exp hu).mpr ((div_le_iff₀ hx).mpr htx)
  rw [(fourScaledWeight_global_deriv hx ht).deriv, ite_eq_left hl]
  have he :
    t ^ (3 / 4 : ℝ) * |fourPoleWeightDeriv (t / x) / (x * Real.sqrt x)| =
      (x ^ (3 / 4 : ℝ) / (x * Real.sqrt x)) *
        ((t / x) ^ (3 / 4 : ℝ) * |fourPoleWeightDeriv (t / x)|) := by
    rw [abs_div, abs_of_pos (mul_pos hx (Real.sqrt_pos.mpr hx)), Real.div_rpow ht.le hx.le]
    have hp := (Real.rpow_pos_of_pos hx (3 / 4 : ℝ)).ne'
    symm
    calc
      _ =
          (x ^ (3 / 4 : ℝ) * (x ^ (3 / 4 : ℝ))⁻¹) *
            (t ^ (3 / 4 : ℝ) * (|fourPoleWeightDeriv (t / x)| / (x * Real.sqrt x))) :=
        by ring
      _ = _ := by rw [mul_inv_cancel₀ hp, one_mul]
  rw [he]
  exact
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (fourPoleWeightDeriv_abs_le hu hl) (Real.rpow_nonneg hu.le _))
      (div_nonneg (Real.rpow_nonneg hx.le _) (mul_nonneg hx.le (Real.sqrt_nonneg x)))

/-- For scale at least two, the full-support weighted derivative integral is below
`x^(1/4)`. Scale the exact majorant moment and restrict its nonnegative integral. -/
theorem fourScaledWeight_full_variation {x : ℝ} (hx : 2 ≤ x) :
    (∫ t : ℝ in (2 : ℝ)..(Real.exp (28 / 25 : ℝ) * x),
        t ^ (3 / 4 : ℝ) * |deriv (fourScaledWeight x) t|) <
      x ^ (1 / 4 : ℝ) := by
  let b := Real.exp (28 / 25 : ℝ)
  let y := b * x
  let M : ℝ → ℝ := fun u ↦ u ^ (3 / 4 : ℝ) * fourPoleVariationMajorant u
  have hx0 : 0 < x := (by norm_num only : (0 : ℝ) < 2).trans_le hx
  have hb0 : 0 < b := Real.exp_pos _
  have hb : 1 ≤ b := Real.one_le_exp_iff.mpr (by norm_num only)
  have hy : 2 ≤ y := hx.trans (le_mul_of_one_le_left hx0.le hb)
  have hM : IntervalIntegrable M MeasureTheory.volume 0 b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb0.le).mpr fourPole_full_majorant_integral.1
  have hMc : IntervalIntegrable (fun t ↦ M (t / x)) MeasureTheory.volume 0 y := by
    have h := hM.comp_mul_left (c := x⁻¹)
    simpa only [zero_div, div_inv_eq_mul, inv_mul_eq_div, zero_mul] using h
  have hR :
    IntervalIntegrable (fun t ↦ (x ^ (3 / 4 : ℝ) / (x * Real.sqrt x)) * M (t / x))
      MeasureTheory.volume 2 y := by
    apply (hMc.const_mul _).mono_set
    rw [Set.uIcc_of_le (by linarith only [hy] : (0 : ℝ) ≤ y), Set.uIcc_of_le hy]
    exact Set.Icc_subset_Icc_left (by norm_num only)
  have hL :
    IntervalIntegrable (fun t ↦ t ^ (3 / 4 : ℝ) * |deriv (fourScaledWeight x) t|)
      MeasureTheory.volume 2 y := by
    have h :=
      MeasureTheory.IntegrableOn.mul_continuousOn
        (fourScaledWeight_deriv_integrableOn (y := y) hx0).norm
        (Real.continuous_rpow_const (by norm_num only : (0 : ℝ) ≤ 3 / 4)).continuousOn isCompact_Icc
    simpa only [Real.norm_eq_abs, mul_comm] using
      (intervalIntegrable_iff_integrableOn_Icc_of_le hy).mpr h
  have hI :=
    intervalIntegral.integral_mono_on hy hL hR
      (fun t ht ↦
        fourScaledWeight_full_deriv_le hx0 ((by norm_num only : (0 : ℝ) < 2).trans_le ht.1) ht.2)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_div M hx0.ne'] at hI
  have hratio : y / x = b := mul_div_cancel_right₀ b hx0.ne'
  rw [hratio] at hI
  simp only [smul_eq_mul] at hI
  have hf : x ^ (3 / 4 : ℝ) / Real.sqrt x = x ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hx0]
    norm_num only
  have he :
    x ^ (3 / 4 : ℝ) / (x * Real.sqrt x) * (x * ∫ u : ℝ in (2 / x)..b, M u) =
      x ^ (1 / 4 : ℝ) * ∫ u : ℝ in (2 / x)..b, M u := by
    calc
      _ = (x ^ (3 / 4 : ℝ) / Real.sqrt x) * ∫ u : ℝ in (2 / x)..b, M u := by
        calc
          _ = (x * x⁻¹) * ((x ^ (3 / 4 : ℝ) / Real.sqrt x) * ∫ u : ℝ in (2 / x)..b, M u) := by ring
          _ = _ := by rw [mul_inv_cancel₀ hx0.ne', one_mul]
      _ = _ := by rw [hf]
  rw [he] at hI
  have hpos : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioc 0 b)] M := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
    have hl : Real.log u ≤ 28 / 25 := (Real.log_le_iff_le_exp hu.1).mpr hu.2
    have hv : 0 ≤ fourPoleCoord u := by
      dsimp only [fourPoleCoord]
      linarith only [hl]
    have hu0 : 0 < u := hu.1
    dsimp only [M, fourPoleVariationMajorant]
    exact
      mul_nonneg (Real.rpow_nonneg hu.1.le _)
        (mul_nonneg
          (div_nonneg (Real.exp_nonneg _)
            (mul_nonneg (mul_nonneg (by norm_num only) hu0.le) (Real.sqrt_nonneg _)))
          (add_nonneg (mul_nonneg (by norm_num only) (pow_nonneg hv 3))
            (mul_nonneg (by norm_num only) (sq_nonneg _))))
  have hm :=
    intervalIntegral.integral_mono_interval (div_nonneg (by norm_num only : (0 : ℝ) ≤ 2) hx0.le)
      ((div_le_iff₀ hx0).mpr hy) (le_refl b) hpos hM
  have hbound : (∫ u : ℝ in (0 : ℝ)..b, M u) < 1 := by
    rw [intervalIntegral.integral_of_le hb0.le]
    exact fourPole_full_majorant_lt_one
  have hlt := mul_lt_mul_of_pos_left (hm.trans_lt hbound) (Real.rpow_pos_of_pos hx0 (1 / 4 : ℝ))
  rw [mul_one] at hlt
  exact hI.trans_lt hlt

/-- Under RH and for scale at least two, the full principal series differs from its
exact full main term by at most `13 x^(1/4) + 40/sqrt x`. -/
theorem fourPole_full_principal_error_le (hRH : RiemannHypothesis) {x : ℝ} (hx : 2 ≤ x) :
    |(∑' n : ℕ, (MellinKernel.summand rationalPoleFourKernel) (1 : DirichletCharacter ℂ 1) x n).re -
          Real.sqrt x * (2 * (13 / 25 : ℝ) * Real.exp (14 / 25) / (1 + 13 / 25) ^ 4)| ≤
      13 * x ^ (1 / 4 : ℝ) + 40 / Real.sqrt x := by
  have h := fourPole_full_principal_error hRH hx
  rw [fourScaledWeight_full_integral ((by norm_num only : (0 : ℝ) < 2).trans_le hx)] at h
  have hv := fourScaledWeight_full_variation hx
  linarith only [h, hv]

/-- Under RH, twice the unit-cutoff principal sum minus the full principal series
is bounded below by its exact main gap minus `65 x^(1/4) + 120/sqrt x`.
This is the principal contribution needed when subtracting the positive tail in
a finite no-witness comparison. -/
theorem fourPole_principal_gap_lower (hRH : RiemannHypothesis) {x : ℝ} (hx : 2 ≤ x) :
    Real.sqrt x *
          (2 * ((484820459 / 528581976 : ℝ) * Real.exp (-(14 / 13))) -
            (2 * (13 / 25 : ℝ) * Real.exp (14 / 25) / (1 + 13 / 25) ^ 4)) -
        (65 * x ^ (1 / 4 : ℝ) + 120 / Real.sqrt x) ≤
      2 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * fourScaledWeight x n) -
        (∑' n : ℕ,
            (MellinKernel.summand rationalPoleFourKernel) (1 : DirichletCharacter ℂ 1) x n).re := by
  have hc := (abs_le.mp (fourPole_cutoff_principal_error hRH hx)).1
  have hf := (abs_le.mp (fourPole_full_principal_error_le hRH hx)).2
  have he : 120 / Real.sqrt x = 3 * (40 / Real.sqrt x) := by ring
  rw [he]
  nlinarith only [hc, hf]

end PseudoPrime.LLS.PaperStatements

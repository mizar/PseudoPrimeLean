/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186FiniteSign
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186FiniteMoment
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaExpansion

import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianLaplaceSignCell

/-! # A low-cost finite-window bound for the K186 Gamma convolution -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The profile lower bound survives damping on the initial prefix. -/
private theorem k186_quarter_pointwise {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 35) :
    -(10 ^ 35 : ℝ) ≤ Real.exp (-(1 / 4 : ℝ) * t) * HighGaussianKernel.k186.realProfile.eval t := by
  have he : Real.exp (-(1 / 4 : ℝ) * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by norm_num only) ht.1)
  have hm : -(10 ^ 35 : ℝ) ≤ Real.exp (-(1 / 4 : ℝ) * t) * -(10 ^ 35 : ℝ) := by
    simpa only [one_mul] using
      mul_le_mul_of_nonpos_right he
        (neg_nonpos.mpr (pow_nonneg (by norm_num only : (0 : ℝ) ≤ 10) 35))
  exact hm.trans (mul_le_mul_of_nonneg_left (k186_profile_lower_to35 ht) (Real.exp_nonneg _))

/-- The signed quarter-rate integral over the initial prefix is bounded
below by the rectangle with the certified profile lower bound. -/
private theorem k186_quarter_prefix_le :
    -35 * (10 ^ 35 : ℝ) ≤
      ∫ t in (0 : ℝ)..35,
        Real.exp (-(1 / 4 : ℝ) * t) * HighGaussianKernel.k186.realProfile.eval t := by
  let f := fun t : ℝ ↦ Real.exp (-(1 / 4 : ℝ) * t) * HighGaussianKernel.k186.realProfile.eval t
  have hf : Continuous f :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      HighGaussianKernel.k186.realProfile.continuous
  have hconst : IntervalIntegrable (fun _ : ℝ ↦ -(10 ^ 35 : ℝ)) MeasureTheory.volume 0 35 :=
    continuous_const.intervalIntegrable _ _
  change _ ≤ ∫ t in (0 : ℝ)..35, f t
  calc
    _ = ∫ _ in (0 : ℝ)..35, -(10 ^ 35 : ℝ) := by
      rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_neg, neg_mul]
    _ ≤ _ :=
      intervalIntegral.integral_mono_on (by norm_num only) hconst (hf.intervalIntegrable 0 35)
        (fun _ ht ↦ k186_quarter_pointwise ht)

/-- Past the entrance at 35, the verified nonnegative profile up to 57
adds only a nonnegative amount to the quarter-rate prefix. -/
private theorem k186_quarter_integral_le {z : ℝ} (hz : z ∈ Set.Icc (35 : ℝ) 57) :
    -35 * (10 ^ 35 : ℝ) ≤
      ∫ t in (0 : ℝ)..z,
        Real.exp (-(1 / 4 : ℝ) * t) * HighGaussianKernel.k186.realProfile.eval t := by
  let f := fun t : ℝ ↦ Real.exp (-(1 / 4 : ℝ) * t) * HighGaussianKernel.k186.realProfile.eval t
  have hf : Continuous f :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      HighGaussianKernel.k186.realProfile.continuous
  have ht : 0 ≤ ∫ t in (35 : ℝ)..z, f t :=
    intervalIntegral.integral_nonneg hz.1
      (fun t ht ↦
        mul_nonneg (Real.exp_nonneg _) (k186_profile_nonneg_35_57 ⟨ht.1, ht.2.trans hz.2⟩))
  change _ ≤ ∫ t in (0 : ℝ)..z, f t
  rw [←
    intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable 0 35)
      (hf.intervalIntegrable 35 z)]
  exact k186_quarter_prefix_le.trans (le_add_of_nonneg_right ht)

/-- A rational Taylor bound at the left endpoint controls the common
exponential factor for the entire early high window. -/
private theorem k186_conv_decay_le {z : ℝ} (hz : 35 ≤ z) :
    Real.exp (-(5 / 2 : ℝ) * z) ≤ 1 / 10 ^ 38 := by
  have ha : Real.exp (-(5 / 2 : ℝ) * z) ≤ Real.exp (-((175 / 2 : ℚ) : ℝ)) := by
    apply Real.exp_le_exp.mpr
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
    linarith only [hz]
  have hb := negative_endpoint_exp_upper_valid (by norm_num only : (0 : ℚ) ≤ 175 / 2)
  have hc : negativeEndpointExpUpper (175 / 2) ≤ 1 / 10 ^ 38 := by decide +kernel
  exact
    (ha.trans hb).trans
      (by
        simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using
          (Rat.cast_le (K := ℝ)).mpr hc)

/-- Pull the endpoint factor out of the quarter-rate convolution. -/
private theorem k186_quarter_conv_eq (z : ℝ) :
    (∫ t in (0 : ℝ)..z,
        Real.exp ((1 / 4 : ℝ) * (z - t)) * HighGaussianKernel.k186.realProfile.eval t) =
      Real.exp (z / 4) *
        ∫ t in (0 : ℝ)..z,
          Real.exp (-(1 / 4 : ℝ) * t) * HighGaussianKernel.k186.realProfile.eval t := by
  have he (t : ℝ) :
    Real.exp ((1 / 4 : ℝ) * (z - t)) * HighGaussianKernel.k186.realProfile.eval t =
      Real.exp (z / 4) *
        (Real.exp (-(1 / 4 : ℝ) * t) * HighGaussianKernel.k186.realProfile.eval t) := by
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp only [he, intervalIntegral.integral_const_mul]

/-- Throughout the first part of the finite window, the first Gamma
convolution charges at most one twentieth in the comparison. -/
theorem k186_finite_gamma_conv_le {z : ℝ} (hz : z ∈ Set.Icc (35 : ℝ) 57) :
    Real.exp (-(11 / 4 : ℝ) * z) *
        max
          (-(∫ t in (0 : ℝ)..z,
              Real.exp ((1 / 4 : ℝ) * (z - t)) * HighGaussianKernel.k186.realProfile.eval t))
          0 ≤
      1 / 20 := by
  have hb := mul_le_mul_of_nonneg_left (k186_quarter_integral_le hz) (Real.exp_nonneg (z / 4))
  rw [k186_quarter_conv_eq]
  have hM : 0 ≤ Real.exp (z / 4) * (35 * 10 ^ 35) :=
    mul_nonneg (Real.exp_nonneg _) (by norm_num only)
  have hk := neg_le_neg hb
  rw [show -(Real.exp (z / 4) * (-35 * (10 ^ 35 : ℝ))) = Real.exp (z / 4) * (35 * 10 ^ 35) by
      ring] at hk
  have hm := max_le hk hM
  refine (mul_le_mul_of_nonneg_left hm (Real.exp_nonneg _)).trans ?_
  rw [← mul_assoc, ← Real.exp_add, show -(11 / 4 : ℝ) * z + z / 4 = -(5 / 2 : ℝ) * z by ring]
  exact
    (mul_le_mul_of_nonneg_right (k186_conv_decay_le hz.1)
          (by norm_num only : (0 : ℝ) ≤ 35 * 10 ^ 35)).trans
      (by norm_num only)

/-- The second Gamma convolution remains nonnegative until the first
finite-window sign boundary. -/
private theorem k186_finite_gamma_j_nonneg {z : ℝ} (hz : z ∈ Set.Icc (35 : ℝ) 57) :
    0 ≤
      ∫ t in (0 : ℝ)..z,
        HighGaussianKernel.k186.realProfile.eval t * Real.exp (-(9 / 4 : ℝ) * t) := by
  let f := fun t : ℝ ↦ HighGaussianKernel.k186.realProfile.eval t * Real.exp (-(9 / 4 : ℝ) * t)
  have hf : Continuous f :=
    HighGaussianKernel.k186.realProfile.continuous.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have ht : 0 ≤ ∫ t in (35 : ℝ)..z, f t :=
    intervalIntegral.integral_nonneg hz.1
      (fun t ht ↦
        mul_nonneg (k186_profile_nonneg_35_57 ⟨ht.1, ht.2.trans hz.2⟩) (Real.exp_nonneg _))
  change 0 ≤ ∫ t in (0 : ℝ)..z, f t
  rw [←
    intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable 0 35)
      (hf.intervalIntegrable 35 z)]
  exact add_nonneg k186_gamma_j_prefix_nonneg ht

/-- A common lower rectangle handles the late convolution tails at either rate. -/
private theorem k186_finite_conv_rect {s z : ℝ} (hs : 0 ≤ s) (hz : z ∈ Set.Icc (57 : ℝ) 65) :
    -(8 * (10 ^ 61 : ℝ) * Real.exp (-s * 57)) ≤
      ∫ t in (57 : ℝ)..z, Real.exp (-s * t) * HighGaussianKernel.k186.realProfile.eval t := by
  let C : ℝ := -(10 ^ 61 : ℝ) * Real.exp (-s * 57)
  let f := fun t : ℝ ↦ Real.exp (-s * t) * HighGaussianKernel.k186.realProfile.eval t
  have hC : C ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by norm_num only) (Real.exp_nonneg _)
  have hf : Continuous f :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      HighGaussianKernel.k186.realProfile.continuous
  have hpt (t : ℝ) (ht : t ∈ Set.Icc (57 : ℝ) z) : C ≤ f t := by
    have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left ht.1 (neg_nonpos.mpr hs))
    have hB := k186_profile_lower_57_65 ⟨ht.1, ht.2.trans hz.2⟩
    calc
      C ≤ Real.exp (-s * t) * -(10 ^ 61 : ℝ) := by
        dsimp only [C]
        rw [mul_comm (-(10 ^ 61 : ℝ))]
        exact mul_le_mul_of_nonpos_right he (by norm_num only)
      _ ≤ f t := mul_le_mul_of_nonneg_left hB (Real.exp_nonneg _)
  have hl :=
    intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hz.1
      (continuous_const.intervalIntegrable (a := (57 : ℝ)) (b := z)) (hf.intervalIntegrable 57 z)
      hpt
  rw [intervalIntegral.integral_const, smul_eq_mul] at hl
  have hlen : z - 57 ≤ 8 := by linarith only [hz.2]
  have hlow := mul_le_mul_of_nonpos_right hlen hC
  change _ ≤ ∫ t in (57 : ℝ)..z, f t
  exact
    (show -(8 * (10 ^ 61 : ℝ) * Real.exp (-s * 57)) = 8 * C
          by
          dsimp only [C]
          ring).le.trans
      (hlow.trans hl)

/-- The exponentially damped tail rectangle is below one millionth. -/
private theorem k186_finite_tail_small :
    8 * (10 ^ 61 : ℝ) * Real.exp (-(11 / 4 : ℝ) * 57) ≤ 1 / 10 ^ 6 := by
  have h := negative_endpoint_exp_upper_valid (by norm_num only : (0 : ℚ) ≤ 627 / 4)
  have hc : negativeEndpointExpUpper (627 / 4) ≤ 1 / 10 ^ 68 := by decide +kernel
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  rw [show -(11 / 4 : ℝ) * 57 = -(627 / 4 : ℝ) by norm_num only]
  have hb : Real.exp (-(627 / 4 : ℝ)) ≤ 1 / 10 ^ 68 :=
    h.trans
      (by
        simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using
          (Rat.cast_le (K := ℝ)).mpr hc)
  exact
    (mul_le_mul_of_nonneg_left hb (by norm_num only : (0 : ℝ) ≤ 8 * 10 ^ 61)).trans
      (by norm_num only)

/-- The late sign changes in the first convolution still fit the same
one-twentieth budget after pulling out the endpoint exponential. -/
private theorem k186_finite_gamma_i_late {z : ℝ} (hz : z ∈ Set.Icc (57 : ℝ) 65) :
    Real.exp (-(11 / 4 : ℝ) * z) *
        max
          (-(∫ t in (0 : ℝ)..z,
              Real.exp ((1 / 4 : ℝ) * (z - t)) * HighGaussianKernel.k186.realProfile.eval t))
          0 ≤
      1 / 20 := by
  let f := fun t : ℝ ↦ Real.exp (-(1 / 4 : ℝ) * t) * HighGaussianKernel.k186.realProfile.eval t
  have hf : Continuous f :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      HighGaussianKernel.k186.realProfile.continuous
  have hp := k186_quarter_integral_le (z := 57) ⟨by norm_num only, le_rfl⟩
  have hr := k186_finite_conv_rect (s := 1 / 4) (by norm_num only) hz
  have hlow :
    -35 * (10 ^ 35 : ℝ) - 8 * (10 ^ 61 : ℝ) * Real.exp (-(1 / 4 : ℝ) * 57) ≤
      ∫ t in (0 : ℝ)..z, f t := by
    rw [←
      intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable 0 57)
        (hf.intervalIntegrable 57 z)]
    exact add_le_add hp hr
  let M : ℝ := 35 * 10 ^ 35 + 8 * 10 ^ 61 * Real.exp (-(1 / 4 : ℝ) * 57)
  have hM : 0 ≤ M :=
    add_nonneg (by norm_num only) (mul_nonneg (by norm_num only) (Real.exp_nonneg _))
  have hb : -(∫ t in (0 : ℝ)..z, f t) ≤ M := by
    dsimp only [M]
    linarith only [hlow]
  rw [k186_quarter_conv_eq]
  have hc := mul_le_mul_of_nonneg_left hb (Real.exp_nonneg (z / 4))
  rw [mul_neg] at hc
  refine
    (mul_le_mul_of_nonneg_left (max_le hc (mul_nonneg (Real.exp_nonneg _) hM))
          (Real.exp_nonneg _)).trans
      ?_
  rw [← mul_assoc, ← Real.exp_add, show -(11 / 4 : ℝ) * z + z / 4 = -(5 / 2 : ℝ) * z by ring]
  have he := k186_conv_decay_le ((by norm_num only : (35 : ℝ) ≤ 57).trans hz.1)
  have he' :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hz.1 (by norm_num only : -(5 / 2 : ℝ) ≤ 0))
  have hp' := mul_le_mul_of_nonneg_right he (by norm_num only : (0 : ℝ) ≤ 35 * 10 ^ 35)
  have hr' :
    Real.exp (-(5 / 2 : ℝ) * z) * (8 * 10 ^ 61 * Real.exp (-(1 / 4 : ℝ) * 57)) ≤ 1 / 10 ^ 6 := by
    have hp₀ : (0 : ℝ) ≤ 8 * 10 ^ 61 := by norm_num only
    refine (mul_le_mul_of_nonneg_right he' (mul_nonneg hp₀ (Real.exp_nonneg _))).trans ?_
    rw [mul_left_comm, ← Real.exp_add,
      show -(5 / 2 : ℝ) * 57 + -(1 / 4 : ℝ) * 57 = -(11 / 4 : ℝ) * 57 by norm_num only]
    exact k186_finite_tail_small
  dsimp only [M]
  rw [mul_add]
  exact (add_le_add hp' hr').trans (by norm_num only)

/-- The late second convolution has a small damped negative part. -/
private theorem k186_finite_gamma_j_late {z : ℝ} (hz : z ∈ Set.Icc (57 : ℝ) 65) :
    Real.exp (-z / 2) *
        -(∫ t in (0 : ℝ)..z,
            HighGaussianKernel.k186.realProfile.eval t * Real.exp (-(9 / 4 : ℝ) * t)) ≤
      1 / 10 ^ 6 := by
  let f := fun t : ℝ ↦ HighGaussianKernel.k186.realProfile.eval t * Real.exp (-(9 / 4 : ℝ) * t)
  have hf : Continuous f :=
    HighGaussianKernel.k186.realProfile.continuous.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hp : 0 ≤ ∫ t in (0 : ℝ)..57, f t := k186_finite_gamma_j_nonneg ⟨by norm_num only, le_rfl⟩
  have hr : -(8 * (10 ^ 61 : ℝ) * Real.exp (-(9 / 4 : ℝ) * 57)) ≤ ∫ t in (57 : ℝ)..z, f t := by
    simpa only [f, mul_comm] using k186_finite_conv_rect (s := 9 / 4) (by norm_num only) hz
  have hlow : -(∫ t in (0 : ℝ)..z, f t) ≤ 8 * 10 ^ 61 * Real.exp (-(9 / 4 : ℝ) * 57) := by
    rw [←
      intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable 0 57)
        (hf.intervalIntegrable 57 z)]
    linarith only [hp, hr]
  have he : Real.exp (-z / 2) ≤ Real.exp (-57 / 2) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_neg hz.1) (by norm_num only))
  refine (mul_le_mul_of_nonneg_left hlow (Real.exp_nonneg _)).trans ?_
  have hp' : (0 : ℝ) ≤ 8 * 10 ^ 61 := by norm_num only
  refine (mul_le_mul_of_nonneg_right he (mul_nonneg hp' (Real.exp_nonneg _))).trans ?_
  rw [mul_left_comm, ← Real.exp_add,
    show (-57 / 2 : ℝ) + -(9 / 4 : ℝ) * 57 = -(11 / 4 : ℝ) * 57 by norm_num only]
  exact k186_finite_tail_small

/-- Across the finite high window, H33 reduces the common contour
to the signed Gamma derivative sum and a small uniform error. -/
theorem k186_finite_common_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive)
    (hn : χ ≠ 1) (hi : χ⁻¹ = χ) (he : χ.Even) {z : ℝ} (hz : z ∈ Set.Icc (35 : ℝ) 65) :
    highCommonContour .k186 (Real.exp (z - 5)) ≤
      Real.exp (-(11 / 4 : ℝ) * z) *
          (∑ j ∈ Finset.range (HighGaussianKernel.k186.realProfile.natDegree + 1),
            highGammaCoeff .k186 j *
              ((Polynomial.derivative^[j]) HighGaussianKernel.k186.realProfile).eval z) +
        1 / 20 +
        1 / 10 ^ 6 := by
  have ha :=
    high_common_contour_h33 .k186 hp hn hi he ((by norm_num only : (0 : ℝ) < 35).trans_le hz.1)
  have hs : (11 / 4 : ℝ) - 5 / 2 = 1 / 4 := by norm_num only
  have hd : (11 / 4 : ℝ) - 1 / 2 = 9 / 4 := by norm_num only
  simp only [HighGaussianKernel.pole, Rat.cast_div, Rat.cast_ofNat, hs, hd] at ha
  have ht :
    0 ≤
      ∑' n : ℕ,
        Real.exp (-((1 / 2 : ℝ) + 2 * (n + 2)) * z) *
          highProfileLaplace .k186 (9 / 4 - 2 * (n + 2)) :=
    tsum_nonneg (fun n ↦ mul_nonneg (Real.exp_nonneg _) (high_profile_laplace_nonneg .k186 _))
  have hBudget :
    (Real.exp (-(11 / 4 : ℝ) * z) *
          max
            (-(∫ t in (0 : ℝ)..z,
                Real.exp ((1 / 4 : ℝ) * (z - t)) * HighGaussianKernel.k186.realProfile.eval t))
            0 ≤
        1 / 20) ∧
      (Real.exp (-z / 2) *
          -(∫ t in (0 : ℝ)..z,
              HighGaussianKernel.k186.realProfile.eval t * Real.exp (-(9 / 4 : ℝ) * t)) ≤
        1 / 10 ^ 6) := by
    by_cases h : z ≤ 57
    · refine ⟨k186_finite_gamma_conv_le ⟨hz.1, h⟩, ?_⟩
      exact
        (mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _)
              (neg_nonpos.mpr (k186_finite_gamma_j_nonneg ⟨hz.1, h⟩))).trans
          (by norm_num only)
    · exact
        ⟨k186_finite_gamma_i_late ⟨(le_of_not_ge h), hz.2⟩,
          k186_finite_gamma_j_late ⟨(le_of_not_ge h), hz.2⟩⟩
  have hb :=
    mul_le_mul_of_nonneg_left
      (le_max_left
        (-(∫ t in (0 : ℝ)..z,
            Real.exp ((1 / 4 : ℝ) * (z - t)) * HighGaussianKernel.k186.realProfile.eval t))
        0)
      (Real.exp_nonneg (-(11 / 4 : ℝ) * z))
  rw [ha, mul_sub]
  linarith only [ht, hBudget.1, hBudget.2, hb]

end PseudoPrime.PrimeTestBounds.MillerRabin

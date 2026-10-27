/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalLogRightZeros

/-! # Genus correction kernels at high ordinate without RH -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For real part at most one and absolute ordinate at least one, the combined
genus kernel centered at two is at most `4/(1+Im(z)^2)`. Combine reciprocals
before estimating norms and compare the squared distances. This bounds both
halves of the critical strip and preserves quadratic ordinate decay. -/
theorem norm_two_center_genus_kernel_le_quadratic_of_large_im {z : ℂ} (hzhi : z.re ≤ 1)
    (hheight : 1 ≤ |z.im|) : ‖1 / ((2 : ℂ) - z) + 1 / z‖ ≤ 4 / (1 + z.im ^ 2) := by
  have him : 1 ≤ z.im ^ 2 := by nlinarith only [hheight, sq_abs z.im, sq_nonneg (|z.im| - 1)]
  have hden : 0 < 1 + z.im ^ 2 := by nlinarith only [sq_nonneg z.im]
  have hzsq : (1 + z.im ^ 2) / 4 ≤ ‖z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    nlinarith only [him, sq_nonneg z.re]
  have hwsq : 1 + z.im ^ 2 ≤ ‖(2 : ℂ) - z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    norm_num only [Complex.sub_re, Complex.sub_im, Complex.re_ofNat, Complex.im_ofNat, zero_sub,
      neg_sq]
    nlinarith only [hzhi, sq_nonneg (z.re - 1)]
  have hzpos : 0 < ‖z‖ := by nlinarith only [hzsq, hden, norm_nonneg z]
  have hwpos : 0 < ‖(2 : ℂ) - z‖ := by nlinarith only [hwsq, hden, norm_nonneg ((2 : ℂ) - z)]
  have hprod := mul_le_mul hzsq hwsq hden.le (sq_nonneg ‖z‖)
  have hpnonneg := mul_nonneg (norm_nonneg z) (norm_nonneg ((2 : ℂ) - z))
  have hp : (1 + z.im ^ 2) / 2 ≤ ‖z‖ * ‖(2 : ℂ) - z‖ := by nlinarith only [hprod, hpnonneg, hden]
  rw [one_div_add_one_div (norm_pos_iff.mp hwpos) (norm_pos_iff.mp hzpos), norm_div, norm_mul,
    sub_add_cancel]
  norm_num only [Complex.norm_ofNat]
  apply (div_le_div_iff₀ (mul_pos hwpos hzpos) hden).mpr
  nlinarith only [hp]

/-- For real part in the closed critical strip, the inverse quadratic ordinate
weight is at most four times the inverse-square distance from three halves.
Compare the two denominators explicitly. This connects ordinate weights to the
unconditional shifted genus-mass estimate. -/
theorem inverse_quadratic_im_le_four_shifted_mass {z : ℂ} (hzlo : 0 ≤ z.re) (hzhi : z.re ≤ 1) :
    1 / (1 + z.im ^ 2) ≤ 4 * ‖(((3 / 2 : ℝ) : ℂ) - z)⁻¹‖ ^ 2 := by
  have hden : 0 < 1 + z.im ^ 2 := by nlinarith only [sq_nonneg z.im]
  have hs : ‖((3 / 2 : ℝ) : ℂ) - z‖ ^ 2 = (3 / 2 - z.re) ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_sub]
    ring
  have hspos : 0 < ‖((3 / 2 : ℝ) : ℂ) - z‖ ^ 2 := by
    rw [hs]
    nlinarith only [hzhi, sq_nonneg z.im, sq_nonneg (z.re - 1)]
  have hsle : ‖((3 / 2 : ℝ) : ℂ) - z‖ ^ 2 ≤ 4 * (1 + z.im ^ 2) := by
    rw [hs]
    nlinarith only [hzlo, hzhi, sq_nonneg z.im, mul_nonneg hzlo (sub_nonneg.mpr hzhi)]
  rw [norm_inv, inv_pow, ← one_div]
  have hratio : 1 / (1 + z.im ^ 2) ≤ 4 / ‖((3 / 2 : ℝ) : ℂ) - z‖ ^ 2 := by
    apply (div_le_div_iff₀ hden hspos).mpr
    simpa only [one_mul] using hsle
  simpa only [div_eq_mul_inv, one_mul] using hratio

/-- For a point in the closed critical strip with absolute ordinate at least one,
the combined genus kernel is at most sixteen times its shifted inverse-square
mass. Compose the quadratic kernel and distance comparisons. This removes any
need for a zero gap when estimating the remote genus correction. -/
theorem norm_two_center_genus_kernel_le_shifted_mass_of_large_im {z : ℂ} (hzlo : 0 ≤ z.re)
    (hzhi : z.re ≤ 1) (hheight : 1 ≤ |z.im|) :
    ‖1 / ((2 : ℂ) - z) + 1 / z‖ ≤ 16 * ‖(((3 / 2 : ℝ) : ℂ) - z)⁻¹‖ ^ 2 := by
  have hk := norm_two_center_genus_kernel_le_quadratic_of_large_im hzhi hheight
  have hm := inverse_quadratic_im_le_four_shifted_mass hzlo hzhi
  simp only [div_eq_mul_inv, one_mul] at hk hm ⊢
  linarith only [hk, hm]

/-- For a primitive nonprincipal character with nonprincipal inverse, every
genus term of absolute ordinate at least one is at most sixteen times its actual
shifted multiplicity mass. Nonzero divisor multiplicity places the zero in the
open critical strip; analyticity makes the multiplicity nonnegative. This is
the pointwise input for the unconditional correction-tail bound. -/
theorem norm_completed_genus_term_le_shifted_mass_of_large_im {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {ρ : ℂ}
    (hheight : 1 ≤ |ρ.im|) :
    ‖(MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) * (1 / ((2 : ℂ) - ρ) + 1 / ρ)‖ ≤
      16 * (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        ‖(((3 / 2 : ℝ) : ℂ) - ρ)⁻¹‖ ^ 2 := by
  by_cases hD : MeromorphicOn.divisor χ.completedLFunction Set.univ ρ = 0
  · simp only [hD, Int.cast_zero, zero_mul, mul_zero, norm_zero, le_refl]
  · have hz := dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD
    have hlo := (completedLFunction_zero_re_pos hp hinv hz).le
    have hhi := (completedLFunction_zero_re_lt_one hne hz).le
    have hAn : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
      (χ.differentiable_completedLFunction hne).analyticAt z
    have hnonneg : (0 : ℝ) ≤ MeromorphicOn.divisor χ.completedLFunction Set.univ ρ := by
      exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn ρ
    rw [norm_mul, Complex.norm_intCast, abs_of_nonneg hnonneg]
    have hb :=
      mul_le_mul_of_nonneg_left
        (norm_two_center_genus_kernel_le_shifted_mass_of_large_im hlo hhi hheight) hnonneg
    nlinarith only [hb]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalLogKernelBounds

/-! # Regularized logarithmic zero bounds retaining real-part weights -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- At scale at least two and nonnegative real part, the half-power factor is at
most twice `x^Re z`. Compare the powers at the two scales on the positive axis.
This retains the real part required by the log-free density estimate. -/
theorem norm_half_power_le_two_rpow {x : ℝ} (hx : 2 ≤ x) {z : ℂ} (hzlo : 0 ≤ z.re) :
    ‖(1 - (2 : ℂ) ^ (-z)) * (x : ℂ) ^ z‖ ≤ 2 * x ^ z.re := by
  have hxpos : 0 < x := by linarith only [hx]
  have hhalf : 0 < x / 2 := div_pos hxpos (by norm_num only)
  have hfirst : ‖(x : ℂ) ^ z‖ = x ^ z.re := Complex.norm_cpow_eq_rpow_re_of_pos hxpos z
  have hsecond : ‖((x / 2 : ℝ) : ℂ) ^ z‖ ≤ x ^ z.re := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hhalf]
    exact Real.rpow_le_rpow hhalf.le (by linarith only [hxpos]) hzlo
  rw [half_power_difference_eq hxpos.le]
  exact (norm_sub_le _ _).trans (by linarith only [hfirst, hsecond])

/-- For real part between one half and one, the combined genus kernel centered
at two is bounded by four times the inverse quadratic ordinate weight. Combine
the two reciprocals before taking norms and compare squared distances.
This preserves quadratic high-ordinate decay without RH. -/
theorem norm_two_center_genus_kernel_le_quadratic {z : ℂ} (hzlo : 1 / 2 ≤ z.re) (hzhi : z.re ≤ 1) :
    ‖1 / ((2 : ℂ) - z) + 1 / z‖ ≤ 4 / (1 + z.im ^ 2) := by
  have hden : 0 < 1 + z.im ^ 2 := by nlinarith only [sq_nonneg z.im]
  have hzsq : (1 + z.im ^ 2) / 4 ≤ ‖z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    nlinarith only [hzlo, sq_nonneg z.im, sq_nonneg (z.re - 1 / 2)]
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
  have hz : z ≠ 0 := norm_pos_iff.mp hzpos
  have hw : (2 : ℂ) - z ≠ 0 := norm_pos_iff.mp hwpos
  rw [one_div_add_one_div hw hz, norm_div, norm_mul]
  have he : ((2 : ℂ) - z) + z = 2 := sub_add_cancel 2 z
  rw [he]
  norm_num only [Complex.norm_ofNat]
  apply (div_le_div_iff₀ (mul_pos hwpos hzpos) hden).mpr
  nlinarith only [hp]

/-- For a nonprincipal character, scale at least two, and real part in the right
half of the critical strip, the regularized zero term is bounded by its divisor
multiplicity times `(8x^Re z + 4 log 2)/(1 + Im z²)`. Bound the original half-power
term and the combined genus correction separately. This is the pointwise input
for density-weighted zero sums, retaining both real part and ordinate decay. -/
theorem norm_regularizedLogHalfZeroTerm_le_right_re {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hne : χ ≠ 1) {x : ℝ} (hx : 2 ≤ x) {ρ : ℂ} (hlo : 1 / 2 ≤ ρ.re) (hhi : ρ.re ≤ 1) :
    ‖regularizedLogHalfZeroTerm χ x ρ‖ ≤
      (8 * x ^ ρ.re + 4 * Real.log 2) *
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) /
        (1 + ρ.im ^ 2) := by
  let D := MeromorphicOn.divisor χ.completedLFunction Set.univ ρ
  have hAn : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
    (χ.differentiable_completedLFunction hne).analyticAt z
  have hD : (0 : ℝ) ≤ D := by exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn ρ
  have hDactual : 0 ≤ (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) := hD
  have hden : 0 < 1 + ρ.im ^ 2 := by nlinarith only [sq_nonneg ρ.im]
  have hsq : (1 + ρ.im ^ 2) / 4 ≤ ‖ρ‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    nlinarith only [hlo, sq_nonneg ρ.im, sq_nonneg (ρ.re - 1 / 2)]
  have hsqp : 0 < ‖ρ‖ ^ 2 := by linarith only [hsq, hden]
  have hratio : 1 / ‖ρ‖ ^ 2 ≤ 4 / (1 + ρ.im ^ 2) := by
    rw [div_le_div_iff₀ hsqp hden]
    linarith only [hsq]
  have hp := norm_half_power_le_two_rpow hx (by linarith only [hlo] : 0 ≤ ρ.re)
  have hxpos : 0 < x := by linarith only [hx]
  have hxp : 0 ≤ x ^ ρ.re := (Real.rpow_pos_of_pos hxpos ρ.re).le
  have hhalf : ‖completedLogHalfZeroTerm χ x ρ‖ ≤ 8 * x ^ ρ.re * (D : ℝ) / (1 + ρ.im ^ 2) := by
    have he :
      ‖completedLogHalfZeroTerm χ x ρ‖ =
        (D : ℝ) * ‖(1 - (2 : ℂ) ^ (-ρ)) * (x : ℂ) ^ ρ‖ / ‖ρ‖ ^ 2 := by
      simp only [completedLogHalfZeroTerm, norm_div, norm_mul, norm_pow, Complex.norm_intCast,
        abs_of_nonneg hDactual]
      ring
    rw [he]
    have hfirst := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hD) hsqp.le
    have hsecond :=
      mul_le_mul_of_nonneg_left hratio (mul_nonneg (by linarith only [hxp] : 0 ≤ 2 * x ^ ρ.re) hD)
    simp only [div_eq_mul_inv] at hfirst hsecond ⊢
    nlinarith only [hfirst, hsecond]
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num only)
  have hlnorm : ‖(Real.log 2 : ℂ)‖ = Real.log 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl]
  have hg := norm_two_center_genus_kernel_le_quadratic hlo hhi
  have hgm := mul_le_mul_of_nonneg_left hg (mul_nonneg hl hD)
  have hn :=
    norm_sub_le (completedLogHalfZeroTerm χ x ρ)
      ((Real.log 2 : ℂ) * ((D : ℂ) * (1 / ((2 : ℂ) - ρ) + 1 / ρ)))
  rw [norm_mul, norm_mul, Complex.norm_intCast, abs_of_nonneg hD, hlnorm] at hn
  change
    ‖regularizedLogHalfZeroTerm χ x ρ‖ ≤ (8 * x ^ ρ.re + 4 * Real.log 2) * (D : ℝ) / (1 + ρ.im ^ 2)
  change ‖regularizedLogHalfZeroTerm χ x ρ‖ ≤ _ at hn
  simp only [div_eq_mul_inv, one_mul] at hhalf hgm hn ⊢
  nlinarith only [hn, hhalf, hgm]

/-- For a finite set in the right half of the critical strip, sum the regularized
kernel bound while retaining actual divisor multiplicity, the factor `x^Re z`,
and the inverse quadratic ordinate weight. The character is nonprincipal and the
scale is at least two. This exposes the precise weighted sums needed from density. -/
theorem sum_norm_regularizedLogHalfZeroTerm_le_right_weighted_sum {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) {x : ℝ} (hx : 2 ≤ x) (S : Finset ℂ)
    (hlo : ∀ ρ ∈ S, 1 / 2 ≤ ρ.re) (hhi : ∀ ρ ∈ S, ρ.re ≤ 1) :
    ∑ ρ ∈ S, ‖regularizedLogHalfZeroTerm χ x ρ‖ ≤
      8 *
          (∑ ρ ∈ S,
            x ^ ρ.re * (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) /
              (1 + ρ.im ^ 2)) +
        4 * Real.log 2 *
          (∑ ρ ∈ S,
            (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) / (1 + ρ.im ^ 2)) := by
  calc
    _ ≤
        ∑ ρ ∈ S,
          (8 * x ^ ρ.re + 4 * Real.log 2) *
              (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) /
            (1 + ρ.im ^ 2) :=
      Finset.sum_le_sum
        (fun ρ hρ ↦ norm_regularizedLogHalfZeroTerm_le_right_re hne hx (hlo ρ hρ) (hhi ρ hρ))
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun ρ _ ↦ by ring)

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction

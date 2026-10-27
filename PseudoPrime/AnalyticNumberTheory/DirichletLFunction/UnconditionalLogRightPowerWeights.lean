/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalLogRightZeros

/-! # Power-weighted right-strip regularized zero bounds -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a nonprincipal character, scale at least two, and real part in the right
half-strip, the regularized norm is at most `(8+4 log 2)` times its divisor-weighted
power term. Since `x^Re(rho) >= 1`, the same power weight absorbs the genus
correction. This avoids a second unweighted family-mass error. -/
theorem norm_regularizedLogHalfZeroTerm_le_right_power_weight {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) {x : ℝ} (hx : 2 ≤ x) {ρ : ℂ} (hlo : 1 / 2 ≤ ρ.re)
    (hhi : ρ.re ≤ 1) :
    ‖regularizedLogHalfZeroTerm χ x ρ‖ ≤
      (8 + 4 * Real.log 2) *
        ((MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          (x ^ ρ.re / (1 + ρ.im ^ 2))) := by
  have hAn : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
    (χ.differentiable_completedLFunction hne).analyticAt z
  have hD : (0 : ℝ) ≤ MeromorphicOn.divisor χ.completedLFunction Set.univ ρ := by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn ρ
  have hpow : 1 ≤ x ^ ρ.re := Real.one_le_rpow (by linarith only [hx]) (by linarith only [hlo])
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num only)
  have hcoeff : 8 * x ^ ρ.re + 4 * Real.log 2 ≤ (8 + 4 * Real.log 2) * x ^ ρ.re := by
    nlinarith only [mul_nonneg hlog (sub_nonneg.mpr hpow)]
  calc
    _ ≤
        (8 * x ^ ρ.re + 4 * Real.log 2) *
            (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) /
          (1 + ρ.im ^ 2) :=
      norm_regularizedLogHalfZeroTerm_le_right_re hne hx hlo hhi
    _ ≤
        ((8 + 4 * Real.log 2) * x ^ ρ.re) *
            (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) /
          (1 + ρ.im ^ 2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff hD)
        (add_nonneg zero_le_one (sq_nonneg ρ.im))
    _ = _ := by ring

/-- A completed zero in a rectangle from real threshold at most one to real part
one has its real part between those endpoints. Extract the rectangle coordinates.
This provides the pointwise hypotheses for right-strip kernel estimates. -/
theorem completedZerosInRectangle_halfStrip_realpart_bounds {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) {σ : ℝ} (hσ : σ ≤ 1) (H : ℕ) {ρ : ℂ}
    (hρ :
      ρ ∈
        completedZerosInRectangle χ hne ((σ : ℂ) - (H : ℝ) * Complex.I)
          ((1 : ℂ) + (H : ℝ) * Complex.I)) :
    σ ≤ ρ.re ∧ ρ.re ≤ 1 := by
  have hb := (mem_completedZerosInRectangle_iff.mp hρ).1
  rw [dirichletCompletedLFunctionRectangleBox, Rectangle.rectangleClosedBox,
    Complex.mem_reProdIm] at hb
  have hre := hb.1
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    mul_zero, zero_mul, sub_zero, Complex.add_re, add_zero, Complex.one_re] at hre
  rwa [Set.uIcc_of_le hσ] at hre

/-- For a nonprincipal character, scale at least two, and a rectangular threshold
between one half and one, the finite regularized norm sum is bounded by its actual
divisor-weighted power sum times `8+4 log 2`. Sum the pointwise estimate after
extracting real-part bounds. This connects regularized kernels to weighted density. -/
theorem sum_norm_regularizedLogHalfZeroTerm_rectangle_le_right_power_weight {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) {x σ : ℝ} (hx : 2 ≤ x) (hσlo : 1 / 2 ≤ σ)
    (hσhi : σ ≤ 1) (H : ℕ) :
    (∑
        ρ ∈
          completedZerosInRectangle χ hne ((σ : ℂ) - (H : ℝ) * Complex.I)
            ((1 : ℂ) + (H : ℝ) * Complex.I),
        ‖regularizedLogHalfZeroTerm χ x ρ‖) ≤
      (8 + 4 * Real.log 2) *
        ∑
          ρ ∈
            completedZerosInRectangle χ hne ((σ : ℂ) - (H : ℝ) * Complex.I)
              ((1 : ℂ) + (H : ℝ) * Complex.I),
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            (x ^ ρ.re / (1 + ρ.im ^ 2)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ρ hρ
  have hre := completedZerosInRectangle_halfStrip_realpart_bounds hne hσhi H hρ
  exact norm_regularizedLogHalfZeroTerm_le_right_power_weight hne hx (hσlo.trans hre.1) hre.2

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction

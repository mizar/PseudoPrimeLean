/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCounting
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroClassification

/-!
# Zero-contribution terms and ledgers for the Riemann zeta function

This file records the standard "zero contribution" closed forms that appear in explicit-formula
arguments for `riemannZeta` (the residue attached to a zero `ρ` of the reciprocal/logarithmic
kernel `x^(ρ-1)/(ρ(ρ-1))`, `x^ρ/ρ²`), and the finite ledgers summing these contributions over the
zeros in a rectangle. These are purely closed-form expressions in
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity`
and elementary complex arithmetic; they do not reference any particular contour-kernel
construction.
-/

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The reciprocal-kernel contribution attached to one zeta zero. -/
noncomputable def riemannZetaReciprocalZeroContribution (x : ℝ) (ρ : ℂ) : ℂ :=
  -(riemannZetaZeroMultiplicity ρ : ℂ) * (x : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))

/-- The logarithmic-kernel contribution attached to one zeta zero. -/
noncomputable def riemannZetaLogZeroContribution (x : ℝ) (ρ : ℂ) : ℂ :=
  -(riemannZetaZeroMultiplicity ρ : ℂ) * (x : ℂ) ^ ρ / ρ ^ 2

/-- The reciprocal residue ledger for an arbitrary closed contour rectangle. -/
noncomputable def riemannZetaReciprocalContourZeroLedger (x : ℝ) (z w : ℂ) : ℂ :=
  ∑ ρ ∈ riemannZetaZerosInAnyRectangle z w, riemannZetaReciprocalZeroContribution x ρ

/-- The logarithmic residue ledger for an arbitrary closed contour rectangle. -/
noncomputable def riemannZetaLogContourZeroLedger (x : ℝ) (z w : ℂ) : ℂ :=
  ∑ ρ ∈ riemannZetaZerosInAnyRectangle z w, riemannZetaLogZeroContribution x ρ

/-- **The pointwise logarithmic-kernel zero-contribution norm formula under RH.** -/
theorem norm_riemannZetaLogZeroContribution_of_rh (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x)
    {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hre : 0 ≤ ρ.re) :
    ‖riemannZetaLogZeroContribution x ρ‖ =
      Real.sqrt x * (riemannZetaZeroMultiplicity ρ : ℝ) / Complex.normSq ρ := by
  have hhalf := riemannZeta_zero_re_eq_half_of_riemannHypothesis hRH hρ hre
  unfold riemannZetaLogZeroContribution
  rw [norm_div, norm_mul, norm_neg, Complex.norm_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hx,
    hhalf]
  rw [show x ^ (1 / 2 : ℝ) = Real.sqrt x from by rw [Real.sqrt_eq_rpow]]
  rw [show ‖ρ ^ 2‖ = Complex.normSq ρ from by rw [norm_pow, Complex.normSq_eq_norm_sq]]
  ring

/-- **The pointwise reciprocal-kernel zero-contribution norm formula under RH.** -/
theorem norm_riemannZetaReciprocalZeroContribution_of_rh (hRH : RiemannHypothesis) {x : ℝ}
    (hx : 0 < x) {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hre : 0 ≤ ρ.re) :
    ‖riemannZetaReciprocalZeroContribution x ρ‖ =
      (riemannZetaZeroMultiplicity ρ : ℝ) / (Real.sqrt x * Complex.normSq ρ) := by
  have hhalf := riemannZeta_zero_re_eq_half_of_riemannHypothesis hRH hρ hre
  have hnormeq : ‖ρ - 1‖ = ‖ρ‖ := by
    have hsq := normSq_riemannZeta_zero_sub_one_eq_of_riemannHypothesis hRH hρ hre
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsq
    exact (sq_eq_sq₀ (norm_nonneg (ρ - 1)) (norm_nonneg ρ)).mp hsq
  have hre_sub : (ρ - 1).re = -(1 / 2) := by
    rw [Complex.sub_re, hhalf]
    simp only [Complex.one_re]
    norm_num only
  unfold riemannZetaReciprocalZeroContribution
  rw [norm_div, norm_mul, norm_neg, Complex.norm_natCast, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, hre_sub, hnormeq]
  rw [show x ^ (-(1 / 2 : ℝ)) = (Real.sqrt x)⁻¹ from by rw [Real.rpow_neg hx.le, Real.sqrt_eq_rpow]]
  rw [Complex.normSq_eq_norm_sq]
  ring

end PseudoPrime.AnalyticNumberTheory.RiemannZeta

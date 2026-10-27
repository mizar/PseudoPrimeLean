/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.MangoldtDirichletBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.Basic

/-! # Numerical bounds for ordinary L-function logarithmic derivatives

Absolute convergence to the right of one and the logarithmic-power integral comparison
give explicit bounds uniform in the modulus, character, and imaginary part.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For real sigma greater than one and every height, the ordinary L-function logarithmic
derivative norm is at most (sigma-1)^(-2)+(sigma-1)^(-1). Bound the twisted series
by the untwisted von Mangoldt series and its integral comparison. The estimate is unconditional
and uniform in the modulus and character, including principal characters. -/
theorem norm_logDeriv_le_inv_gap {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {σ : ℝ}
    (hσ : 1 < σ) (t : ℝ) :
    ‖logDeriv χ.LFunction ((σ : ℂ) + t * Complex.I)‖ ≤ (σ - 1)⁻¹ ^ 2 + (σ - 1)⁻¹ := by
  have hn := norm_neg_deriv_div_dirichletLFunction_le_vonMangoldt_tsum χ hσ t
  simp only [neg_div, norm_neg] at hn
  exact hn.trans (Arithmetic.tsum_vonMangoldt_div_rpow_le hσ)

/-- At a real argument greater than one, the ordinary logarithmic derivative has
the explicit inverse-gap bound. Specialize the uniform vertical-line estimate to height zero.
This controls the ordinary part of the centered Poisson error. -/
theorem norm_logDeriv_real_le_inv_gap {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {σ : ℝ}
    (hσ : 1 < σ) : ‖logDeriv χ.LFunction (σ : ℂ)‖ ≤ (σ - 1)⁻¹ ^ 2 + (σ - 1)⁻¹ := by
  simpa only [Complex.ofReal_zero, zero_mul, add_zero] using norm_logDeriv_le_inv_gap χ hσ 0

/-- For any character and positive r, the ordinary logarithmic-derivative norm at
1+r is bounded by the explicit Euler ratio. Remove the character by the untwisted
von Mangoldt series, then keep the zeta denominator. The estimate is unconditional
and reduces the centered Poisson errors without changing the character hypotheses. -/
theorem norm_logDeriv_real_le_euler_ratio {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {r : ℝ}
    (hr : 0 < r) :
    ‖logDeriv χ.LFunction ((1 + r : ℝ) : ℂ)‖ ≤
      (r⁻¹ ^ 2 + (r + 1)⁻¹) / (1 + (2 : ℝ) ^ (-r) / r) := by
  have hs : 1 < 1 + r := by linarith only [hr]
  have hn := norm_neg_deriv_div_dirichletLFunction_le_vonMangoldt_tsum χ hs 0
  simp only [neg_div, norm_neg, Complex.ofReal_zero, zero_mul, add_zero] at hn
  exact hn.trans (Arithmetic.tsum_vonMangoldt_le_euler_ratio hr)

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction

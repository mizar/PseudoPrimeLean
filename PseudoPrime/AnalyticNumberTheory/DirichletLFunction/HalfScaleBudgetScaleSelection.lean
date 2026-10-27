/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.HalfScaleBudgetAbsorption

/-! # Polynomial scale selection for density and exponential errors -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- A polynomial time bound gives the logarithmic density scale and exponential decay
bound simultaneously when the polynomial exponent is at least four times the density constant. -/
theorem polynomial_scale_log_bounds {R x A : ℝ} {b : ℕ} (hR : 2 ≤ R) (hA : 0 ≤ A)
    (hb : 4 * A ≤ (b : ℝ)) (hx : R ^ b ≤ x) :
    2 * A * Real.log (R + 1) ≤ Real.log x ∧ -(1 / Real.log R) * Real.log x / 2 ≤ -(b : ℝ) / 2 := by
  have hRp : 0 < R := by linarith only [hR]
  have hlog : 0 < Real.log R := Real.log_pos (by linarith only [hR])
  have hl := Real.log_le_log (pow_pos hRp b) hx
  rw [Real.log_pow] at hl
  have hRadd : R + 1 ≤ 2 * R := by linarith only [hR]
  have hladd := Real.log_le_log (by linarith only [hR] : 0 < R + 1) hRadd
  rw [Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) hRp.ne'] at hladd
  have hl2 := Real.log_le_log (by norm_num only : (0 : ℝ) < 2) hR
  have hsum : Real.log (R + 1) ≤ 2 * Real.log R := by linarith only [hladd, hl2]
  have hm := mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) hA)
  have hbmul := mul_le_mul_of_nonneg_right hb hlog.le
  have hdiv := (le_div_iff₀ hlog).mpr hl
  constructor
  · nlinarith only [hm, hbmul, hl]
  · have he : -(1 / Real.log R) * Real.log x / 2 = -(Real.log x / Real.log R) / 2 := by ring
    rw [he]
    linarith only [hdiv]

/-- For positive amplitude and tolerance, choose a natural polynomial exponent above any
prescribed lower bound whose exponential error is below the tolerance. -/
theorem exists_small_exponential_at_nat_scale {B ε : ℝ} (hB : 0 < B) (hε : 0 < ε) (L : ℝ) :
    ∃ b : ℕ, L ≤ (b : ℝ) ∧ B * Real.exp (-(b : ℝ) / 2) ≤ ε := by
  obtain ⟨b, hb⟩ := exists_nat_gt (max L (2 * Real.log (B / ε)))
  refine ⟨b, (le_max_left _ _).trans hb.le, ?_⟩
  have hratio : 0 < B / ε := div_pos hB hε
  have hlog := (le_max_right L (2 * Real.log (B / ε))).trans hb.le
  have he := Real.exp_le_exp.mpr (by linarith only [hlog] : -(b : ℝ) / 2 ≤ -Real.log (B / ε))
  rw [Real.exp_neg, Real.exp_log hratio] at he
  have hm := mul_le_mul_of_nonneg_left he hB.le
  have hinv : B * (B / ε)⁻¹ = ε := by rw [inv_div, ← mul_div_assoc, mul_div_cancel_left₀ ε hB.ne']
  exact hm.trans_eq hinv

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction

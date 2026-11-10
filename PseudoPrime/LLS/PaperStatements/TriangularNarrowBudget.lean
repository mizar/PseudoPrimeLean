/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.TriangularNarrowPrincipal

/-! # Explicit principal budget for the width-eight kernel -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The shifted width-eighteen budget is at most the explicit width-eight budget.
The exponential lower bound follows from a finite positive Taylor sum; the numerical
coefficients are those used in the middle-range large-index argument. -/
private theorem narrow_budget {x : ℝ} (hx : 0 < x) :
    300000000 * Real.sqrt (Real.exp (-20) * x) + 1300000 * (Real.exp (-20) * x) ^ (1 / 4 : ℝ) ≤
      13700 * Real.sqrt x + 8800 * x ^ (1 / 4 : ℝ) := by
  have h5 : Real.exp (-5) ≤ (1 / 148 : ℝ) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 5) 20
    norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
      Nat.cast_one, pow_zero, pow_succ] at h
    have h' : (148 : ℝ) ≤ Real.exp 5 := by linarith only [h]
    rw [Real.exp_neg, one_div]
    exact (inv_le_inv₀ (Real.exp_pos 5) (by norm_num only)).2 h'
  have h10 : Real.exp (-10) ≤ (1 / 21904 : ℝ) := by
    have h' := mul_self_le_mul_self (Real.exp_pos (-5)).le h5
    rw [← Real.exp_add] at h'
    norm_num only at h' ⊢
    exact h'
  rw [Real.sqrt_mul (Real.exp_pos _).le, Real.mul_rpow (Real.exp_pos _).le hx.le]
  have hs : Real.sqrt (Real.exp (-20)) = Real.exp (-10) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    norm_num only
  have hr : Real.exp (-20) ^ (1 / 4 : ℝ) = Real.exp (-5) := by
    rw [← Real.exp_mul]
    norm_num only
  rw [hs, hr]
  have hsx := Real.sqrt_nonneg x
  have hrx := Real.rpow_nonneg hx.le (1 / 4 : ℝ)
  nlinarith only [h5, h10, hsx, hrx, mul_nonneg (sub_nonneg.mpr h5) hrx,
    mul_nonneg (sub_nonneg.mpr h10) hsx]

/-- Under RH, the width-eight principal sum at any positive scale is at most
`13700 * sqrt x + 8800 * x ^ (1 / 4)`. Apply the shifted width-eighteen
bound and its explicit numerical estimate for the middle-range argument. -/
theorem triangular8_principal_explicit (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ,
          (triangularMellinKernel (by norm_num only : (0 : ℝ) < 8)).summand
            (1 : DirichletCharacter ℂ 1) x n).re ≤
      13700 * Real.sqrt x + 8800 * x ^ (1 / 4 : ℝ) := by
  exact (triangular8_principal_upper hRH hx).trans (narrow_budget hx)

end PseudoPrime.LLS.PaperStatements

/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-! # The normalized Euler logarithm of zeta -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The Euler logarithm of zeta in the half-plane of absolute convergence.
Its coefficient at `n` is `Λ(n) / log n`; the totalized values at `0` and
`1` are zero. Exponentiation recovers zeta for `Re s > 1`. -/
noncomputable def backlundZetaLog (s : ℂ) : ℂ :=
  LSeries (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (Real.log n : ℂ)) s

/-- The Euler-log coefficient has norm at most one, including the totalized
zero-logarithm cases. The von Mangoldt function is nonnegative and at most
the natural logarithm. -/
private theorem norm_eulerLogCoeff_le_one (n : ℕ) :
    ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (Real.log n : ℂ)‖ ≤ 1 := by
  rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, abs_of_nonneg (Real.log_natCast_nonneg n)]
  by_cases hn : Real.log n = 0
  · rw [hn, div_zero]; norm_num only
  · have hp : 0 < Real.log n := lt_of_le_of_ne (Real.log_natCast_nonneg n) (Ne.symm hn)
    exact (div_le_one₀ hp).2 ArithmeticFunction.vonMangoldt_le_log

/-- The Euler logarithm exponentiates to zeta when `Re s > 1`. This is the
absolute-convergence form of the Euler-product identity. -/
theorem exp_backlundZetaLog {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (backlundZetaLog s) = riemannZeta s := by exact riemannZeta_eq_exp_LSeries hs

/-- For `Re s > 1`, the norm of the Euler logarithm is at most the real
logarithm of zeta at `Re s`. Bound the complex series by the sum of the
norms and identify the latter with the positive real Euler-log series. -/
theorem norm_backlundZetaLog_le {s : ℂ} (hs : 1 < s.re) :
    ‖backlundZetaLog s‖ ≤ Real.log (riemannZeta (s.re : ℂ)).re := by
  let f : ℕ → ℂ := fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (Real.log n : ℂ)
  have hsum : LSeriesSummable f s :=
    LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => norm_eulerLogCoeff_le_one n) hs
  have hterm (n : ℕ) :
    ‖LSeries.term f s n‖ = ArithmeticFunction.vonMangoldt n / ((n : ℝ) ^ s.re * Real.log n) := by
    by_cases hn : n = 0
    · subst n
      simp only [LSeries.term_zero, norm_zero, Nat.cast_zero, Real.log_zero, mul_zero, div_zero]
    · rw [LSeries.norm_term_eq]
      simp only [hn, ↓reduceIte, f, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        abs_of_nonneg (Real.log_natCast_nonneg n)]
      rw [div_div, mul_comm]
  change ‖∑' n, LSeries.term f s n‖ ≤ _
  calc
    _ ≤ ∑' n, ‖LSeries.term f s n‖ := norm_tsum_le_tsum_norm (summable_norm_iff.mpr hsum)
    _ = Real.log (riemannZeta (s.re : ℂ)).re := by
      rw [log_riemannZeta_eq hs]
      exact tsum_congr hterm

/-- The Euler logarithm is complex differentiable on `Re s > 1`. Its
coefficients are uniformly bounded, placing its abscissa of absolute
convergence at most one. -/
theorem differentiableAt_backlundZetaLog {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ backlundZetaLog s := by
  let f : ℕ → ℂ := fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (Real.log n : ℂ)
  have ha : LSeries.abscissaOfAbsConv f ≤ 1 :=
    LSeries.abscissaOfAbsConv_le_of_le_const ⟨1, fun n _ => norm_eulerLogCoeff_le_one n⟩
  have ht : LSeries.abscissaOfAbsConv f < (s.re : EReal) := ha.trans_lt (by exact_mod_cast hs)
  exact (LSeries_hasDerivAt ht).differentiableAt

end PseudoPrime.AnalyticNumberTheory.RiemannZeta

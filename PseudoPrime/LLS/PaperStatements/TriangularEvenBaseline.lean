/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Gamma.RealDigammaTrapezoid
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorLogDeriv

/-! # Even-character baseline for the triangular Gamma comparison -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The real digamma value at one quarter is bounded by the stated logarithmic
expression. Translate twice by the digamma recurrence and apply the trapezoid
upper bound at nine quarters. -/
theorem digamma_quarter_le_log_bound :
    (Complex.digamma ((1 / 4 : ℝ) : ℂ)).re ≤ Real.log (9 / 4 : ℝ) - 2 / 9 - 24 / 5 := by
  have ht :=
    (AnalyticNumberTheory.Gamma.real_digamma_trapezoid_bounds (r := 9 / 4) (by norm_num only)).2
  norm_num only at ht
  have hrec :=
    congrArg Complex.re
      (Complex.digamma_apply_add_nat (s := ((1 / 4 : ℝ) : ℂ))
        (AnalyticNumberTheory.Gamma.not_neg_nat_of_re_pos (by norm_num only [Complex.ofReal_re])) 2)
  simp only [← Complex.ofReal_natCast, ← Complex.ofReal_add, ← Complex.ofReal_inv,
    ← Complex.ofReal_sum, Complex.add_re, Complex.ofReal_re] at hrec
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat] at hrec
  linarith only [ht, hrec]

/-- The logarithmic part of the even-character baseline is at most `-14 / 43`.
The rational lower bound for pi and the elementary lower bound for `log (1+x)`
give an explicit rational estimate without numerical approximation. -/
theorem log_nine_fourths_sub_log_pi_le :
    Real.log (9 / 4 : ℝ) - Real.log Real.pi ≤ -(14 / 43 : ℝ) := by
  have hpi : (25 / 8 : ℝ) ≤ Real.pi := by linarith only [Real.pi_gt_d4]
  have hpilog := Real.log_le_log (by norm_num only : (0 : ℝ) < 25 / 8) hpi
  have hratio := Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 7 / 18 by norm_num only)
  have hratio' : (14 / 43 : ℝ) ≤ Real.log (25 / 18 : ℝ) := by
    norm_num only at hratio
    exact hratio
  have heq : Real.log (25 / 18 : ℝ) = Real.log (25 / 8 : ℝ) - Real.log (9 / 4 : ℝ) := by
    rw [← Real.log_div (by norm_num only : (25 / 8 : ℝ) ≠ 0) (by norm_num only : (9 / 4 : ℝ) ≠ 0)]
    norm_num only
  linarith only [hpilog, hratio', heq]

/-- The even-character real Gamma baseline is strictly below `-8 / 3`.
Combine the quarter-digamma upper bound with the rational logarithmic estimate;
this retains the negative contribution in the triangular comparison. -/
theorem gamma_even_baseline_lt :
    (-Real.log Real.pi + (Complex.digamma ((1 / 4 : ℝ) : ℂ)).re) / 2 < -(8 / 3 : ℝ) := by
  have hd := digamma_quarter_le_log_bound
  have hl := log_nine_fourths_sub_log_pi_le
  linarith only [hd, hl]

/-- The real logarithmic derivative of the Gamma factor of an even Dirichlet
character at the central point is below `-8 / 3`. The even Gamma-factor formula
reduces the claim to the quarter-digamma baseline bound. -/
theorem gamma_central_even_baseline_lt {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ : χ.Even) :
    (logDeriv χ.gammaFactor (1 / 2)).re < -(8 / 3 : ℝ) := by
  have hz : ((1 / 2 : ℂ) / 2) = ((1 / 4 : ℝ) : ℂ) := by
    norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  have hp : 0 < (((1 / 2 : ℂ)) / 2).re := by
    rw [hz]
    norm_num only [Complex.ofReal_re]
  have he :=
    AnalyticNumberTheory.DirichletLFunction.gammaLogDeriv_even_eq_digamma hχ (s := 1 / 2)
      (fun n ↦ AnalyticNumberTheory.Gamma.not_neg_nat_of_re_pos hp n)
  rw [he, hz, ← Complex.ofReal_log Real.pi_pos.le]
  simp only [Complex.add_re, Complex.div_ofNat_re, Complex.neg_re, Complex.ofReal_re]
  have hb := gamma_even_baseline_lt
  linarith only [hb]

end PseudoPrime.LLS.PaperStatements

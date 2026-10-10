/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.SquareCorrectedBounds
public import Mathlib.NumberTheory.Chebyshev
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeSumBounds

/-! Transfer quantitative Mangoldt-sum errors into general L-value bounds. -/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- For admissible RH data and cutoff at least one hundred, quantitative Mangoldt and psi
errors give simultaneous norm and reciprocal bounds with the zeta-at-two reciprocal factor.
Insert the arithmetic majorant error into the existing exponential bounds using nonnegative
degree. The analytic prime-sum inputs remain explicit;
no prime number theorem is assumed implicitly. -/
theorem norm_L_one_and_reciprocal_le_of_mangoldt_errors (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {x a b : ℝ} (hx : 100 ≤ x)
    (ha :
      |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / ((n : ℝ) * Real.log n)) -
            (Real.log (Real.log x) + Real.eulerMascheroniConstant)| ≤
        a)
    (hb : |Chebyshev.psi x - x| ≤ b) :
    ‖f.L 1‖ ≤
        Real.exp
          ((f.degree : ℝ) *
              (Real.log (Real.log x) + Real.eulerMascheroniConstant - 1 / Real.log x + a +
                b / (x * Real.log x)) +
            |Real.log f.analyticConductor| / (Real.sqrt x * Real.log x) +
            f.truncatedConductorErrorBound x) ∧
      1 / ‖f.L 1‖ ≤
        (6 / Real.pi ^ 2) ^ f.degree *
          Real.exp
            ((f.degree : ℝ) *
                (Real.log (Real.log x) + Real.eulerMascheroniConstant - 1 / Real.log x + a +
                  b / (x * Real.log x) +
                  3 / (2 * Real.sqrt x)) +
              |Real.log f.analyticConductor| / (Real.sqrt x * Real.log x) +
              f.truncatedConductorErrorBound x) := by
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 100) hx
  have hQ :=
    (abs_le.mp (AnalyticNumberTheory.Arithmetic.abs_truncatedMangoldtMajorant_error_le hx1 ha hb)).2
  have hQ' :
    AnalyticNumberTheory.Arithmetic.truncatedMangoldtMajorant x ≤
      Real.log (Real.log x) + Real.eulerMascheroniConstant - 1 / Real.log x + a +
        b / (x * Real.log x) := by
    linarith only [hQ]
  have hd := Nat.cast_nonneg (α := ℝ) f.degree
  constructor
  · refine
      (norm_L_one_and_reciprocal_le_exp_truncated_majorants f hf hRH
            (le_trans (by norm_num only : (2 : ℝ) ≤ 100) hx)).1.trans
        ?_
    apply Real.exp_le_exp.mpr
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hQ' hd) (le_refl _)) (le_refl _)
  · refine (reciprocal_norm_L_one_le_square_corrected f hf hRH hx).trans ?_
    apply
      mul_le_mul_of_nonneg_left _
        (pow_nonneg (div_nonneg (by norm_num only : (0 : ℝ) ≤ 6) (sq_nonneg Real.pi)) _)
    apply Real.exp_le_exp.mpr
    exact
      add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left (add_le_add hQ' (le_refl _)) hd) (le_refl _))
        (le_refl _)

end PseudoPrime.LLS.Extensions.GeneralLFunction

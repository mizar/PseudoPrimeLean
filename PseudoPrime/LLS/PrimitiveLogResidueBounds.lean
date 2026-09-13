/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveLogResidueClosedForms
import PseudoPrime.LLS.PrimitiveLogMainErrorBounds

/-!
# Combined parity-common upper bound for the `s = 0` log-kernel residue

Substitutes the completed-side derivative bound
(`DirichletLFunction.neg_re_deriv_logDeriv_completedLFunction_zero_le`
in `AnalyticNumberTheory/DirichletLFunction/QuadraticFunctionalConsequences.lean`)
and the numerical main-error bounds
(`PrimitiveLogMainErrorBounds.lean`) into the odd/even raw closed forms
(`PrimitiveLogResidueClosedForms.lean`), giving both parities the *same* upper bound
`(2 + log x)|Re B(χ)| + (1/2)(log N - log π) log x - 11/4`.
`PrimitiveLogResidueLedger.lean` uses these bounds after dispatching on parity.
-/

namespace PseudoPrime.LLS

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/--
Input/assumptions: `N ≥ 2`, `χ` primitive nontrivial quadratic odd mod `N`, GRH, `χ⁻¹ ≠ 1`,
`x ≥ 64`.
Conclusion:
`Re(residue) ≤ (2 + log x)|Re B(χ)| + (1/2)(log N - log π) log x - 11/4`.
Content: substitute
`DirichletLFunction.neg_re_deriv_logDeriv_completedLFunction_zero_le`
and
`llsPrimitiveLogOddMainError_le_neg_eleven_fourths` into
`DirichletLFunction.re_deriv_dirichletLogMellinZeroRegularization_zero_of_odd_raw`.
Role: the odd-parity log-kernel residue bound.
-/
theorem re_deriv_llsPrimitiveLogMellinZeroRegularization_zero_of_odd_le {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic)
    (hodd : χ.Odd) {x : ℝ} (hx : 64 ≤ x) :
    (deriv
          (dirichletLogMellinZeroRegularization
            x χ)
          0).re ≤
      (2 + Real.log x) * |primitiveBRe χ| +
          (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x -
        11 / 4 := by
  have hxpos : (0 : ℝ) < x := by linarith
  rw [re_deriv_dirichletLogMellinZeroRegularization_zero_of_odd_raw
      hN2 hGRH hprimitive hne hinv hquad hodd hxpos]
  have hD :=
    neg_re_deriv_logDeriv_completedLFunction_zero_le
      hGRH hprimitive hne hinv hquad hN2
  have hE := llsPrimitiveLogOddMainError_le_neg_eleven_fourths hx
  unfold Analysis.primitiveLogOddMainError at hE
  have hlogx_nn : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
  nlinarith [hD, hE, mul_le_mul_of_nonneg_right hD hlogx_nn]

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/--
Input/assumptions: `N ≥ 2`, `χ` primitive nontrivial quadratic mod `N`, GRH, `χ⁻¹ ≠ 1`,
`x ≥ 64`.
Conclusion:
`Re(iteratedDeriv 2 h 0 / 2) ≤ (2 + log x)|Re B(χ)| + (1/2)(log N - log π) log x - 11/4`.
Content: substitute
`DirichletLFunction.neg_re_deriv_logDeriv_completedLFunction_zero_le`
and
`llsPrimitiveLogEvenMainError_le_neg_eleven_fourths` into
`DirichletLFunction.re_iteratedDeriv_two_dirichletLogEvenZeroRegularization_zero_div_two_raw`.
Role: bounds the expression built from the canonical even local factor, with no parity premise.
The residue-ledger consumer assumes even parity when identifying this expression with the residue.
-/
theorem re_iteratedDeriv_two_llsPrimitiveLogEvenZeroRegularization_zero_div_two_le {N : ℕ}
    [NeZero N] (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ}
    (hx : 64 ≤ x) :
    (iteratedDeriv 2
            (dirichletLogEvenZeroRegularization
              x 1
              (dirichletEvenZeroLocalFactor χ))
            0 /
          2).re ≤
      (2 + Real.log x) * |primitiveBRe χ| +
          (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x -
        11 / 4 := by
  have hxpos : (0 : ℝ) < x := by linarith
  rw [re_iteratedDeriv_two_dirichletLogEvenZeroRegularization_zero_div_two_raw
      hN2 hGRH hprimitive hne hinv hquad hxpos]
  have hD :=
    neg_re_deriv_logDeriv_completedLFunction_zero_le
      hGRH hprimitive hne hinv hquad hN2
  have hE := llsPrimitiveLogEvenMainError_le_neg_eleven_fourths hx
  unfold Analysis.primitiveLogEvenMainError at hE
  have hlogx_nn : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
  nlinarith [hD, hE, mul_le_mul_of_nonneg_right hD hlogx_nn]

end PseudoPrime.LLS

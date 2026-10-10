/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveLogResidueClosedForms
public import PseudoPrime.LLS.PrimitiveLogMainErrorBounds

/-!
# Combined parity-common upper bound for the `s = 0` log-kernel residue

Substitutes the completed-side derivative bound
(`DirichletLFunction.neg_re_deriv_logDeriv_completedLFunction_zero_le_abs_BRe`
in `AnalyticNumberTheory/DirichletLFunction/PrimitiveFunctionalEquation.lean`)
and the numerical main-error bounds
(`PrimitiveLogMainErrorBounds.lean`) into the odd/even raw closed forms
(`PrimitiveLogResidueClosedForms.lean`), giving both parities the *same* upper bound
`(2 + log x)|Re B(χ)| + (1/2)(log N - log π) log x - 11/4`.
`PrimitiveLogResidueLedger.lean` uses these bounds after dispatching on parity.
-/

@[expose] public section

namespace PseudoPrime.LLS

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- Under GRH, a primitive nonprincipal character of modulus at least two and `x ≥ 64`
satisfies the displayed upper bound for the even-zero regularization coefficient.
The closed form combines the completed logarithmic derivative bound with the explicit
even main-error estimate `-11/4`. This supplies the even branch of the residue ledger;
the inequality itself does not require an evenness assumption. -/
theorem re_iteratedDeriv_two_llsPrimitiveLogEvenZeroRegularization_zero_div_two_le {N : ℕ}
    [NeZero N] (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hprimitive : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 64 ≤ x) :
    (iteratedDeriv 2 (dirichletLogEvenZeroRegularization x 1 (dirichletEvenZeroLocalFactor χ)) 0 /
          2).re ≤
      (2 + Real.log x) * |primitiveBRe χ| + (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x -
        11 / 4 := by
  rw [re_iteratedDeriv_two_dirichletLogEvenZeroRegularization_zero_div_two hN2 hGRH hprimitive hne
      hinv (show (0 : ℝ) < x from lt_of_lt_of_le (show (0 : ℝ) < 64 by norm_num only) hx)]
  have hD := neg_re_deriv_logDeriv_completedLFunction_zero_le_abs_BRe hGRH hprimitive hne hinv hN2
  have hE := llsPrimitiveLogEvenMainError_le_neg_eleven_fourths hx
  unfold Analysis.primitiveLogEvenMainError at hE
  have hsum := add_le_add hD hE
  calc
    -(deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0).re +
            |primitiveBRe χ| * Real.log x +
            (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x +
            Real.pi ^ 2 / 24 -
          (Real.eulerMascheroniConstant / 2) * Real.log x -
          (1 / 2) * (Real.log x) ^ 2 =
        (-(deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0).re +
            (Real.pi ^ 2 / 24 - (Real.eulerMascheroniConstant / 2) * Real.log x -
              (1 / 2) * (Real.log x) ^ 2)) +
          ((1 / 2) * (Real.log ↑N - Real.log Real.pi) * Real.log x +
            |primitiveBRe χ| * Real.log x) :=
      by ring
    _ ≤
        (2 * |primitiveBRe χ| + (-(11 / 4))) +
          ((1 / 2) * (Real.log ↑N - Real.log Real.pi) * Real.log x +
            |primitiveBRe χ| * Real.log x) :=
      by
      have h :=
        add_le_add hsum
          (le_refl
            ((1 / 2) * (Real.log ↑N - Real.log Real.pi) * Real.log x +
              |primitiveBRe χ| * Real.log x))
      exact h
    _ =
        (2 + Real.log x) * |primitiveBRe χ| +
            (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x -
          11 / 4 :=
      by ring

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For an odd primitive nonprincipal character under GRH and `x ≥ 64`, bound the real
derivative of the Mellin zero regularization by the displayed conductor and zero-mass terms.
The odd closed form, completed logarithmic derivative estimate, and odd main-error bound
give the constant `-11/4`. This is the odd branch of the logarithmic residue estimate. -/
theorem re_deriv_llsPrimitiveLogMellinZeroRegularization_zero_of_odd_le {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hprimitive : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hodd : χ.Odd) {x : ℝ} (hx : 64 ≤ x) :
    (deriv (dirichletLogMellinZeroRegularization x χ) 0).re ≤
      (2 + Real.log x) * |primitiveBRe χ| + (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x -
        11 / 4 := by
  rw [re_deriv_dirichletLogMellinZeroRegularization_zero_of_odd hN2 hGRH hprimitive hne hinv hodd
      (show (0 : ℝ) < x from lt_of_lt_of_le (show (0 : ℝ) < 64 by norm_num only) hx)]
  have hD := neg_re_deriv_logDeriv_completedLFunction_zero_le_abs_BRe hGRH hprimitive hne hinv hN2
  have hE := llsPrimitiveLogOddMainError_le_neg_eleven_fourths hx
  unfold Analysis.primitiveLogOddMainError at hE
  have hsum := add_le_add hD hE
  calc
    -(deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0).re +
            |primitiveBRe χ| * Real.log x +
            (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x +
            Real.pi ^ 2 / 8 -
          (Real.log 2 + Real.eulerMascheroniConstant / 2) * Real.log x =
        (-(deriv (logDeriv (DirichletCharacter.completedLFunction χ)) 0).re +
            (Real.pi ^ 2 / 8 - (Real.log 2 + Real.eulerMascheroniConstant / 2) * Real.log x)) +
          ((1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x +
            |primitiveBRe χ| * Real.log x) :=
      by ring
    _ ≤
        (2 * |primitiveBRe χ| + (-(11 / 4))) +
          ((1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x +
            |primitiveBRe χ| * Real.log x) :=
      by
      have h :=
        add_le_add hsum
          (le_refl
            ((1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x +
              |primitiveBRe χ| * Real.log x))
      exact h
    _ =
        (2 + Real.log x) * |primitiveBRe χ| +
            (1 / 2) * (Real.log N - Real.log Real.pi) * Real.log x -
          11 / 4 :=
      by ring

end PseudoPrime.LLS

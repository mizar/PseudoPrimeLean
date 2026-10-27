/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ParameterizedReciprocalWeightedBounds
public import PseudoPrime.Analysis.RetainedEvenReciprocalError

/-! # Parity-conditional even reciprocal bound with retained error -/

@[expose] public section

namespace PseudoPrime.LLS.Extensions

/-- Under GRH, an even primitive nonprincipal character has the reciprocal
weighted-sum upper bound with main error -179/200 for x at least 64.
Apply the parity-conditional contour limit with the certified even error.
This is a reusable replacement for the fixed -4/5 input at small scales. -/
theorem primitiveReciprocalRaw_even_le_neg_179_div_200 {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (heven : χ.Even) {x : ℝ} (hx : 64 ≤ x) :
    (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ).re ≤
      (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) - 179 / 200 -
        (1 - 1 / Real.sqrt x) ^ 2 * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| := by
  have hx1 : (1 : ℝ) < x := by linarith only [hx]
  have h :=
    primitiveReciprocalRaw_even_le_of_mainError hN2 hGRH hp hne (inv_ne_one.mpr hne) heven hx1
      (Analysis.primitiveReciprocalEvenMainError_le_neg_179_div_200 hx)
  linarith only [h]

end PseudoPrime.LLS.Extensions

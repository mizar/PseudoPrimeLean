/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.OrdinateTail
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroReciprocal100Brackets
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCombinedBudget100RH

/-! # Combined zero budget from ordinate brackets -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, 29 ordered positive zeros in the lower brackets and an upper
count bound of 58 give the combined zero budget with constant `1/25` for
`T ≥ 100`. The same count also supplies completeness and simplicity. -/
theorem combined_zero_of_brackets100 (hRH : RiemannHypothesis) (g : Fin 29 → ℝ)
    (hmono : StrictMono g) (hpos : ∀ i, 0 < g i) (hheight : ∀ i, g i ≤ 100)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0)
    (hcount : zeroCount 100 ≤ 58) (hbrackets : LowZero100LowerBounds g) {T : ℝ} (hT : 100 ≤ T) :
    zeroReciprocalSum T + T * ordinateTail T ≤
      ((Real.log (T / (2 * Real.pi))) ^ 2 + 2 * Real.log (T / (2 * Real.pi)) + 2) / (2 * Real.pi) +
            1 / 25 -
          (3 / 8 : ℝ) / T +
        1 / (15 * T ^ 2) := by
  obtain ⟨h100, hhead⟩ := head100_of_count hRH g hmono hpos hheight hzero hcount hbrackets
  exact combined_zero_budget100 hRH h100 hhead hT

end PseudoPrime.AnalyticNumberTheory.RiemannZeta

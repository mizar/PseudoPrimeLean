/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroReciprocal100Brackets
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.CriticalLineZeros

/-! # Reciprocal zero sums from critical-line sign intervals -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, 29 separated positive intervals below height 100, each with
opposite xi endpoint signs, give the reciprocal-sum estimate when the zero
count is at most 58 and their lower endpoints imply the numerical brackets.
The intermediate value theorem supplies the zero ordinates. -/
theorem reciprocal_sum_of_sign100 (hRH : RiemannHypothesis) (a b : Fin 29 → ℝ) (hpos : ∀ i, 0 ≤ a i)
    (hheight : ∀ i, b i ≤ 100) (hab : ∀ i, a i < b i) (hsep : ∀ i j, i < j → b i ≤ a j)
    (hsign :
      ∀ i,
        let f := fun t : ℝ ↦ (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
        (f (a i) < 0 ∧ 0 < f (b i)) ∨ (f (b i) < 0 ∧ 0 < f (a i)))
    (hbrackets : ∀ g : Fin 29 → ℝ, (∀ i, a i < g i ∧ g i < b i) → LowZero100LowerBounds g)
    (hcount : zeroCount 100 ≤ 58) {T : ℝ} (hT : 100 ≤ T) :
    zeroReciprocalSum T ≤ (Real.log (T / (2 * Real.pi))) ^ 2 / (2 * Real.pi) + 41 / 1000 := by
  obtain ⟨g, hmono, hg, hz⟩ := RiemannXi.critical_zeros_of_sign_intervals a b hab hsep hsign
  apply reciprocal_sum_of_count100 hRH g hmono ?_ ?_ hz hcount (hbrackets g hg) hT
  · intro i
    exact (hpos i).trans_lt (hg i).1
  · intro i
    exact (hg i).2.le.trans (hheight i)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta

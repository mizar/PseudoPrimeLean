/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroReciprocalIntegratedRH
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroReciprocal100Brackets
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.CriticalLineZeros

/-! # Integrated reciprocal-zero constant from finite ξ sign conditions -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, 29 ordered zeros in the lower brackets and the height-100
count bound yield the sharp integrated reciprocal-zero constant. -/
theorem zeroReciprocalConstant_sharp_of_brackets (hRH : RiemannHypothesis) (g : Fin 29 → ℝ)
    (hmono : StrictMono g) (hpos : ∀ i, 0 < g i) (hheight : ∀ i, g i ≤ 100)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0)
    (hcount : zeroCount 100 ≤ 58) (hbrackets : LowZero100LowerBounds g) :
    zeroReciprocalConstant ≤ -(317 / 10000 : ℝ) := by
  obtain ⟨hc, hs⟩ := head100_of_count hRH g hmono hpos hheight hzero hcount hbrackets
  exact zeroReciprocalConstant_le_sharp hRH hc hs

/-- Under RH, separated ξ sign changes, their lower brackets, and a count
bound at height 100 yield the sharp integrated reciprocal-zero constant.
These finite sign and count conditions remain explicit hypotheses. -/
theorem zeroReciprocalConstant_sharp_of_signs (hRH : RiemannHypothesis) (a b : Fin 29 → ℝ)
    (hpos : ∀ i, 0 ≤ a i) (hheight : ∀ i, b i ≤ 100) (hab : ∀ i, a i < b i)
    (hsep : ∀ i j, i < j → b i ≤ a j)
    (hsign :
      ∀ i,
        let f := fun t : ℝ ↦ (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
        (f (a i) < 0 ∧ 0 < f (b i)) ∨ (f (b i) < 0 ∧ 0 < f (a i)))
    (hbrackets : ∀ g : Fin 29 → ℝ, (∀ i, a i < g i ∧ g i < b i) → LowZero100LowerBounds g)
    (hcount : zeroCount 100 ≤ 58) : zeroReciprocalConstant ≤ -(317 / 10000 : ℝ) := by
  obtain ⟨g, hmono, hg, hz⟩ := RiemannXi.critical_zeros_of_sign_intervals a b hab hsep hsign
  apply zeroReciprocalConstant_sharp_of_brackets hRH g hmono ?_ ?_ hz hcount (hbrackets g hg)
  · intro i
    exact (hpos i).trans_lt (hg i).1
  · intro i
    exact (hg i).2.le.trans (hheight i)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta

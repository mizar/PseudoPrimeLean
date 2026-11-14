/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiMargin20RH
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.CriticalLineZeros

/-! # Conditional height-20 ψ margin from ξ sign intervals -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, 29 separated ξ sign-change intervals through height 100, a
count upper bound of 58, and their lower-bracket implication yield the
`1/150` ψ margin for `log x ≥ 20`. The intermediate value theorem supplies
the required critical-line zeros. -/
theorem psi_lee_nosal_margin20_of_signs (hRH : RiemannHypothesis) (a b : Fin 29 → ℝ)
    (hpos : ∀ i, 0 ≤ a i) (hheight : ∀ i, b i ≤ 100) (hab : ∀ i, a i < b i)
    (hsep : ∀ i j, i < j → b i ≤ a j)
    (hsign :
      ∀ i,
        let f := fun t : ℝ ↦ (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
        (f (a i) < 0 ∧ 0 < f (b i)) ∨ (f (b i) < 0 ∧ 0 < f (a i)))
    (hbrackets : ∀ g : Fin 29 → ℝ, (∀ i, a i < g i ∧ g i < b i) → LowZero100LowerBounds g)
    (hcount : zeroCount 100 ≤ 58) {x : ℝ} (hx : 0 < x) (hL : (20 : ℝ) ≤ Real.log x) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x *
        (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) - 1 / 150) := by
  obtain ⟨g, hmono, hg, hz⟩ := RiemannXi.critical_zeros_of_sign_intervals a b hab hsep hsign
  apply psi_lee_nosal_margin20_of_brackets hRH g hmono ?_ ?_ hz hcount (hbrackets g hg) hx hL
  · intro i
    exact (hpos i).trans_lt (hg i).1
  · intro i
    exact (hg i).2.le.trans (hheight i)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta

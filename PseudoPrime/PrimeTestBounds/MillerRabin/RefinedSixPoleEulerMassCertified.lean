/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerTotal

/-! Three-character zero mass with the certified Euler bound. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH and the three character hypotheses, use the certified Euler total in the mass bound. -/
theorem refined_three_mass_even_certified {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hRH : RiemannHypothesis) (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q)
    (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hRA : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis a)
    (hRB : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis b)
    (hRC : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis c) (hpA : a.IsPrimitive)
    (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1) (hnC : c ≠ 1)
    (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even) (heC : c.Even)
    {X : ℝ} (hX : 1000 ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    sixMass a + sixMass b + sixMass c <
      (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) -
        (6366 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  exact
    refined_three_mass_even_prefix1000 a b c hP hQ hR hRA hRB hRC hpA hpB hpC hnA hnB hnC hiA hiB
      hiC heA heB heC hX ht hA hB hC (refined_euler_total_upper hRH)

end PseudoPrime.PrimeTestBounds.MillerRabin

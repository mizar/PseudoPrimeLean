/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerPrefix1000

/-! # Refined three-character mass with the certified Euler prefix -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxRecDepth 100000 in
/-- Under individual RH, the three even primitive characters satisfy the
refined zero-mass bound with correction `6.366` when they equal one at primes
through `X ≥ 1000`. The exact finite Euler certificate and the Gamma bound
remove both numerical hypotheses; only the universal Euler-total bound remains
assumed. This is the input for the high-range witness inequality. -/
theorem refined_three_mass_even_prefix1000 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hRA : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis a)
    (hRB : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis b)
    (hRC : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis c) (hpA : a.IsPrimitive)
    (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1) (hnC : c ≠ 1)
    (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even) (heC : c.Even)
    {X : ℝ} (hX : 1000 ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1)
    (hE :
      (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) <
        (53 / 25 : ℝ) * (27 / 25 : ℝ) ^ 5) :
    sixMass a + sixMass b + sixMass c <
      (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) -
        (6366 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  apply
    refined_three_mass_even_numeric a b c hP hQ hR hRA hRB hRC hpA hpB hpC hnA hnB hnC hiA hiB hiC
      heA heB heC refinedEulerPrefixSet ?_ ht hA hB hC hE refined_euler_prefix_1000_lower
  intro k hk
  have hk' : (k : ℝ) ≤ 1000 := by exact_mod_cast refinedEulerPrefixSet_le k hk
  exact hk'.trans hX

end PseudoPrime.PrimeTestBounds.MillerRabin

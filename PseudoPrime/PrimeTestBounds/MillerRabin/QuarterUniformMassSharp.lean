/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformMass
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerTotalSharp

/-! # Zero-mass estimate with an explicit Euler tail -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH and prime-level triviality, three even primitive characters
have a zero-mass upper bound retaining the Euler tail. The lower bound for
the total Euler mass gives the normalized constant `3117/400`. -/
theorem quarter_uniform_mass_sharp {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hRH : RiemannHypothesis) (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q)
    (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hRA : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis a)
    (hRB : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis b)
    (hRC : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis c) (hpA : a.IsPrimitive)
    (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1) (hnC : c ≠ 1)
    (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even) (heC : c.Even)
    {X : ℝ} (hX : 0 ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    sixMass a + sixMass b + sixMass c <
      (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) +
        -(3117 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 +
        4 *
          ((∑' n : ℕ, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) -
            ∑ k ∈ Finset.Ioc 0 ⌊X⌋₊,
              ArithmeticFunction.vonMangoldt k * refinedSixEulerWeight k) := by
  have hS : ∀ k ∈ Finset.Ioc 0 ⌊X⌋₊, (k : ℝ) ≤ X := by
    intro k hk
    exact (Nat.cast_le.mpr (Finset.mem_Ioc.mp hk).2).trans (Nat.floor_le hX)
  have h :=
    refined_three_mass_of_prime_one a b c hP hQ hR hRA hRB hRC hpA hpB hpC hnA hnB hnC hiA hiB hiC
      (Finset.Ioc 0 ⌊X⌋₊) hS ht hA hB hC
  have hΓA := refined_gamma_even_precise heA
  have hΓB := refined_gamma_even_precise heB
  have hΓC := refined_gamma_even_precise heC
  have hE := quarter_euler_total_lower_sharp hRH
  linarith only [h, hΓA, hΓB, hΓC, hE]

end PseudoPrime.PrimeTestBounds.MillerRabin

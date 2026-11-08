/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerMassCertified

/-! # Finite Euler prefix at the first uniform-triple cutoff -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The certified prime-power rows at or below 252. This subset is available
at every cutoff in the paper's finite uniform-triple range. -/
def target028EulerPrefix252 : Finset ℕ :=
  refinedEulerPrefixSet.filter (fun n ↦ n ≤ 252)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Kernel reduction evaluates the exact rational prefix of the existing certificate.
/-- The rational Euler prefix through 252 exceeds the normalized lower bound
`39/25`. Each row is taken from the previously checked prime-power table. -/
theorem target028_euler_prefix252_rational :
    (39 / 25 : ℚ) * (27 / 25 : ℚ) ^ 5 <
      ∑ n ∈ target028EulerPrefix252, refinedEulerAtomLower n (refinedEulerData n) := by
  decide +kernel

-- The filtered 193-row prefix is reduced when applying its checked row evidence.
set_option maxRecDepth 1000000 in
/-- The actual Euler sum through 252 exceeds `39/25` times the kernel
normalization. The checked rational prefix is transferred term by term. -/
theorem target028_euler_prefix252_lower :
    (39 / 25 : ℝ) * (27 / 25 : ℝ) ^ 5 <
      ∑ n ∈ target028EulerPrefix252,
        ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
  have hc :=
    refined_euler_prefix_sound target028EulerPrefix252 refinedEulerData
      (fun n hn ↦ refined_euler_prefix_check n (Finset.mem_filter.mp hn).1)
  have hl :
    ((39 / 25 : ℚ) * (27 / 25 : ℚ) ^ 5 : ℝ) <
      ((∑ n ∈ target028EulerPrefix252, refinedEulerAtomLower n (refinedEulerData n) : ℚ) : ℝ) := by
    exact_mod_cast target028_euler_prefix252_rational
  norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] at hl ⊢
  exact hl.trans_le hc

-- Membership reduction traverses the existing 193-row prime-power prefix.
set_option maxRecDepth 1000000 in
/-- Every index in the selected prefix is at most 252. -/
theorem target028_euler_prefix252_le {n : ℕ} (hn : n ∈ target028EulerPrefix252) : n ≤ 252 := by
  exact (Finset.mem_filter.mp hn).2

-- Applying the finite-prefix theorem reduces the filtered 193-row table.
set_option maxRecDepth 1000000 in
/-- Under RH and the three even-character prefix conditions through a cutoff
at least 252, their total zero mass has correction `547/100`. The certified
252-prefix, the universal Euler upper bound, and the even Gamma bound supply
the three terms in the general zero-mass comparison. -/
theorem target028_three_mass_prefix252 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hRH : RiemannHypothesis) (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q)
    (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hRA : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis a)
    (hRB : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis b)
    (hRC : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis c) (hpA : a.IsPrimitive)
    (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1) (hnC : c ≠ 1)
    (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even) (heC : c.Even)
    {X : ℝ} (hX : 252 ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    sixMass a + sixMass b + sixMass c <
      (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) -
        (547 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  have hS : ∀ k ∈ target028EulerPrefix252, (k : ℝ) ≤ X := by
    intro k hk
    exact (Nat.cast_le.mpr (target028_euler_prefix252_le hk)).trans hX
  have h :=
    refined_three_mass_of_prime_one a b c hP hQ hR hRA hRB hRC hpA hpB hpC hnA hnB hnC hiA hiB hiC
      target028EulerPrefix252 hS ht hA hB hC
  have hΓA := refined_gamma_even_upper heA
  have hΓB := refined_gamma_even_upper heB
  have hΓC := refined_gamma_even_upper heC
  have hE := refined_euler_total_upper hRH
  have hpref := target028_euler_prefix252_lower
  linarith only [h, hΓA, hΓB, hΓC, hE, hpref]

end PseudoPrime.PrimeTestBounds.MillerRabin

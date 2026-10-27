/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaActualConductorBudget

/-! # Square and dyadic conductor absorption at an arbitrary scale -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: odd square decomposition, compatible conductor and dyadic branch, and x >= 20000.
Claim: arbitrary square-prime prefixes and the dyadic cost fit mu log(4n)+3/4.
Proof: apply the established odd or even conductor estimate at the actual scale.
Role: remove the prescribed logarithmic profile from joint local comparisons. -/
theorem gamma_actual_square_dyadic_cost_le_of_scale {n d m f : ℕ} (hn : n = d * m ^ 2)
    (hodd : Odd n) (hd : 0 < d) (hm : 0 < m) (hf : 0 < f) (hdf : d ∣ f) (hfd : f ≤ 4 * d)
    (χ : DirichletCharacter ℂ f) (hbranch : (f = d ∧ (χ 2 = 1 ∨ χ 2 = -1)) ∨ Even f) (S : Finset ℕ)
    (hS : S ⊆ n.primeFactors) (hχ : ∀ p ∈ S, χ p = -1) (K : ℕ → Finset ℕ) (K2 : Finset ℕ) {x : ℝ}
    (hx : 20000 ≤ x) :
    (11783423 / 25000000 : ℝ) * Real.log f + (∑ p ∈ S, gammaActualPrimeLocalCost χ p (K p) x) +
        gammaActualPrimeLocalCost χ 2 K2 x ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) + 3 / 4 := by
  rcases hbranch with ⟨rfl, h2⟩ | he
  · have h :=
      gamma_actual_odd_conductor_square_dyadic_cost_le hn hodd hd hm S hS χ hχ h2 K K2
        (by linarith only [hx])
    linarith only [h]
  · exact
      gamma_actual_even_conductor_square_dyadic_cost_le hn hodd hd hm hf hdf hfd he S hS χ hχ K K2
        hx

end PseudoPrime.Analysis

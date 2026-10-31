/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.ResidueSubgroup
public import PseudoPrime.LLS.PaperStatements.RationalLogShiftWitness
public import PseudoPrime.LLS.PaperStatements.GammaUniformRationalProfileBounds

/-! # A rational coefficient-0.796 shifted profile

The rational triple (199/250,0,117) has the same decimal entrance 10^15188
as the positive coefficient-0.8 profile. The proof controls the ambient-scale
excess as well as the actual nonunit loss, uniformly over every proper subgroup.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under GRH, q ≥ 10^15188 and χ nonprincipal, a coprime prime with χ(p) ≠ 1
exists through (199/250)(log q+117)². Apply the uniform subgroup cutoff to the unit kernel.
This is the general-character version with the same expression and starting value. -/
theorem exists_prime_character_ne_one_le_gamma_199_div_250_plus_117_15188 {q : ℕ}
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hq : 10 ^ 15188 ≤ q) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ χ p ≠ 1 ∧ (p : ℝ) ≤ (199 / 250 : ℝ) * (Real.log q + 117) ^ 2 := by
  exact
    exists_prime_character_ne_one_of_uniform_subgroup_cutoff χ hne
      (fun H hH ↦
        PaperStatements.exists_prime_outside_le_gamma_199_div_250_plus_117_15188 H hH hGRH hq)

/-- Under GRH, q ≥ 10^15188 and H proper, the least coprime outside prime is
at most (199/250)(log q+117)². Minimize the bounded outside-prime witness.
Minimality is among all eligible primes and retains the same starting value. -/
theorem exists_least_prime_outside_le_gamma_199_div_250_plus_117_15188 {q : ℕ}
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hq : 10 ^ 15188 ≤ q) :
    ∃ p : ℕ,
      PrimeOutsideSubgroup q H p ∧
        (p : ℝ) ≤ (199 / 250 : ℝ) * (Real.log q + 117) ^ 2 ∧
        ∀ r, PrimeOutsideSubgroup q H r → p ≤ r := by
  exact
    exists_least_prime_outside_of_subgroup_cutoff H
      (PaperStatements.exists_prime_outside_le_gamma_199_div_250_plus_117_15188 H hH hGRH hq)

end PseudoPrime.LLS

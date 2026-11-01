/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.ResidueSubgroup
public import PseudoPrime.LLS.PaperStatements.GammaUniformSmallScaleBounds
public import PseudoPrime.LLS.GammaUniformRationalProfileBounds
public import PseudoPrime.LLS.PaperStatements.GammaUniformRationalProfileBounds
public import PseudoPrime.LLS.RefinedTheorem11S1Subgroup
public import PseudoPrime.LLS.PaperStatements.GammaUniformStarting3000

/-! # Rational coefficient-0.796 witnesses from modulus 3000 -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under GRH, q ≥ 3000 and χ nonprincipal, a coprime prime with χ(p) ≠ 1
exists through (199/250)(log q+216)². Apply the uniform subgroup cutoff to its unit kernel.
This is the general-character interface for the starting value 3000. -/
theorem exists_prime_neOne_gamma216_3000_GRH {q : ℕ} (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hq : 3000 ≤ q) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ χ p ≠ 1 ∧ (p : ℝ) ≤ (199 / 250 : ℝ) * (Real.log q + 216) ^ 2 := by
  exact
    exists_prime_neOne_uniformSubgroup χ hne
      (fun H hH ↦ PaperStatements.exists_primeOutside_199_250_216_from3000_GRH H hH hGRH hq)

/-- Under GRH, q ≥ 3000 and H proper, the least coprime outside prime is
at most (199/250)(log q+216)². Minimize the bounded subgroup witness.
Minimality is among all eligible primes, with the same starting value and formula. -/
theorem exists_least_outside_gamma216_3000_GRH {q : ℕ} (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hq : 3000 ≤ q) :
    ∃ p : ℕ,
      PrimeOutsideSubgroup q H p ∧
        (p : ℝ) ≤ (199 / 250 : ℝ) * (Real.log q + 216) ^ 2 ∧
        ∀ r, PrimeOutsideSubgroup q H r → p ≤ r := by
  exact
    exists_least_prime_outside_of_subgroup_cutoff H
      (PaperStatements.exists_primeOutside_199_250_216_from3000_GRH H hH hGRH hq)

end PseudoPrime.LLS

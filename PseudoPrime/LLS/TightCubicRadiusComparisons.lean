/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TightCubicConductorBounds
public import PseudoPrime.LLS.PaperStatements.TightCubicConductorBounds
public import PseudoPrime.LLS.PaperStatements.TightCubicRadiusComparisons

/-! # Uniform exclusions and comparisons for tight cubic radii -/

@[expose] public section

namespace PseudoPrime.LLS

/-- A nonprincipal character under GRH has a unit-prime non-one witness
below the tight cubic conductor radius. Apply the sensitive theorem with
the uniform prime-factor cost of the original level. -/
theorem exists_prime_neOne_cubicConductor_GRH {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {G : ℝ}
    (hlog : Real.log χ.conductor ≤ G) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (PaperStatements.tightCubicConductorRadius G q) ^ 2 ∧ ¬p ∣ q ∧ χ p ≠ 1 := by
  exact
    exists_prime_neOne_cubicSensitive_GRH χ hχ hGRH hlog
      (AnalyticNumberTheory.Arithmetic.characterExclusionCost_le_twice χ.primitiveCharacter q)

/-- A nonprincipal character trivial on H supplies a unit prime outside H
within the tight cubic conductor radius under GRH. Transfer its non-one
value to nonmembership in H. The conductor envelope has no entrance threshold. -/
theorem exists_prime_outside_cubicConductor_GRH {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ht : ∀ u : (ZMod q)ˣ, u ∈ H → χ (u : ZMod q) = 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {G : ℝ}
    (hlog : Real.log χ.conductor ≤ G) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧
        (p : ℝ) ≤ (PaperStatements.tightCubicConductorRadius G q) ^ 2 ∧
        ¬∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q) := by
  obtain ⟨p, hp, hb, hd, hv⟩ := exists_prime_neOne_cubicConductor_GRH χ hχ hGRH hlog
  refine ⟨p, hp, hd, hb, ?_⟩
  rintro ⟨u, hu, he⟩
  exact hv (he ▸ ht u hu)

end PseudoPrime.LLS

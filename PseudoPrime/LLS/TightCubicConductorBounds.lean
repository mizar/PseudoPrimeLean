/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.CubicSquareFactorBounds
public import PseudoPrime.LLS.PaperStatements.TightCubicConductorBounds

/-! # Tight cubic budgets and conductor radii with constants 63/2 and 28 -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under GRH, a nonprincipal character has a prime non-one value outside its
level below the tight cubic radius squared. Transfer primitive character
values on units; the inputs are conductor and sensitive-cost envelopes. -/
theorem exists_prime_ne_one_le_tight_cubic_sensitive_radius {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {G E : ℝ}
    (hlog : Real.log χ.conductor ≤ G)
    (hcost : AnalyticNumberTheory.Arithmetic.characterExclusionCost χ.primitiveCharacter q ≤ E) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (PaperStatements.tightCubicExclusionRadius G E) ^ 2 ∧ ¬p ∣ q ∧ χ p ≠ 1 := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hc := NumberTheory.three_le_conductor_of_ne_one χ hχ
  have hn := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hχ
  obtain ⟨p, hp, hb, hd, hv⟩ :=
    PaperStatements.exists_prime_outside_le_tight_cubic_exclusion_radius χ.primitiveCharacter
      (le_trans (by decide : 2 ≤ 3) hc) (NeZero.ne q) hGRH χ.primitiveCharacter_isPrimitive hn hlog
      hcost
  have he := χ.primitiveCharacter_apply_of_isCoprime (hp.coprime_iff_not_dvd.mpr hd).isCoprime
  simp only [Int.cast_natCast] at he
  exact ⟨p, hp, hb, hd, fun h ↦ hv (he.trans h)⟩

end PseudoPrime.LLS

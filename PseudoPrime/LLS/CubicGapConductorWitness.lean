/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ExcludedCharacterDefect
public import PseudoPrime.LLS.PaperStatements.CubicGapRationalBounds
public import PseudoPrime.LLS.PaperStatements.ReciprocalGapAmbientArithmetic
public import PseudoPrime.LLS.SelectedReciprocalConductorBounds
public import PseudoPrime.LLS.PaperStatements.SelectedReciprocalConductorBounds
public import PseudoPrime.LLS.PaperStatements.CubicGapConductorWitness

/-! # Cubic-gap conductor bounds with arbitrary prime exclusions -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under GRH, a nonprincipal character has a unit-prime non-one witness below
the cubic radius for any envelope of its conductor logarithm. Apply the primitive
extraction with excluded level q and transfer character values on units. -/
theorem exists_prime_ne_one_le_cubic_conductor_radius {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {G : ℝ}
    (hlog : Real.log χ.conductor ≤ G) :
    ∃ p : ℕ,
      p.Prime ∧ (p : ℝ) ≤ (PaperStatements.cubicConductorRadius G q) ^ 2 ∧ ¬p ∣ q ∧ χ p ≠ 1 := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hc := NumberTheory.three_le_conductor_of_ne_one χ hχ
  have hn := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hχ
  obtain ⟨p, hp, hb, hd, hv⟩ :=
    PaperStatements.exists_prime_outside_le_cubicConductorRadius_sq χ.primitiveCharacter
      (le_trans (by decide : 2 ≤ 3) hc) (NeZero.ne q) hGRH χ.primitiveCharacter_isPrimitive hn hlog
  have he := χ.primitiveCharacter_apply_of_isCoprime (hp.coprime_iff_not_dvd.mpr hd).isCoprime
  simp only [Int.cast_natCast] at he
  exact ⟨p, hp, hb, hd, fun h ↦ hv (he.trans h)⟩

/-- A nonprincipal character trivial on H gives a unit prime outside H under GRH,
with the cubic conductor radius. Transfer the non-one value to nonmembership.
No lower threshold on the conductor envelope is required. -/
theorem exists_prime_outside_le_cubic_conductor_radius {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ht : ∀ u : (ZMod q)ˣ, u ∈ H → χ (u : ZMod q) = 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {G : ℝ}
    (hlog : Real.log χ.conductor ≤ G) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧
        (p : ℝ) ≤ (PaperStatements.cubicConductorRadius G q) ^ 2 ∧
        ¬∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q) := by
  obtain ⟨p, hp, hb, hd, hv⟩ := exists_prime_ne_one_le_cubic_conductor_radius χ hχ hGRH hlog
  refine ⟨p, hp, hd, hb, ?_⟩
  rintro ⟨u, hu, he⟩
  exact hv (he ▸ ht u hu)

end PseudoPrime.LLS

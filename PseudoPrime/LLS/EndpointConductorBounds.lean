/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.AffineConductorWitnessBounds
public import PseudoPrime.LLS.PaperStatements.AffineConductorWitnessBounds
public import PseudoPrime.LLS.PaperStatements.EndpointConductorBounds

/-! # Separate endpoint caps and conductor-sensitive prime witnesses -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under GRH, a nonprincipal character at nonzero level q has a unit-prime
non-one witness below the displayed root bound in its primitive conductor and
ambient exclusion cost. Primitivize and transfer the unit value back to χ.
This is the original-level interface for the smaller-scale conductor estimate. -/
theorem exists_prime_ne_one_le_endpoint_conductor_root {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤
          (((287 / 80 : ℝ) * Real.log χ.conductor + 4327 / 80 +
              Real.sqrt
                (((287 / 80 : ℝ) * Real.log χ.conductor + 4327 / 80) ^ 2 +
                  (14 / 5 : ℝ) * (∑ r ∈ q.primeFactors, Real.log r))) ^
            2) ∧
        ¬p ∣ q ∧ χ p ≠ 1 := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hc := NumberTheory.three_le_conductor_of_ne_one χ hχ
  obtain ⟨p, hp, hb, hd, hv⟩ :=
    PaperStatements.exists_prime_ne_one_le_endpoint_conductor_root χ.primitiveCharacter hc
      χ.primitiveCharacter_isPrimitive hGRH (NeZero.ne q)
  have he := χ.primitiveCharacter_apply_of_isCoprime (hp.coprime_iff_not_dvd.mpr hd).isCoprime
  simp only [Int.cast_natCast] at he
  exact ⟨p, hp, hb, hd, fun h ↦ hv (he.trans h)⟩

/-- Under GRH, a nonprincipal character trivial on a subgroup supplies a
unit-prime outside its image below the root conductor budget. Apply the character
witness and contradict triviality on a proposed subgroup unit.
This retains the chosen character's conductor in the subgroup conclusion. -/
theorem exists_prime_outside_le_endpoint_character_conductor {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (ht : ∀ u : (ZMod q)ˣ, u ∈ H → χ (u : ZMod q) = 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧
        (p : ℝ) ≤
          (((287 / 80 : ℝ) * Real.log χ.conductor + 4327 / 80 +
              Real.sqrt
                (((287 / 80 : ℝ) * Real.log χ.conductor + 4327 / 80) ^ 2 +
                  (14 / 5 : ℝ) * (∑ r ∈ q.primeFactors, Real.log r))) ^
            2) ∧
        ¬∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q) := by
  obtain ⟨p, hp, hb, hd, hv⟩ := exists_prime_ne_one_le_endpoint_conductor_root χ hχ hGRH
  refine ⟨p, hp, hd, hb, ?_⟩
  rintro ⟨u, hu, he⟩
  exact hv (he ▸ ht u hu)

end PseudoPrime.LLS

/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.EndpointConductorBounds
public import PseudoPrime.LLS.PaperStatements.EndpointConductorBounds
public import PseudoPrime.NumberTheory.DirichletCharacterParity
public import PseudoPrime.LLS.Extensions.RetainedEvenReciprocalBounds
public import PseudoPrime.Analysis.PrecisePiLogBound
public import PseudoPrime.LLS.PaperStatements.DirectHadamardConductorBounds

/-! # Direct Hadamard bounds from the real reciprocal formula -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under GRH, a nonprincipal character at nonzero level q has a unit-prime
non-one witness below the direct Hadamard root bound in its primitive conductor.
Apply the primitive theorem with exclusion q and transfer the value on units. -/
theorem exists_prime_ne_one_le_direct_conductor_root {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤
          (((2429 / 720 : ℝ) * Real.log χ.conductor + 19171 / 400 +
              Real.sqrt
                (((2429 / 720 : ℝ) * Real.log χ.conductor + 19171 / 400) ^ 2 +
                  (14 / 5 : ℝ) * (∑ r ∈ q.primeFactors, Real.log r))) ^
            2) ∧
        ¬p ∣ q ∧ χ p ≠ 1 := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hc := NumberTheory.three_le_conductor_of_ne_one χ hχ
  obtain ⟨p, hp, hb, hd, hv⟩ :=
    PaperStatements.exists_prime_ne_one_le_direct_conductor_root χ.primitiveCharacter hc
      χ.primitiveCharacter_isPrimitive hGRH (NeZero.ne q)
  have he := χ.primitiveCharacter_apply_of_isCoprime (hp.coprime_iff_not_dvd.mpr hd).isCoprime
  simp only [Int.cast_natCast] at he
  exact ⟨p, hp, hb, hd, fun h ↦ hv (he.trans h)⟩

/-- Under GRH, a nonprincipal character trivial on a subgroup supplies a
unit-prime outside its image below the direct Hadamard root bound.
Transfer the proved character nontriviality to exclusion from the subgroup image. -/
theorem exists_prime_outside_le_direct_character_conductor {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (ht : ∀ u : (ZMod q)ˣ, u ∈ H → χ (u : ZMod q) = 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧
        (p : ℝ) ≤
          (((2429 / 720 : ℝ) * Real.log χ.conductor + 19171 / 400 +
              Real.sqrt
                (((2429 / 720 : ℝ) * Real.log χ.conductor + 19171 / 400) ^ 2 +
                  (14 / 5 : ℝ) * (∑ r ∈ q.primeFactors, Real.log r))) ^
            2) ∧
        ¬∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q) := by
  obtain ⟨p, hp, hb, hd, hv⟩ := exists_prime_ne_one_le_direct_conductor_root χ hχ hGRH
  refine ⟨p, hp, hd, hb, ?_⟩
  rintro ⟨u, hu, he⟩
  exact hv (he ▸ ht u hu)

/-- Under GRH, a nonprincipal even character at nonzero level q has a
unit-prime non-one witness below the parity-refined root bound in its conductor.
Preserve evenness through primitivization and transfer the unit value. -/
theorem exists_prime_ne_one_le_even_direct_conductor_root {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (heven : χ.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤
          (((2429 / 720 : ℝ) * Real.log χ.conductor + 17939 / 400 +
              Real.sqrt
                (((2429 / 720 : ℝ) * Real.log χ.conductor + 17939 / 400) ^ 2 +
                  (14 / 5 : ℝ) * (∑ r ∈ q.primeFactors, Real.log r))) ^
            2) ∧
        ¬p ∣ q ∧ χ p ≠ 1 := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hc := NumberTheory.three_le_conductor_of_ne_one χ hχ
  obtain ⟨p, hp, hb, hd, hv⟩ :=
    PaperStatements.exists_prime_ne_one_le_even_direct_conductor_root χ.primitiveCharacter hc
      χ.primitiveCharacter_isPrimitive ((NumberTheory.primitiveCharacter_even_iff χ).mpr heven) hGRH
      (NeZero.ne q)
  have he := χ.primitiveCharacter_apply_of_isCoprime (hp.coprime_iff_not_dvd.mpr hd).isCoprime
  simp only [Int.cast_natCast] at he
  exact ⟨p, hp, hb, hd, fun h ↦ hv (he.trans h)⟩

end PseudoPrime.LLS

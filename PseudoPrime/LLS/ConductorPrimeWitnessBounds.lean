/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ConductorPrimeExclusionBounds
public import PseudoPrime.LLS.Theorem11S2
public import PseudoPrime.NumberTheory.DirichletCharacterSmallLevels

/-! # Original-level character witnesses retaining primitive conductor costs -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under GRH, a nonprincipal character at nonzero level q has a unit-prime
witness bounded by a square in its primitive conductor and a linear sum over
excluded prime logarithms. Apply the primitive bound with excluded modulus q,
then transfer its value on coprime inputs back to the original character. -/
theorem exists_prime_ne_one_le_conductor_prime_budget {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤
          8 * (12 * Real.log χ.conductor + 200) ^ 2 + 16 * (∑ r ∈ q.primeFactors, Real.log r) ∧
        ¬p ∣ q ∧ χ p ≠ 1 := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hc := NumberTheory.three_le_conductor_of_ne_one χ hχ
  obtain ⟨p, hp, hb, hd, hv⟩ :=
    PaperStatements.exists_prime_ne_one_le_conductor_exclusion χ.primitiveCharacter hc
      χ.primitiveCharacter_isPrimitive hGRH (NeZero.ne q)
  have he := χ.primitiveCharacter_apply_of_isCoprime (hp.coprime_iff_not_dvd.mpr hd).isCoprime
  simp only [Int.cast_natCast] at he
  exact ⟨p, hp, hb, hd, fun h ↦ hv (he.trans h)⟩

/-- Under GRH, a nonprincipal character trivial on a unit subgroup supplies
a unit-prime outside that subgroup, with its own primitive conductor retained
in the bound and the ambient radical cost linear. Transfer nontriviality of
the character value to exclusion from the subgroup image. -/
theorem exists_prime_outside_le_character_conductor {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ht : ∀ u : (ZMod q)ˣ, u ∈ H → χ (u : ZMod q) = 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧
        (p : ℝ) ≤
          8 * (12 * Real.log χ.conductor + 200) ^ 2 + 16 * (∑ r ∈ q.primeFactors, Real.log r) ∧
        ¬∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q) := by
  obtain ⟨p, hp, hb, hd, hv⟩ := exists_prime_ne_one_le_conductor_prime_budget χ hχ hGRH
  refine ⟨p, hp, hd, hb, ?_⟩
  rintro ⟨u, hu, he⟩
  exact hv (he ▸ ht u hu)

end PseudoPrime.LLS

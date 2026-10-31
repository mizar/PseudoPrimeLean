/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.DirectHadamardConductorBounds
public import PseudoPrime.LLS.PaperStatements.DirectHadamardConductorBounds
public import PseudoPrime.LLS.PaperStatements.VariableReciprocalConductorBounds

/-! # Variable reciprocal cutoffs for conductor-sensitive witness bounds -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under GRH for any nonprincipal χ of nonzero level q and cutoff x ≥ 64,
a unit-prime non-one witness lies below the variable bound in its conductor.
Exclude the original level and transfer the primitive value on units. -/
theorem exists_prime_ne_one_le_variable_reciprocal_root {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 64 ≤ x) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ PaperStatements.variableReciprocalWitnessBound χ.conductor q x (1 / 4) (29 / 10) ∧
        ¬p ∣ q ∧ χ p ≠ 1 := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hc := NumberTheory.three_le_conductor_of_ne_one χ hχ
  obtain ⟨p, hp, hb, hd, hv⟩ :=
    PaperStatements.exists_prime_ne_one_le_variable_reciprocal_root χ.primitiveCharacter hc
      χ.primitiveCharacter_isPrimitive hGRH (NeZero.ne q) hx
  have he := χ.primitiveCharacter_apply_of_isCoprime (hp.coprime_iff_not_dvd.mpr hd).isCoprime
  simp only [Int.cast_natCast] at he
  exact ⟨p, hp, hb, hd, fun h ↦ hv (he.trans h)⟩

/-- Under GRH for any nonprincipal even χ of nonzero level q and x ≥ 64,
a unit-prime non-one witness lies below the variable even conductor bound.
Preserve evenness under primitivization and transfer the value on units. -/
theorem exists_prime_ne_one_le_even_variable_reciprocal_root {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (heven : χ.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 64 ≤ x) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤
          PaperStatements.variableReciprocalWitnessBound χ.conductor q x (179 / 200) (21 / 10) ∧
        ¬p ∣ q ∧ χ p ≠ 1 := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hc := NumberTheory.three_le_conductor_of_ne_one χ hχ
  obtain ⟨p, hp, hb, hd, hv⟩ :=
    PaperStatements.exists_prime_ne_one_le_even_variable_reciprocal_root χ.primitiveCharacter hc
      χ.primitiveCharacter_isPrimitive ((NumberTheory.primitiveCharacter_even_iff χ).mpr heven) hGRH
      (NeZero.ne q) hx
  have he := χ.primitiveCharacter_apply_of_isCoprime (hp.coprime_iff_not_dvd.mpr hd).isCoprime
  simp only [Int.cast_natCast] at he
  exact ⟨p, hp, hb, hd, fun h ↦ hv (he.trans h)⟩

end PseudoPrime.LLS

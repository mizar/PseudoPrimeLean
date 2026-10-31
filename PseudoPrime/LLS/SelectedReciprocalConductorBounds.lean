/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.AdaptiveReciprocalConductorBounds
public import PseudoPrime.LLS.PaperStatements.AdaptiveReciprocalConductorBounds
public import PseudoPrime.LLS.PaperStatements.SelectedReciprocalConductorBounds

/-! # Selected half-conductor reciprocal cutoffs and explicit envelopes -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under GRH for a nonprincipal character at nonzero level q and G≥16 with
log(conductor)≤G, a unit-prime non-one witness lies below the selected envelope.
Apply the primitive theorem with exclusion q and transfer the value on units. -/
theorem exists_prime_ne_one_le_selected_envelope_root {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {G : ℝ} (hG : 16 ≤ G)
    (hlog : Real.log χ.conductor ≤ G) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ PaperStatements.selectedReciprocalWitnessBound G q ∧ ¬p ∣ q ∧ χ p ≠ 1 := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hc := NumberTheory.three_le_conductor_of_ne_one χ hχ
  obtain ⟨p, hp, hb, hd, hv⟩ :=
    PaperStatements.exists_prime_ne_one_le_selected_envelope_root χ.primitiveCharacter hc
      χ.primitiveCharacter_isPrimitive hGRH (NeZero.ne q) hG hlog
  have he := χ.primitiveCharacter_apply_of_isCoprime (hp.coprime_iff_not_dvd.mpr hd).isCoprime
  simp only [Int.cast_natCast] at he
  exact ⟨p, hp, hb, hd, fun h ↦ hv (he.trans h)⟩

/-- Under GRH for a nonprincipal character at nonzero level q, a unit-prime
non-one witness lies below the selected variable root in its conductor.
The existing minimum-based cap keeps the fixed estimate as a candidate. -/
theorem exists_prime_ne_one_le_selected_reciprocal_root {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤
          PaperStatements.variableReciprocalWitnessBound χ.conductor q
            (PaperStatements.halfConductorReciprocalCutoff χ.conductor) (1 / 4) (29 / 10) ∧
        ¬p ∣ q ∧ χ p ≠ 1 := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hc := NumberTheory.three_le_conductor_of_ne_one χ hχ
  obtain ⟨p, hp, hb, hd, hv⟩ :=
    PaperStatements.exists_prime_ne_one_le_selected_reciprocal_root χ.primitiveCharacter hc
      χ.primitiveCharacter_isPrimitive hGRH (NeZero.ne q)
  have he := χ.primitiveCharacter_apply_of_isCoprime (hp.coprime_iff_not_dvd.mpr hd).isCoprime
  simp only [Int.cast_natCast] at he
  exact ⟨p, hp, hb, hd, fun h ↦ hv (he.trans h)⟩

/-- Under GRH, a nonprincipal character trivial on a subgroup gives a unit-prime
outside its image below the selected envelope, assuming G≥16 and log(conductor)≤G.
Transfer the proved non-one value to subgroup nonmembership. -/
theorem exists_prime_outside_le_selected_envelope {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ht : ∀ u : (ZMod q)ˣ, u ∈ H → χ (u : ZMod q) = 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {G : ℝ} (hG : 16 ≤ G)
    (hlog : Real.log χ.conductor ≤ G) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧
        (p : ℝ) ≤ PaperStatements.selectedReciprocalWitnessBound G q ∧
        ¬∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q) := by
  obtain ⟨p, hp, hb, hd, hv⟩ := exists_prime_ne_one_le_selected_envelope_root χ hχ hGRH hG hlog
  refine ⟨p, hp, hd, hb, ?_⟩
  rintro ⟨u, hu, he⟩
  exact hv (he ▸ ht u hu)

end PseudoPrime.LLS

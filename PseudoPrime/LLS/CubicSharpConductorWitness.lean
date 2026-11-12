/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.CubicDefectSharp

/-! # Cubic witnesses using the improved Chebyshev bound -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under GRH, a nonprincipal character has a unit-prime non-one witness below
its sharp cubic conductor radius. Transfer the primitive-character witness on units. -/
theorem exists_prime_ne_one_le_cubic_sharp {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {G : ℝ}
    (hlog : Real.log χ.conductor ≤ G) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (PaperStatements.cubicSharpRadius G q) ^ 2 ∧ ¬p ∣ q ∧ χ p ≠ 1 := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hc := NumberTheory.three_le_conductor_of_ne_one χ hχ
  have hn := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hχ
  obtain ⟨p, hp, hb, hd, hv⟩ :=
    PaperStatements.exists_prime_le_cubicSharpRadius χ.primitiveCharacter
      (le_trans (by decide : 2 ≤ 3) hc) (NeZero.ne q) hGRH χ.primitiveCharacter_isPrimitive hn hlog
  have he := χ.primitiveCharacter_apply_of_isCoprime (hp.coprime_iff_not_dvd.mpr hd).isCoprime
  simp only [Int.cast_natCast] at he
  exact ⟨p, hp, hb, hd, fun h ↦ hv (he.trans h)⟩

/-- Under GRH, a nonprincipal character trivial on `H` yields a prime outside `H`
within the sharp cubic radius. The non-one character value rules out membership in `H`. -/
theorem exists_prime_outside_le_cubic_sharp {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ht : ∀ u : (ZMod q)ˣ, u ∈ H → χ (u : ZMod q) = 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {G : ℝ}
    (hlog : Real.log χ.conductor ≤ G) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧
        (p : ℝ) ≤ (PaperStatements.cubicSharpRadius G q) ^ 2 ∧
        ¬∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q) := by
  obtain ⟨p, hp, hb, hd, hv⟩ := exists_prime_ne_one_le_cubic_sharp χ hχ hGRH hlog
  exact ⟨p, hp, hd, hb, fun ⟨u, hu, he⟩ ↦ hv (he ▸ ht u hu)⟩

end PseudoPrime.LLS

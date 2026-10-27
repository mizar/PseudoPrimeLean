/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.VariableReciprocalConductorBounds
public import PseudoPrime.PseudoSquare.Bounds.DirectHadamardJacobiBounds

/-! # Quadratic witnesses with a variable reciprocal cutoff -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Under GRH for odd nonsquare n and any reciprocal cutoff x ≥ 64, an odd
coprime negative prime lies below the variable even root in the actual conductor.
Exclude 2n, preserve primitive evenness, and transfer the non-one value to Jacobi -1. -/
theorem exists_prime_neg_one_le_variable_reciprocal_conductor_root {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ}
    (hx : 64 ≤ x) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        Nat.Coprime p n ∧
        jacobiSym n p = -1 ∧
        (p : ℝ) ≤
          LLS.PaperStatements.variableReciprocalWitnessBound
            (NumberTheory.complexQuadraticCharacter n hn).conductor (2 * n) x (179 / 200)
            (21 / 10) := by
  let χ := NumberTheory.complexQuadraticCharacter n hn
  let : NeZero (4 * n) := ⟨mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hχ : χ ≠ 1 := by
    intro he
    have hc := DirichletCharacter.eq_one_iff_conductor_eq_one.mp he
    have hh : NumberTheory.primitiveQuadraticCharacter n hn = 1 :=
      DirichletCharacter.level_one' _ hc
    exact NumberTheory.primitiveQuadraticCharacter_ne_one_of_not_square n hn hns hh
  have hf := NumberTheory.three_le_conductor_of_ne_one χ hχ
  obtain ⟨p, hp, hb, hd, hv⟩ :=
    LLS.PaperStatements.exists_prime_ne_one_le_even_variable_reciprocal_root χ.primitiveCharacter hf
      χ.primitiveCharacter_isPrimitive
      ((NumberTheory.primitiveCharacter_even_iff χ).mpr
        (NumberTheory.complexQuadraticCharacter_isEven n hn))
      hGRH (mul_ne_zero (by norm_num only : (2 : ℕ) ≠ 0) hn.pos.ne') hx
  have hpn : ¬p ∣ n := fun h ↦ hd (h.trans (dvd_mul_left n 2))
  have hp2 : p ≠ 2 := by
    intro he
    apply hd
    rw [he]
    exact dvd_mul_right 2 n
  have ho := hp.odd_of_ne_two hp2
  have hcop := hp.coprime_iff_not_dvd.mpr hpn
  have he := NumberTheory.primitiveQuadraticCharacter_apply_odd_prime hn hp ho hpn
  simp only [Int.cast_natCast] at he
  have hne : jacobiSym n p ≠ 1 := by
    intro h
    apply hv
    change NumberTheory.primitiveQuadraticCharacter n hn p = 1
    rw [he, h, Int.cast_one]
  have hj :=
    jacobiSym.eq_one_or_neg_one
      (show (n : ℤ).gcd p = 1 by
        rw [Int.gcd_natCast_natCast]
        exact hcop.symm.gcd_eq_one)
  exact ⟨p, hp, ho, hcop, hj.resolve_left hne, hb⟩

/-- Under GRH for odd nonsquare n, the least negative odd-prime witness is at
most the variable even conductor bound at every x ≥ 64. Apply leastness to the
actual prime theorem. This connects cutoff selection to the public least witness. -/
theorem primeNegOneWitness_le_variable_reciprocal_conductor_root {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) {x : ℝ} (hx : 64 ≤ x) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤
      LLS.PaperStatements.variableReciprocalWitnessBound
        (NumberTheory.complexQuadraticCharacter n hn).conductor (2 * n) x (179 / 200)
        (21 / 10) := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ :=
    exists_prime_neg_one_le_variable_reciprocal_conductor_root (hn := hn) (hns := hns) hGRH hx
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hj⟩)).trans hb

/-- Under GRH for odd nonsquare n, the least non-one odd-prime witness is at
most the variable even conductor bound at every x ≥ 64. A negative Jacobi value
is non-one, so the actual negative prime also bounds this least witness. -/
theorem primeNeOneWitness_le_variable_reciprocal_conductor_root {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) {x : ℝ} (hx : 64 ≤ x) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤
      LLS.PaperStatements.variableReciprocalWitnessBound
        (NumberTheory.complexQuadraticCharacter n hn).conductor (2 * n) x (179 / 200)
        (21 / 10) := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ :=
    exists_prime_neg_one_le_variable_reciprocal_conductor_root (hn := hn) (hns := hns) hGRH hx
  have hne : jacobiSym n p ≠ 1 := by
    rw [hj]; norm_num only
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hne⟩)).trans hb

end PseudoPrime.PseudoSquare

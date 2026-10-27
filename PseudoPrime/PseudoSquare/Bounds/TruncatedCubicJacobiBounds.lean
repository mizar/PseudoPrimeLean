/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TruncatedCubicIteration
public import PseudoPrime.PseudoSquare.Bounds.TightCubicNegativeSupportBounds

/-! # Negative Jacobi witnesses with cutoff-localized cubic costs -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Under GRH, conductor and cutoff-localized cost envelopes with squared
cubic radius at most X give an odd coprime negative Jacobi prime at most X.
Apply localized primitive-character extraction and transfer its value.
Only excluded prime factors at most X contribute to the cost. -/
theorem exists_prime_neg_one_le_of_truncated_cubic_radius {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {G E X : ℝ}
    (hlog : Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ G)
    (hcost :
      LLS.PaperStatements.truncatedCharacterExclusionCost
          (NumberTheory.primitiveQuadraticCharacter n hn) (2 * n) X ≤
        E)
    (hbound : (LLS.PaperStatements.tightCubicExclusionRadius G E) ^ 2 ≤ X) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ Nat.Coprime p n ∧ jacobiSym n p = -1 ∧ (p : ℝ) ≤ X := by
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
  have hprim := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hχ
  obtain ⟨p, hp, hb, hd, hv⟩ :=
    LLS.PaperStatements.exists_prime_outside_le_of_truncated_cubic_radius χ.primitiveCharacter
      (le_trans (by decide : 2 ≤ 3) hf) (mul_ne_zero (by norm_num only : (2 : ℕ) ≠ 0) hn.pos.ne')
      hGRH χ.primitiveCharacter_isPrimitive hprim hlog hcost hbound
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

/-- Under GRH, the localized cubic fixed-point criterion bounds the least
negative odd-prime witness. Leastness transfers the extracted prime bound,
preserving the cutoff and its smaller exclusion cost. -/
theorem primeNegOneWitness_le_of_truncated_cubic_radius {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) {G E X : ℝ}
    (hlog : Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ G)
    (hcost :
      LLS.PaperStatements.truncatedCharacterExclusionCost
          (NumberTheory.primitiveQuadraticCharacter n hn) (2 * n) X ≤
        E)
    (hbound : (LLS.PaperStatements.tightCubicExclusionRadius G E) ^ 2 ≤ X) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ X := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ :=
    exists_prime_neg_one_le_of_truncated_cubic_radius (hns := hns) hGRH hlog hcost hbound
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hj⟩)).trans hb

/-- The same localized negative witness also bounds the least non-one
odd-prime witness, without identifying their least values. The witness is
coprime to n and its Jacobi value is minus one. -/
theorem primeNeOneWitness_le_of_truncated_cubic_radius {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) {G E X : ℝ}
    (hlog : Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ G)
    (hcost :
      LLS.PaperStatements.truncatedCharacterExclusionCost
          (NumberTheory.primitiveQuadraticCharacter n hn) (2 * n) X ≤
        E)
    (hbound : (LLS.PaperStatements.tightCubicExclusionRadius G E) ^ 2 ≤ X) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ X := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ :=
    exists_prime_neg_one_le_of_truncated_cubic_radius (hns := hns) hGRH hlog hcost hbound
  have hjne : jacobiSym n p ≠ 1 := hj.trans_ne (by decide : (-1 : ℤ) ≠ 1)
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hjne⟩)).trans hb

/-- Every descending localized cubic iterate bounds the least negative
odd-prime witness under GRH. The conductor logarithm supplies the sign of G;
the proved step invariant supplies the fixed-point inequality. -/
theorem primeNegOneWitness_le_truncatedCubicIterate {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) {G : ℝ}
    (hlog : Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ G) (k : ℕ) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤
      LLS.PaperStatements.truncatedCubicIterate (NumberTheory.primitiveQuadraticCharacter n hn)
        (2 * n) G k := by
  exact
    primeNegOneWitness_le_of_truncated_cubic_radius (hns := hns) hGRH hw hlog le_rfl
      (LLS.PaperStatements.truncatedCubicIterate_step_le _ _
        ((Real.log_natCast_nonneg _).trans hlog) k)

end PseudoPrime.PseudoSquare

/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.CubicCharacterExclusion
public import PseudoPrime.PseudoSquare.Bounds.CubicConductorJacobiBounds

/-! # Negative Jacobi witnesses retaining character-sensitive exclusions -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

open AnalyticNumberTheory.Arithmetic in
/-- For an odd nonsquare input under GRH, envelopes for the primitive conductor
and its character-sensitive cost at 2n give an odd coprime negative prime witness.
Use the refined primitive extraction and the odd-prime evaluation of the canonical
quadratic character. This keeps arithmetic cost estimates as separate inputs. -/
theorem exists_prime_neg_one_le_cubic_sensitive_radius {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {G E : ℝ}
    (hlog : Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ G)
    (hcost : characterExclusionCost (NumberTheory.primitiveQuadraticCharacter n hn) (2 * n) ≤ E) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        Nat.Coprime p n ∧
        jacobiSym n p = -1 ∧ (p : ℝ) ≤ (LLS.PaperStatements.cubicExclusionRadius G E) ^ 2 := by
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
    LLS.PaperStatements.exists_prime_outside_le_cubic_exclusion_radius χ.primitiveCharacter
      (le_trans (by decide : 2 ≤ 3) hf) (mul_ne_zero (by norm_num only : (2 : ℕ) ≠ 0) hn.pos.ne')
      hGRH χ.primitiveCharacter_isPrimitive hprim hlog hcost
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

open AnalyticNumberTheory.Arithmetic in
/-- The least negative odd-prime witness satisfies the refined cubic envelope
under GRH and the two cost envelopes. Apply leastness to the constructed prime,
so the arithmetic assumptions are exactly those of the existence theorem. -/
theorem primeNegOneWitness_le_cubic_sensitive_radius {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {G E : ℝ}
    (hlog : Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ G)
    (hcost : characterExclusionCost (NumberTheory.primitiveQuadraticCharacter n hn) (2 * n) ≤ E)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤
      (LLS.PaperStatements.cubicExclusionRadius G E) ^ 2 := by
  obtain ⟨p, hp, ho, _, hj, hb⟩ :=
    exists_prime_neg_one_le_cubic_sensitive_radius (hns := hns) hGRH hlog hcost
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hj⟩)).trans hb

end PseudoPrime.PseudoSquare

/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterProgressionSums
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.BoundedPrimitiveLabels

/-! # Elementary cardinality and conductor bounds for character families -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- At a nonzero level, every finite complex character family has cardinality at
most the level. Use the character count equal to the totient and the elementary
totient upper bound. This controls the explicit remainder sum after weighted density. -/
theorem card_character_family_le_level {q : ℕ} [NeZero q] (S : Finset (DirichletCharacter ℂ q)) :
    S.card ≤ q := by
  have hc := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  rw [Nat.card_eq_fintype_card] at hc
  exact (Finset.card_le_univ S).trans (hc.trans_le (Nat.totient_le q))

/-- The number of distinct prime divisors of a nonzero natural number is at most
that number. Embed its prime support in the positive interval through the level.
This coarse bound suffices to absorb level-change corrections at polynomial scales. -/
theorem card_primeFactors_le_level {q : ℕ} (hq : q ≠ 0) : q.primeFactors.card ≤ q := by
  have hs : q.primeFactors ⊆ Finset.Icc 1 q := by
    intro p hp
    have hd := Nat.mem_primeFactors.mp hp
    exact Finset.mem_Icc.mpr ⟨hd.1.one_le, Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hd.2.1⟩
  have hc := Finset.card_le_card hs
  rw [Nat.card_Icc, Nat.add_sub_cancel] at hc
  exact hc

/-- For a character at a nonzero level below a conductor cutoff, its bounded
primitive label has numerical level at most the original level. Forget the bounded
label and use conductor divisibility. This permits one common modulus majorant
for all primitive remainder terms. -/
theorem boundedPrimitiveCharacterLabel_level_le {q Q : ℕ} [NeZero q] (hq : q ≤ Q)
    (χ : DirichletCharacter ℂ q) : (boundedPrimitiveCharacterLabel hq χ).1.val + 1 ≤ q := by
  have he := congrArg Sigma.fst (forget_boundedPrimitiveCharacterLabel hq χ)
  change (boundedPrimitiveCharacterLabel hq χ).1.val + 1 = χ.conductor at he
  rw [he]
  exact Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level

end PseudoPrime.AnalyticNumberTheory.Arithmetic

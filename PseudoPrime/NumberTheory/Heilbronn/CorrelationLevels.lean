/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.InvariantFourierBounds

/-! # Invariant level sets of Heilbronn correlations -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Nonzero difference residues whose ordered Heilbronn correlation satisfies
P. Arbitrary predicates include thresholds and dyadic bands. Excluding zero
separates its exceptional p-1 contribution in the energy argument. -/
noncomputable def heilbronnCorrelationLevel (p : ℕ) [Fact p.Prime] (P : ℕ → Prop) :
    Finset (ZMod (p ^ 2)) := by
  classical exact Finset.univ.filter (fun x ↦ x ≠ 0 ∧ P (Nat.card (cosetDifferenceAt p 0 0 x)))

/-- Membership in a correlation level is exactly nonzero difference plus
its numerical predicate. Expand the finite filter. This supplies the
threshold and band hypotheses without repeating set construction proofs. -/
theorem mem_heilbronnCorrelationLevel {p : ℕ} [Fact p.Prime] (P : ℕ → Prop) (x : ZMod (p ^ 2)) :
    x ∈ heilbronnCorrelationLevel p P ↔ x ≠ 0 ∧ P (Nat.card (cosetDifferenceAt p 0 0 x)) := by
  classical simp only [heilbronnCorrelationLevel, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Multiplication by a Heilbronn element preserves the difference count.
Write the element as a nonzero Teichmuller lift and use scaling invariance.
This is the numerical invariance behind all correlation level sets. -/
theorem correlation_mul_heilbronn {p : ℕ} [Fact p.Prime] {γ x : ZMod (p ^ 2)}
    (hγ : γ ∈ shiftedTeichCoset p 0) :
    Nat.card (cosetDifferenceAt p 0 0 (γ * x)) = Nat.card (cosetDifferenceAt p 0 0 x) := by
  obtain ⟨b, hb, he⟩ := hγ
  rw [he, principalShift_zero, one_mul, mul_comm (teichLift p b) x,
    card_cosetDifferenceAt_mul_teichLift 0 0 x b hb]

/-- Every correlation level is Heilbronn-invariant. Multiplication preserves
nonzero residues and correlation values; injectivity and equal cardinality
upgrade image inclusion to equality. No restriction on the predicate is needed. -/
theorem heilbronnCorrelationLevel_invariant {p : ℕ} [Fact p.Prime] (P : ℕ → Prop) :
    IsHeilbronnInvariant (heilbronnCorrelationLevel p P) := by
  intro γ hγ
  have hu := isUnit_of_mem_heilbronn hγ
  apply Finset.eq_of_subset_of_card_le
  · apply Finset.image_subset_iff.mpr
    intro x hx
    have hm := (mem_heilbronnCorrelationLevel P x).mp hx
    apply (mem_heilbronnCorrelationLevel P (γ * x)).mpr
    constructor
    · intro he
      exact hm.1 (hu.mul_left_cancel (he.trans (mul_zero γ).symm))
    · rw [correlation_mul_heilbronn hγ]
      exact hm.2
  · rw [Finset.card_image_of_injective _ (fun x y he ↦ hu.mul_left_cancel he)]

/-- If the level predicate excludes zero, all its residues are units.
A nonzero nonunit has empty difference fiber and hence correlation zero.
This checks the unit-support premise of the invariant Fourier estimate. -/
theorem heilbronnCorrelationLevel_units {p : ℕ} [Fact p.Prime] (P : ℕ → Prop) (hP : ¬P 0) :
    ∀ x ∈ heilbronnCorrelationLevel p P, IsUnit x := by
  intro x hx
  have hm := (mem_heilbronnCorrelationLevel P x).mp hx
  by_contra hu
  have he := cosetDifferenceAt_nonunit_empty 0 x hm.1 hu
  have hz : Nat.card (cosetDifferenceAt p 0 0 x) = 0 := by rw [he, Nat.card_of_isEmpty]
  exact hP (hz ▸ hm.2)

/-- Every correlation level excluding correlation zero satisfies the
fourth-power Fourier energy estimate at every nonzero frequency. Apply the
proved invariance and unit support. This connects the Fourier bound to the
actual threshold and dyadic sets used in mixed third energy. -/
theorem correlation_level_character_fourth_le_energy {p : ℕ} [Fact p.Prime] (P : ℕ → Prop)
    (hP : ¬P 0) {l : ZMod (p ^ 2)} (hl : l ≠ 0) :
    (((p - 1 : ℕ) : ℝ) ^ 4) * ‖residueCharacterSum (heilbronnCorrelationLevel p P) l‖ ^ 4 ≤
      (p : ℝ) ^ 2 * heilbronnEnergy p * ((heilbronnCorrelationLevel p P).card : ℝ) ^ 3 := by
  exact
    invariant_character_fourth_le_energy _ (heilbronnCorrelationLevel_invariant P)
      (heilbronnCorrelationLevel_units P hP) hl

end PseudoPrime.NumberTheory.Heilbronn

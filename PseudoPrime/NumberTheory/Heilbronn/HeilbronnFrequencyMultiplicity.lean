/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.SubquadraticEnergyBudget

/-! # Frequencies with integer multiplicities for the Heilbronn subgroup -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Nonzero integer frequencies in [-H,H], before reduction modulo the residue modulus. -/
def signedShortIntegers (H : ℕ) : Finset ℤ :=
  (Finset.Icc (-(H : ℤ)) H).erase 0

/-- Membership records both interval endpoints and exclusion of zero. -/
theorem mem_signedShortIntegers {H : ℕ} {x : ℤ} :
    x ∈ signedShortIntegers H ↔ -(H : ℤ) ≤ x ∧ x ≤ H ∧ x ≠ 0 := by
  simp only [signedShortIntegers, Finset.mem_erase, Finset.mem_Icc]
  constructor
  · rintro ⟨h0, hlo, hhi⟩
    exact ⟨hlo, hhi, h0⟩
  · rintro ⟨hlo, hhi, h0⟩
    exact ⟨h0, hlo, hhi⟩

/-- There are exactly 2H signed nonzero integers of absolute value at most H. -/
theorem card_signedShortIntegers (H : ℕ) : (signedShortIntegers H).card = 2 * H := by
  have hmem : (0 : ℤ) ∈ Finset.Icc (-(H : ℤ)) H :=
    Finset.mem_Icc.mpr ⟨neg_nonpos.mpr (Nat.cast_nonneg H), Nat.cast_nonneg H⟩
  rw [signedShortIntegers, Finset.card_erase_of_mem hmem, Int.card_Icc]
  have he : (H : ℤ) + 1 - -(H : ℤ) = ((2 * H + 1 : ℕ) : ℤ) := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [he, Int.toNat_natCast, Nat.add_sub_cancel]

/-- For any finite map, the sum of squared fiber sizes counts ordered collisions.
The proof partitions the collision set by its common image. -/
theorem sum_fiber_cards_sq {ι β : Type*} [Fintype β] [DecidableEq β] (S : Finset ι) (f : ι → β) :
    (∑ b : β, (S.filter (fun x ↦ f x = b)).card ^ 2) =
      ((S ×ˢ S).filter (fun z ↦ f z.1 = f z.2)).card := by
  classical
  let C := (S ×ˢ S).filter (fun z ↦ f z.1 = f z.2)
  have he (b : β) :
    C.filter (fun z ↦ f z.1 = b) =
      (S.filter (fun x ↦ f x = b)) ×ˢ (S.filter (fun x ↦ f x = b)) := by
    ext z
    simp only [C, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨ha, hb⟩, heq⟩, hfa⟩
      exact ⟨⟨ha, hfa⟩, ⟨hb, heq.symm.trans hfa⟩⟩
    · rintro ⟨⟨ha, hfa⟩, ⟨hb, hfb⟩⟩
      exact ⟨⟨⟨ha, hb⟩, hfa.trans hfb.symm⟩, hfa⟩
  have h :=
    Finset.card_eq_sum_card_fiberwise (s := C) (t := Finset.univ) (f := fun z ↦ f z.1)
      (fun z hz ↦ Finset.mem_univ _)
  rw [h]
  apply Finset.sum_congr rfl
  intro b hb
  rw [he, Finset.card_product, pow_two]

/-- Pairs of a Heilbronn subgroup element and a nonzero signed frequency of height H. -/
noncomputable def heilbronnFrequencyPairs (p H : ℕ) [Fact p.Prime] :
    Finset (heilbronnSubgroup p × ℤ) := by classical exact Finset.univ ×ˢ signedShortIntegers H

/-- Number of raw pairs producing a residue frequency. Integer multiplicities are retained. -/
noncomputable def heilbronnFrequencyMultiplicity (p H : ℕ) [Fact p.Prime] (w : ZMod (p ^ 2)) :
    ℕ := by
  classical
    exact ((heilbronnFrequencyPairs p H).filter (fun z ↦ ((z.1.val : ZMod (p ^ 2)) * z.2) = w)).card

/-- Summing all frequency multiplicities gives 2H(p-1), by partition into fibers
and the order p-1 of the Heilbronn subgroup. No injectivity of integer reduction is assumed. -/
theorem sum_heilbronnFrequencyMultiplicity {p H : ℕ} [Fact p.Prime] :
    (∑ w : ZMod (p ^ 2), heilbronnFrequencyMultiplicity p H w) = 2 * H * (p - 1) := by
  classical
  have h :=
    Finset.card_eq_sum_card_fiberwise (s := heilbronnFrequencyPairs p H) (t := Finset.univ) (f :=
      fun z ↦ (z.1.val : ZMod (p ^ 2)) * z.2) (fun z hz ↦ Finset.mem_univ _)
  have hs := h.symm
  change (∑ w, heilbronnFrequencyMultiplicity p H w) = (heilbronnFrequencyPairs p H).card at hs
  rw [heilbronnFrequencyPairs, Finset.card_product, Finset.card_univ, ← Nat.card_eq_fintype_card,
    card_heilbronnSubgroup, card_signedShortIntegers] at hs
  simpa only [Nat.mul_comm] using hs

end PseudoPrime.NumberTheory.Heilbronn

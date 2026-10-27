/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.LevelEnergyAmplification
public import PseudoPrime.Analysis.FiniteDyadicCover
public import Mathlib.Data.Finset.Max

/-! # Dyadic selection and amplification of retained Heilbronn energy -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Any selected nonzero energy is covered by its dyadic sublevels in at
most log₂(p)+1 bands. Apply the generic square cover to the actual level
set. Extra threshold or truncation conditions in P are preserved exactly. -/
theorem heilbronnLevelEnergy_le_sum_bands {p : ℕ} [Fact p.Prime] (P : ℕ → Prop) :
    heilbronnLevelEnergy p P ≤
      ∑ j ∈ Finset.range (Nat.log2 p + 1),
        heilbronnLevelEnergy p (fun v ↦ P v ∧ 2 ^ j ≤ v ∧ v ≤ 2 * 2 ^ j) := by
  classical
  have h :=
    PseudoPrime.Analysis.sum_squares_le_sum_dyadic_bands (heilbronnCorrelationLevel p P)
      (fun a ↦ Nat.card (cosetDifferenceAt p 0 0 a)) p
      (fun a _ ↦ (card_cosetDifferenceAt_le 0 0 a).trans (Nat.sub_le p 1))
  apply h.trans_eq
  apply Finset.sum_congr rfl
  intro j _
  unfold heilbronnLevelEnergy
  congr 1
  ext a
  simp only [Finset.mem_filter, mem_heilbronnCorrelationLevel, and_assoc]

/-- Some dyadic sublevel retains at least the selected energy divided by
log₂(p)+1, expressed without division. Choose a largest band energy in the
finite cover. This avoids enumerating residues or assuming a rich level. -/
theorem exists_dyadic_heilbronn_level_energy {p : ℕ} [Fact p.Prime] (P : ℕ → Prop) :
    ∃ j < Nat.log2 p + 1,
      heilbronnLevelEnergy p P ≤
        (Nat.log2 p + 1) * heilbronnLevelEnergy p (fun v ↦ P v ∧ 2 ^ j ≤ v ∧ v ≤ 2 * 2 ^ j) := by
  classical
  obtain ⟨j, hj, hm⟩ :=
    (Finset.range (Nat.log2 p + 1)).exists_max_image
      (fun j ↦ heilbronnLevelEnergy p (fun v ↦ P v ∧ 2 ^ j ≤ v ∧ v ≤ 2 * 2 ^ j))
      ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩
  refine ⟨j, Finset.mem_range.mp hj, (heilbronnLevelEnergy_le_sum_bands P).trans ?_⟩
  have h := Finset.sum_le_sum hm
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id] using h

/-- Every retained level has a dyadic sublevel whose concrete weighted
triple correlation controls the original level's squared energy times E.
Combine proved finite selection with B²E amplification. All row, incidence
and band-selection inputs have been discharged. -/
theorem exists_amplified_dyadic_heilbronn_level {p : ℕ} [Fact p.Prime] (P : ℕ → Prop) :
    ∃ j < Nat.log2 p + 1,
      heilbronnLevelEnergy p P ^ 2 * heilbronnEnergy p ≤
        (Nat.log2 p + 1) ^ 2 *
          ((p - 1) ^ 3 *
            weightedHeilbronnTriple p
              (heilbronnLevelWeight p (fun v ↦ P v ∧ 2 ^ j ≤ v ∧ v ≤ 2 * 2 ^ j))) := by
  obtain ⟨j, hj, hB⟩ := exists_dyadic_heilbronn_level_energy (p := p) P
  refine ⟨j, hj, ?_⟩
  have hs := Nat.mul_le_mul hB hB
  rw [← pow_two, ← pow_two, mul_pow] at hs
  calc
    _ ≤
        (Nat.log2 p + 1) ^ 2 *
          (heilbronnLevelEnergy p (fun v ↦ P v ∧ 2 ^ j ≤ v ∧ v ≤ 2 * 2 ^ j) ^ 2 *
            heilbronnEnergy p) :=
      by simpa only [mul_assoc] using Nat.mul_le_mul_right (heilbronnEnergy p) hs
    _ ≤ _ := Nat.mul_le_mul_left _ (heilbronn_level_energy_amplification (p := p) _)

end PseudoPrime.NumberTheory.Heilbronn

/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.LevelEnergySelection
public import Mathlib.Tactic.Linarith

/-! # Full Heilbronn energy amplification after the zero-difference split -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Some dyadic nonzero level controls full energy up to the exact diagonal
term (p-1)². Combine the diagonal identity with proved finite selection.
This retains the exceptional zero contribution rather than hiding it in O(1). -/
theorem exists_dyadic_level_covering_full_energy {p : ℕ} [Fact p.Prime] :
    ∃ j < Nat.log2 p + 1,
      heilbronnEnergy p ≤
        (p - 1) ^ 2 +
          (Nat.log2 p + 1) * heilbronnLevelEnergy p (fun v ↦ 2 ^ j ≤ v ∧ v ≤ 2 * 2 ^ j) := by
  obtain ⟨j, hj, hB⟩ := exists_dyadic_heilbronn_level_energy (p := p) (fun _ ↦ True)
  refine ⟨j, hj, ?_⟩
  simp only [true_and] at hB
  rw [heilbronnEnergy_eq_diagonal_add_level]
  exact Nat.add_le_add_left hB _

/-- If the diagonal is at most half the full energy, a dyadic nonzero level
retains at least E/(2(log₂(p)+1)). Use the exact diagonal split and natural
number inequalities. This supplies a rich level without assuming its existence. -/
theorem exists_dyadic_level_retaining_half_energy {p : ℕ} [Fact p.Prime]
    (hE : 2 * (p - 1) ^ 2 ≤ heilbronnEnergy p) :
    ∃ j < Nat.log2 p + 1,
      heilbronnEnergy p ≤
        2 * ((Nat.log2 p + 1) * heilbronnLevelEnergy p (fun v ↦ 2 ^ j ≤ v ∧ v ≤ 2 * 2 ^ j)) := by
  obtain ⟨j, hj, hB⟩ := exists_dyadic_level_covering_full_energy (p := p)
  refine ⟨j, hj, ?_⟩
  linarith only [hE, hB]

/-- Outside the small diagonal-energy case, full energy cubed is bounded
by an actual dyadic-weighted triple correlation with factor 4(log₂(p)+1)².
Select a rich band and apply the stronger B²E amplification. This is an
unconditional finite-count input to the remaining triple-correlation estimate. -/
theorem exists_amplified_full_energy_band {p : ℕ} [Fact p.Prime]
    (hE : 2 * (p - 1) ^ 2 ≤ heilbronnEnergy p) :
    ∃ j < Nat.log2 p + 1,
      heilbronnEnergy p ^ 3 ≤
        4 * (Nat.log2 p + 1) ^ 2 *
          ((p - 1) ^ 3 *
            weightedHeilbronnTriple p
              (heilbronnLevelWeight p (fun v ↦ 2 ^ j ≤ v ∧ v ≤ 2 * 2 ^ j))) := by
  obtain ⟨j, hj, hB⟩ := exists_dyadic_level_retaining_half_energy hE
  refine ⟨j, hj, ?_⟩
  calc
    _ = heilbronnEnergy p ^ 2 * heilbronnEnergy p := by ring
    _ ≤
        (2 * ((Nat.log2 p + 1) * heilbronnLevelEnergy p (fun v ↦ 2 ^ j ≤ v ∧ v ≤ 2 * 2 ^ j))) ^ 2 *
          heilbronnEnergy p :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hB 2)
    _ =
        4 * (Nat.log2 p + 1) ^ 2 *
          (heilbronnLevelEnergy p (fun v ↦ 2 ^ j ≤ v ∧ v ≤ 2 * 2 ^ j) ^ 2 * heilbronnEnergy p) :=
      by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (heilbronn_level_energy_amplification (p := p) _)

end PseudoPrime.NumberTheory.Heilbronn

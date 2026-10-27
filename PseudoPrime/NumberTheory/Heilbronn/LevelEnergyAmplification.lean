/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.CorrelationLevelWeights

/-! # Amplification of the exact energy retained by a Heilbronn level -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Weighted triple correlation on the Heilbronn set. Both selected
differences share the first coordinate, and the remaining edge carries
the full correlation. This is the concrete output of matrix amplification. -/
noncomputable def weightedHeilbronnTriple (p : ℕ) [Fact p.Prime] (g : ZMod (p ^ 2) → ℕ) : ℕ :=
  ∑ x : heilbronnElements p,
    ∑ y : heilbronnElements p,
      ∑ z : heilbronnElements p,
        g (x.val - y.val) * g (x.val - z.val) * Nat.card (cosetDifferenceAt p 0 0 (y.val - z.val))

/-- Exact energy retained by a nonzero correlation level. The predicate P
may select a threshold or a band. The zero-difference diagonal is excluded
by the level definition, while all selected squared counts are preserved. -/
noncomputable def heilbronnLevelEnergy (p : ℕ) [Fact p.Prime] (P : ℕ → Prop) : ℕ :=
  ∑ a ∈ heilbronnCorrelationLevel p P, Nat.card (cosetDifferenceAt p 0 0 a) ^ 2

/-- The selected level energy B satisfies B²E≤(p-1)³Q with the actual full
energy E and selected-weight triple sum Q. Evenness, invariance and the
pair-mass identity are all proved, not supplied as premises. This is the
strong amplification input for the improved Heilbronn energy exponent. -/
theorem heilbronn_level_energy_amplification {p : ℕ} [Fact p.Prime] (P : ℕ → Prop) :
    heilbronnLevelEnergy p P ^ 2 * heilbronnEnergy p ≤
      (p - 1) ^ 3 * weightedHeilbronnTriple p (heilbronnLevelWeight p P) := by
  have h :=
    invariant_weight_energy_amplification (heilbronnLevelWeight p P) (heilbronnLevelWeight_neg P)
      (fun _ hγ a ↦ heilbronnLevelWeight_invariant P hγ a)
  rw [heilbronnLevelWeight_pair_mass] at h
  exact h

/-- A selected level retains at most the full additive energy. Restrict
the nonnegative energy sum to its level set. This permits the weaker B³
form when comparison arguments do not use the stronger B²E estimate. -/
theorem heilbronnLevelEnergy_le_energy {p : ℕ} [Fact p.Prime] (P : ℕ → Prop) :
    heilbronnLevelEnergy p P ≤ heilbronnEnergy p := by
  classical exact Finset.sum_le_sum_of_subset (Finset.subset_univ (heilbronnCorrelationLevel p P))

/-- The stronger level amplification also implies B³≤(p-1)³Q, since B≤E.
This recovers the cubic-mass form without any additional analytic input. -/
theorem heilbronn_level_energy_cube_le {p : ℕ} [Fact p.Prime] (P : ℕ → Prop) :
    heilbronnLevelEnergy p P ^ 3 ≤
      (p - 1) ^ 3 * weightedHeilbronnTriple p (heilbronnLevelWeight p P) := by
  calc
    _ = heilbronnLevelEnergy p P ^ 2 * heilbronnLevelEnergy p P := by ring
    _ ≤ heilbronnLevelEnergy p P ^ 2 * heilbronnEnergy p :=
      Nat.mul_le_mul_left _ (heilbronnLevelEnergy_le_energy P)
    _ ≤ _ := heilbronn_level_energy_amplification P

/-- Full energy is the zero-difference diagonal (p-1)² plus the entire
nonzero level energy. Split the finite sum at zero and use its exact fiber
cardinality. This connects rich-level selection to the full energy E. -/
theorem heilbronnEnergy_eq_diagonal_add_level {p : ℕ} [Fact p.Prime] :
    heilbronnEnergy p = (p - 1) ^ 2 + heilbronnLevelEnergy p (fun _ ↦ True) := by
  classical
  have hs :
    heilbronnCorrelationLevel p (fun _ ↦ True) = (Finset.univ : Finset (ZMod (p ^ 2))).erase 0 := by
    ext a
    simp only [mem_heilbronnCorrelationLevel, and_true, Finset.mem_erase, Finset.mem_univ]
  have h :=
    Finset.sum_erase_add (Finset.univ : Finset (ZMod (p ^ 2)))
      (fun a ↦ Nat.card (cosetDifferenceAt p 0 0 a) ^ 2) (Finset.mem_univ 0)
  simpa only [heilbronnEnergy, heilbronnLevelEnergy, hs, card_cosetDifferenceAt_zero,
    add_comm] using h.symm

end PseudoPrime.NumberTheory.Heilbronn

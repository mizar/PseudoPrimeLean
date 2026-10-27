/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.CubicTailEnergyTruncation
public import PseudoPrime.NumberTheory.Heilbronn.TruncatedBandComparison
public import PseudoPrime.Analysis.SeparatedTailEnergyBudget

/-! # Actual energy alternatives with a log-free cutoff cost -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For odd p above the diagonal case, the actual energy satisfies three
alternatives with cutoff H=786432p^3 and the true third moment T kept
separate. All band, tail and off-diagonal estimates are proved inputs. -/
theorem heilbronnEnergy_separated_tail_alternatives {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hd : 4 * (p - 1) ^ 2 ≤ heilbronnEnergy p) :
    (heilbronnEnergy p : ℝ) ^ 3 ≤ 40 * (p : ℝ) ^ 4 * (786432 * (p : ℝ) ^ 3) * (Nat.log2 p + 1 : ℕ) ∨
      (heilbronnEnergy p : ℝ) ^ 3 ≤
        2048 * (p : ℝ) ^ 4 * heilbronnThirdEnergy p * ((Nat.log2 p + 1 : ℕ) : ℝ) ^ 3 ∨
      (heilbronnEnergy p : ℝ) ^ 13 ≤
        10995116277760000 * (p : ℝ) ^ 14 * (heilbronnThirdEnergy p : ℝ) ^ 2 *
          (786432 * (p : ℝ) ^ 3) ^ 4 *
          ((Nat.log2 p + 1 : ℕ) : ℝ) ^ 8 := by
  obtain ⟨M, j, _, hh, hS, hc⟩ := exists_cubic_tail_controlled_energy_band hodd hd
  let P := fun v ↦ v ≤ M ∧ 2 ^ j ≤ v ∧ v ≤ 2 * 2 ^ j
  have hE : (0 : ℝ) < heilbronnEnergy p :=
    Nat.cast_pos.mpr (Nat.zero_lt_one.trans_le (one_le_heilbronnEnergy (p := p)))
  have hcover : (heilbronnEnergy p : ℝ) ≤ 2 * (Nat.log2 p + 1 : ℕ) * heilbronnLevelEnergy p P := by
    have he : heilbronnEnergy p ≤ 2 * (Nat.log2 p + 1) * heilbronnLevelEnergy p P := by
      simpa only [mul_assoc, P] using hc
    exact_mod_cast he
  have hB : (0 : ℝ) < heilbronnLevelEnergy p P := by
    by_contra hn
    have hs :=
      mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) (Nat.cast_nonneg (Nat.log2 p + 1)))
        (le_of_not_gt hn)
    exact (not_le_of_gt hE) (hcover.trans hs)
  have hheight : ((2 * 2 ^ j : ℕ) : ℝ) * heilbronnEnergy p ≤ 10 * (786432 * (p : ℝ) ^ 3) := by
    exact_mod_cast hh
  have ha :
    (heilbronnLevelEnergy p P : ℝ) ^ 2 * heilbronnEnergy p ≤
      (p : ℝ) ^ 4 * (2 * 2 ^ j : ℕ) * heilbronnLevelEnergy p P +
        (p : ℝ) ^ 3 * weightedHeilbronnOffDiagonal p (heilbronnLevelWeight p P) := by
    exact_mod_cast
      level_energy_le_diagonal_add_offDiagonal_powers (p := p) P (2 * 2 ^ j) (fun _ h ↦ h.2.2)
  exact
    PseudoPrime.Analysis.separated_tail_energy_alternatives
      (Nat.cast_pos.mpr (Fact.out : p.Prime).pos) hE hB (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) hcover hheight ha
      (level_offDiagonal_scaled_square_le hodd P (2 * 2 ^ j) (fun _ h ↦ h.2.2) hS)

end PseudoPrime.NumberTheory.Heilbronn

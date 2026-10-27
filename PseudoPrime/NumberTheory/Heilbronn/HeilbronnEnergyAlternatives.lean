/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.TruncatedBandComparison
public import PseudoPrime.Analysis.ThirdMomentEnergyAlternatives

/-! # Proved full-energy alternatives for the Heilbronn subgroup -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For odd prime p outside the small diagonal-energy case, the full
Heilbronn energy satisfies one of two cubic bounds or the thirteenth-power
bound in its third moment T. Obtain an actual truncated band and discharge
every premise of the generic algebraic comparison. The remaining task is
to replace T and the dyadic band count by their proved logarithmic scales. -/
theorem heilbronnEnergy_third_moment_alternatives {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hd : 4 * (p - 1) ^ 2 ≤ heilbronnEnergy p) :
    (heilbronnEnergy p : ℝ) ^ 3 ≤ 40 * (p : ℝ) ^ 4 * heilbronnThirdEnergy p * (Nat.log2 p + 1 : ℕ) ∨
      (heilbronnEnergy p : ℝ) ^ 3 ≤
        2048 * (p : ℝ) ^ 4 * heilbronnThirdEnergy p * ((Nat.log2 p + 1 : ℕ) : ℝ) ^ 3 ∨
      (heilbronnEnergy p : ℝ) ^ 13 ≤
        10995116277760000 * (p : ℝ) ^ 14 * (heilbronnThirdEnergy p : ℝ) ^ 6 *
          ((Nat.log2 p + 1 : ℕ) : ℝ) ^ 8 := by
  obtain ⟨M, j, _, hc⟩ := exists_truncated_band_comparison hodd hd
  dsimp only at hc
  rcases hc with ⟨hcover, hheight, ha, hR⟩
  have hE : (0 : ℝ) < heilbronnEnergy p :=
    Nat.cast_pos.mpr (Nat.zero_lt_one.trans_le (one_le_heilbronnEnergy (p := p)))
  have hB : (0 : ℝ) < heilbronnLevelEnergy p (fun v ↦ v ≤ M ∧ 2 ^ j ≤ v ∧ v ≤ 2 * 2 ^ j) := by
    by_contra hn
    have hs :=
      mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) (Nat.cast_nonneg (Nat.log2 p + 1)))
        (le_of_not_gt hn)
    exact (not_le_of_gt hE) (hcover.trans hs)
  exact
    PseudoPrime.Analysis.third_moment_energy_alternatives
      (Nat.cast_pos.mpr (Fact.out : p.Prime).pos) hE hB (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) hcover hheight ha hR

end PseudoPrime.NumberTheory.Heilbronn

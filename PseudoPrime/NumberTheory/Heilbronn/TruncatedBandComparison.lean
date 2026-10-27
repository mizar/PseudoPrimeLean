/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.TruncatedEnergyBands
public import PseudoPrime.Analysis.ThirdMomentAmplificationAlgebra

/-! # Concrete retained-band inputs for the final Heilbronn energy comparison -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- The retained energy and actual off-diagonal sum satisfy the amplified
comparison with powers of p in place of p-1. Combine the proved diagonal
split with B²E amplification and monotonicity. This keeps all quantities
natural-valued before the final real algebraic comparison. -/
theorem level_energy_le_diagonal_add_offDiagonal_powers {p : ℕ} [Fact p.Prime] (P : ℕ → Prop)
    (Δ : ℕ) (hP : ∀ v, P v → v ≤ Δ) :
    heilbronnLevelEnergy p P ^ 2 * heilbronnEnergy p ≤
      p ^ 4 * Δ * heilbronnLevelEnergy p P +
        p ^ 3 * weightedHeilbronnOffDiagonal p (heilbronnLevelWeight p P) := by
  have ha := heilbronn_level_energy_amplification (p := p) P
  have hd := level_weight_triple_le_diagonal_add_offDiagonal (p := p) P Δ hP
  have hi :=
    Nat.add_le_add_right
      (Nat.mul_le_mul_right (heilbronnLevelEnergy p P) (Nat.mul_le_mul_right Δ (Nat.sub_le p 1)))
      (weightedHeilbronnOffDiagonal p (heilbronnLevelWeight p P))
  exact
    ((ha.trans (Nat.mul_le_mul_left _ hd)).trans
          (Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.sub_le p 1) 3) hi)).trans_eq
      (by ring)

/-- With card(S)Δ²≤4B, the actual off-diagonal square satisfies a budget
independent of the support cardinality. Use the proved mixed third-energy
estimate and the generic support elimination, retaining the exact third
moment T. This supplies the two terms of the final energy case split. -/
theorem level_offDiagonal_scaled_square_le {p : ℕ} [Fact p.Prime] (hodd : Odd p) (P : ℕ → Prop)
    (Δ : ℕ) (hP : ∀ v, P v → v ≤ Δ)
    (hS : (heilbronnCorrelationLevel p P).card * Δ ^ 2 ≤ 4 * heilbronnLevelEnergy p P) :
    (p : ℝ) ^ 2 * (weightedHeilbronnOffDiagonal p (heilbronnLevelWeight p P) : ℝ) ^ 2 ≤
      64 * heilbronnThirdEnergy p * (Nat.log2 p + 1 : ℕ) * (heilbronnLevelEnergy p P : ℝ) ^ 2 *
          heilbronnEnergy p +
        16384 * heilbronnThirdEnergy p * (Nat.log2 p + 1 : ℕ) * heilbronnLevelEnergy p P *
          (Δ : ℝ) ^ 2 *
          (p : ℝ) ^ 3 *
          Real.sqrt (heilbronnEnergy p) := by
  have hn := level_weight_offDiagonal_square_le (p := p) P Δ hP
  have hr :
    (weightedHeilbronnOffDiagonal p (heilbronnLevelWeight p P) : ℝ) ^ 2 ≤
      (Δ : ℝ) ^ 4 * heilbronnThirdEnergy p *
        mixedHeilbronnThirdEnergy p (heilbronnCorrelationLevel p P) := by
    exact_mod_cast hn
  have hm := mixedHeilbronnThirdEnergy_le_explicit hodd (heilbronnCorrelationLevel p P)
  have hb :=
    hr.trans
      (mul_le_mul_of_nonneg_left hm
        (mul_nonneg (pow_nonneg (Nat.cast_nonneg Δ) 4) (Nat.cast_nonneg (heilbronnThirdEnergy p))))
  have hR :
    (weightedHeilbronnOffDiagonal p (heilbronnLevelWeight p P) : ℝ) ^ 2 ≤
      (Δ : ℝ) ^ 4 * heilbronnThirdEnergy p * (Nat.log2 p + 1 : ℕ) *
        (4 * ((heilbronnCorrelationLevel p P).card : ℝ) ^ 2 * heilbronnEnergy p / (p : ℝ) ^ 2 +
          4096 * (heilbronnCorrelationLevel p P).card * p * Real.sqrt (heilbronnEnergy p)) := by
    simpa only [mul_assoc] using hb
  have hSc :
    ((heilbronnCorrelationLevel p P).card : ℝ) * (Δ : ℝ) ^ 2 ≤
      4 * (heilbronnLevelEnergy p P : ℝ) := by
    exact_mod_cast hS
  exact
    PseudoPrime.Analysis.off_diagonal_budget_le_without_support
      (Nat.cast_pos.mpr (Fact.out : p.Prime).pos) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Real.sqrt_nonneg _) hSc hR

/-- Above the small diagonal-energy case, a concrete truncated dyadic band
simultaneously satisfies retention, height control and both polynomial
amplification inequalities. B and R are its actual level energy and
off-diagonal sum. No rich-band, matrix, tail or mixed-energy premise remains. -/
theorem exists_truncated_band_comparison {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hd : 4 * (p - 1) ^ 2 ≤ heilbronnEnergy p) :
    ∃ M j : ℕ,
      j < Nat.log2 p + 1 ∧
        let P := fun v ↦ v ≤ M ∧ 2 ^ j ≤ v ∧ v ≤ 2 * 2 ^ j
        let B : ℝ := heilbronnLevelEnergy p P
        let D : ℝ := (2 * 2 ^ j : ℕ)
        let R : ℝ := weightedHeilbronnOffDiagonal p (heilbronnLevelWeight p P)
        (heilbronnEnergy p : ℝ) ≤ 2 * (Nat.log2 p + 1 : ℕ) * B ∧
          D * heilbronnEnergy p ≤ 10 * heilbronnThirdEnergy p ∧
          B ^ 2 * heilbronnEnergy p ≤ (p : ℝ) ^ 4 * D * B + (p : ℝ) ^ 3 * R ∧
          (p : ℝ) ^ 2 * R ^ 2 ≤
            64 * heilbronnThirdEnergy p * (Nat.log2 p + 1 : ℕ) * B ^ 2 * heilbronnEnergy p +
              16384 * heilbronnThirdEnergy p * (Nat.log2 p + 1 : ℕ) * B * D ^ 2 * (p : ℝ) ^ 3 *
                Real.sqrt (heilbronnEnergy p) := by
  obtain ⟨M, j, hj, hheight, hS, hcover⟩ := exists_height_controlled_energy_band hd
  refine ⟨M, j, hj, ?_⟩
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hc :
      heilbronnEnergy p ≤
        2 * (Nat.log2 p + 1) *
          heilbronnLevelEnergy p (fun v ↦ v ≤ M ∧ 2 ^ j ≤ v ∧ v ≤ 2 * 2 ^ j) := by
      simpa only [mul_assoc] using hcover
    exact_mod_cast hc
  · exact_mod_cast hheight
  · exact_mod_cast
      level_energy_le_diagonal_add_offDiagonal_powers (p := p)
        (fun v ↦ v ≤ M ∧ 2 ^ j ≤ v ∧ v ≤ 2 * 2 ^ j) (2 * 2 ^ j) (fun _ h ↦ h.2.2)
  · exact
      level_offDiagonal_scaled_square_le hodd (fun v ↦ v ≤ M ∧ 2 ^ j ≤ v ∧ v ≤ 2 * 2 ^ j)
        (2 * 2 ^ j) (fun _ h ↦ h.2.2) hS

end PseudoPrime.NumberTheory.Heilbronn

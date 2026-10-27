/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.ThirdMomentEnergyTruncation
public import PseudoPrime.NumberTheory.Heilbronn.LevelEnergySelection

/-! # Rich dyadic Heilbronn bands with controlled height -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- A level whose correlations are all at least K has card(S)K²≤B.
Compare each squared correlation with K² and sum. This controls the support
size in the explicit mixed-energy budget without a new counting assumption. -/
theorem card_mul_sq_le_heilbronnLevelEnergy {p : ℕ} [Fact p.Prime] (P : ℕ → Prop) (K : ℕ)
    (hP : ∀ v, P v → K ≤ v) :
    (heilbronnCorrelationLevel p P).card * K ^ 2 ≤ heilbronnLevelEnergy p P := by
  have h :=
    Finset.sum_le_sum (s := heilbronnCorrelationLevel p P)
      (fun a ha ↦ Nat.pow_le_pow_left (hP _ ((mem_heilbronnCorrelationLevel P a).mp ha).2) 2)
  simpa only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, heilbronnLevelEnergy] using h

/-- If the diagonal is at most E/4, some truncated dyadic level retains
E/(2J), with J=log₂(p)+1. Its lower band height is at most the cutoff M
and ME≤5E₃. Choose the proved third-moment cutoff, select a rich band, and
use positive retained energy to prove that the selected band is nonempty. -/
theorem exists_truncated_dyadic_energy_band {p : ℕ} [Fact p.Prime]
    (hd : 4 * (p - 1) ^ 2 ≤ heilbronnEnergy p) :
    ∃ M j : ℕ,
      0 < M ∧
        j < Nat.log2 p + 1 ∧
        M * heilbronnEnergy p ≤ 5 * heilbronnThirdEnergy p ∧
        2 ^ j ≤ M ∧
        heilbronnEnergy p ≤
          2 *
            ((Nat.log2 p + 1) *
              heilbronnLevelEnergy p (fun v ↦ v ≤ M ∧ 2 ^ j ≤ v ∧ v ≤ 2 * 2 ^ j)) := by
  classical
  obtain ⟨M, hM, _, hME, hlo⟩ := exists_heilbronn_energy_retaining_cutoff hd
  obtain ⟨j, hj, hband⟩ := exists_dyadic_heilbronn_level_energy (p := p) (fun v ↦ v ≤ M)
  have hcover := hlo.trans (Nat.mul_le_mul_left 2 hband)
  have hpos : 0 < heilbronnLevelEnergy p (fun v ↦ v ≤ M ∧ 2 ^ j ≤ v ∧ v ≤ 2 * 2 ^ j) := by
    by_contra hn
    have hz := Nat.eq_zero_of_not_pos hn
    rw [hz, mul_zero, mul_zero] at hcover
    exact Nat.not_succ_le_zero 0 ((one_le_heilbronnEnergy (p := p)).trans hcover)
  have hset := Finset.nonempty_of_sum_ne_zero hpos.ne'
  obtain ⟨a, ha⟩ := hset
  have hmem :=
    (mem_heilbronnCorrelationLevel (p := p) (fun v ↦ v ≤ M ∧ 2 ^ j ≤ v ∧ v ≤ 2 * 2 ^ j) a).mp ha
  exact ⟨M, j, hM, hj, hME, hmem.2.2.1.trans hmem.2.1, hcover⟩

/-- A rich truncated band can be chosen with height Δ=2·2^j satisfying
ΔE≤10E₃ and card(S)Δ²≤4B. The retained energy also satisfies E≤2JB.
These are the actual height and support constraints needed to eliminate
B, S and Δ from the proved explicit amplification comparison. -/
theorem exists_height_controlled_energy_band {p : ℕ} [Fact p.Prime]
    (hd : 4 * (p - 1) ^ 2 ≤ heilbronnEnergy p) :
    ∃ M j : ℕ,
      j < Nat.log2 p + 1 ∧
        (2 * 2 ^ j) * heilbronnEnergy p ≤ 10 * heilbronnThirdEnergy p ∧
        (heilbronnCorrelationLevel p (fun v ↦ v ≤ M ∧ 2 ^ j ≤ v ∧ v ≤ 2 * 2 ^ j)).card *
            (2 * 2 ^ j) ^ 2 ≤
          4 * heilbronnLevelEnergy p (fun v ↦ v ≤ M ∧ 2 ^ j ≤ v ∧ v ≤ 2 * 2 ^ j) ∧
        heilbronnEnergy p ≤
          2 *
            ((Nat.log2 p + 1) *
              heilbronnLevelEnergy p (fun v ↦ v ≤ M ∧ 2 ^ j ≤ v ∧ v ≤ 2 * 2 ^ j)) := by
  obtain ⟨M, j, _, hj, hME, hK, hcover⟩ := exists_truncated_dyadic_energy_band hd
  refine ⟨M, j, hj, ?_, ?_, hcover⟩
  · have h := (Nat.mul_le_mul_right (heilbronnEnergy p) hK).trans hME
    nlinarith only [h]
  · have h :=
      Nat.mul_le_mul_left 4
        (card_mul_sq_le_heilbronnLevelEnergy (p := p) (fun v ↦ v ≤ M ∧ 2 ^ j ≤ v ∧ v ≤ 2 * 2 ^ j)
          (2 ^ j) (fun _ h ↦ h.2.1))
    nlinarith only [h]

end PseudoPrime.NumberTheory.Heilbronn

/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.CubicTailUpperSquareMass
public import PseudoPrime.NumberTheory.Heilbronn.FullCorrelationTail
public import PseudoPrime.NumberTheory.Heilbronn.ThirdMomentEnergyTruncation
public import PseudoPrime.NumberTheory.Heilbronn.TruncatedEnergyBands

/-! # Heilbronn energy cutoffs with a logarithm-free cubic-tail budget -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For odd prime p and positive M, the upper nonzero square mass times M
is at most 786432p^3. Apply the uniform cubic distribution tail to the
finite nonzero correlation set. Unlike the third moment, this has no log. -/
theorem heilbronnLevelEnergy_upper_tail_mul_le_cubic {p M : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hM : 0 < M) : M * heilbronnLevelEnergy p (fun v ↦ M < v) ≤ 786432 * p ^ 3 := by
  classical
  let S := heilbronnCorrelationLevel p (fun _ ↦ True)
  let N := fun x : ZMod (p ^ 2) ↦ Nat.card (cosetDifferenceAt p 0 0 x)
  have ht (K : ℕ) (hK : 0 < K) : (S.filter (fun x ↦ K ≤ N x)).card * K ^ 3 ≤ 262144 * p ^ 3 := by
    have hc :=
      card_mul_cube_le_of_unit_correlation_ge hodd (heilbronnCorrelationLevel p (fun v ↦ K ≤ v))
        (heilbronnCorrelationLevel_units (fun v ↦ K ≤ v) (fun h ↦ (Nat.not_le_of_lt hK) h))
        (fun x hx ↦ ((mem_heilbronnCorrelationLevel (fun v ↦ K ≤ v) x).mp hx).2)
    simpa only [S, N, heilbronnCorrelationLevel, Finset.filter_filter, and_true] using hc
  have h :=
    PseudoPrime.Analysis.upper_square_mass_mul_le_of_cubic_tail S N p (262144 * p ^ 3) M
      (fun x _ ↦ (card_cosetDifferenceAt_le 0 0 x).trans (Nat.sub_le p 1)) hM ht
  simpa only [S, N, heilbronnLevelEnergy, heilbronnCorrelationLevel, Finset.filter_filter, and_true,
    show 3 * (262144 * p ^ 3) = 786432 * p ^ 3 by ring] using h

/-- Above the small diagonal case, a positive cutoff retains half the
energy and satisfies 4C<=ME<=5C for C=786432p^3. Apply the generic rounding
lemma and the log-free tail bound, keeping the third moment out of C. -/
theorem exists_cubic_tail_energy_cutoff {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hd : 4 * (p - 1) ^ 2 ≤ heilbronnEnergy p) :
    ∃ M : ℕ,
      0 < M ∧
        4 * (786432 * p ^ 3) ≤ M * heilbronnEnergy p ∧
        M * heilbronnEnergy p ≤ 5 * (786432 * p ^ 3) ∧
        heilbronnEnergy p ≤ 2 * heilbronnLevelEnergy p (fun v ↦ v ≤ M) := by
  have hEp : heilbronnEnergy p ≤ 786432 * p ^ 3 :=
    (heilbronnEnergy_le_cube.trans (Nat.pow_le_pow_left (Nat.sub_le p 1) 3)).trans
      (Nat.le_mul_of_pos_left (p ^ 3) (by decide : 0 < 786432))
  obtain ⟨M, hM, hlo, hhi⟩ :=
    PseudoPrime.Analysis.exists_third_moment_cutoff
      (Nat.zero_lt_one.trans_le (one_le_heilbronnEnergy (p := p))) hEp
  refine ⟨M, hM, hlo, hhi, ?_⟩
  have he := heilbronnEnergy_eq_diagonal_add_level (p := p)
  rw [← heilbronnLevelEnergy_cutoff_partition M] at he
  exact
    PseudoPrime.Analysis.half_energy_le_of_third_moment_cutoff (by simpa only [add_assoc] using he)
      hd (heilbronnLevelEnergy_upper_tail_mul_le_cubic hodd hM) hlo hM

/-- A log-free cutoff contains a rich dyadic band with height Delta and
Delta E<=10C. Its retained energy is at least E/(2J) and card(S)Delta^2<=4B.
This supplies the actual arithmetic inputs for the log10 comparison. -/
theorem exists_cubic_tail_controlled_energy_band {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hd : 4 * (p - 1) ^ 2 ≤ heilbronnEnergy p) :
    ∃ M j : ℕ,
      j < Nat.log2 p + 1 ∧
        (2 * 2 ^ j) * heilbronnEnergy p ≤ 10 * (786432 * p ^ 3) ∧
        (heilbronnCorrelationLevel p (fun v ↦ v ≤ M ∧ 2 ^ j ≤ v ∧ v ≤ 2 * 2 ^ j)).card *
            (2 * 2 ^ j) ^ 2 ≤
          4 * heilbronnLevelEnergy p (fun v ↦ v ≤ M ∧ 2 ^ j ≤ v ∧ v ≤ 2 * 2 ^ j) ∧
        heilbronnEnergy p ≤
          2 *
            ((Nat.log2 p + 1) *
              heilbronnLevelEnergy p (fun v ↦ v ≤ M ∧ 2 ^ j ≤ v ∧ v ≤ 2 * 2 ^ j)) := by
  classical
  obtain ⟨M, _, _, hME, hlo⟩ := exists_cubic_tail_energy_cutoff hodd hd
  obtain ⟨j, hj, hb⟩ := exists_dyadic_heilbronn_level_energy (p := p) (fun v ↦ v ≤ M)
  have hcover := hlo.trans (Nat.mul_le_mul_left 2 hb)
  have hpos : 0 < heilbronnLevelEnergy p (fun v ↦ v ≤ M ∧ 2 ^ j ≤ v ∧ v ≤ 2 * 2 ^ j) := by
    by_contra hn
    rw [Nat.eq_zero_of_not_pos hn, mul_zero, mul_zero] at hcover
    exact Nat.not_succ_le_zero 0 ((one_le_heilbronnEnergy (p := p)).trans hcover)
  obtain ⟨a, ha⟩ := Finset.nonempty_of_sum_ne_zero hpos.ne'
  have hmem :=
    (mem_heilbronnCorrelationLevel (p := p) (fun v ↦ v ≤ M ∧ 2 ^ j ≤ v ∧ v ≤ 2 * 2 ^ j) a).mp ha
  have hK : 2 ^ j ≤ M := hmem.2.2.1.trans hmem.2.1
  refine ⟨M, j, hj, ?_, ?_, hcover⟩
  · have he := (Nat.mul_le_mul_right (heilbronnEnergy p) hK).trans hME
    nlinarith only [he]
  · have he :=
      Nat.mul_le_mul_left 4
        (card_mul_sq_le_heilbronnLevelEnergy (p := p) (fun v ↦ v ≤ M ∧ 2 ^ j ≤ v ∧ v ≤ 2 * 2 ^ j)
          (2 ^ j) (fun _ h ↦ h.2.1))
    nlinarith only [he]

end PseudoPrime.NumberTheory.Heilbronn

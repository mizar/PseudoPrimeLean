/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.TripleDiagonalSplit
public import PseudoPrime.NumberTheory.Heilbronn.WeightedCorrelationAmplification
public import PseudoPrime.NumberTheory.Heilbronn.CubicTailEnergyTruncation
public import PseudoPrime.NumberTheory.Heilbronn.TruncatedBandComparison

/-! # Moment bounds for the full truncated Heilbronn correlation weight -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Squaring the truncated correlation weight gives exactly the energy below
M. Expand the indicator on the selected nonzero correlation level. -/
theorem truncated_level_weight_square_mass_eq {p M : ℕ} [Fact p.Prime] :
    (∑ a : ZMod (p ^ 2), heilbronnLevelWeight p (fun v ↦ v ≤ M) a ^ 2) =
      heilbronnLevelEnergy p (fun v ↦ v ≤ M) := by
  classical
    simp only [heilbronnLevelWeight, ite_pow, zero_pow (by decide : 2 ≠ 0), heilbronnLevelEnergy,
    Finset.sum_ite_mem, Finset.univ_inter]

/-- The fourth moment of a correlation truncated at height M is at most
M² times its retained energy. On its support, r⁴≤M²r² pointwise. This is the
moment input needed when the weighted Fourier estimate is applied to g². -/
theorem truncated_level_weight_fourth_moment_le {p M : ℕ} [Fact p.Prime] :
    (∑ a : ZMod (p ^ 2), (heilbronnLevelWeight p (fun v ↦ v ≤ M) a ^ 2) ^ 2) ≤
      M ^ 2 * heilbronnLevelEnergy p (fun v ↦ v ≤ M) := by
  classical
  simp only [heilbronnLevelWeight, ite_pow, zero_pow (by decide : 2 ≠ 0), heilbronnLevelEnergy,
    Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  have hv := ((mem_heilbronnCorrelationLevel (fun v ↦ v ≤ M) a).mp ha).2
  calc
    (Nat.card (cosetDifferenceAt p 0 0 a) ^ 2) ^ 2 =
        Nat.card (cosetDifferenceAt p 0 0 a) ^ 2 * Nat.card (cosetDifferenceAt p 0 0 a) ^ 2 :=
      by ring
    _ ≤ M ^ 2 * Nat.card (cosetDifferenceAt p 0 0 a) ^ 2 :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hv 2)

/-- The full truncated correlation weight satisfies the Fourier off-diagonal
bound with its retained energy B and cutoff M. Rewrite the Fourier mass as B
and use the fourth-moment estimate to bound the error term by M²B. -/
theorem truncated_level_offDiagonal_fourier_bound {p M : ℕ} [Fact p.Prime] (hodd : Odd p) :
    (weightedHeilbronnOffDiagonal p (heilbronnLevelWeight p (fun v ↦ v ≤ M)) : ℝ) ^ 2 ≤
      (heilbronnThirdEnergy p : ℝ) *
        (4 * heilbronnEnergy p * (heilbronnLevelEnergy p (fun v ↦ v ≤ M) : ℝ) ^ 2 / (p : ℝ) ^ 2 +
          65536 * (p : ℝ) * Real.sqrt (heilbronnEnergy p) *
            ((M : ℝ) ^ 2 * heilbronnLevelEnergy p (fun v ↦ v ≤ M))) := by
  let g := heilbronnLevelWeight p (fun v ↦ v ≤ M)
  have hm : weightedResidueMass (fun a ↦ g a ^ 2) = heilbronnLevelEnergy p (fun v ↦ v ≤ M) := by
    simpa only [weightedResidueMass, g] using
      truncated_level_weight_square_mass_eq (p := p) (M := M)
  have hvNat := truncated_level_weight_fourth_moment_le (p := p) (M := M)
  have hv :
    (∑ a : ZMod (p ^ 2), ((g a ^ 2 : ℕ) : ℝ) ^ 2) ≤
      (M : ℝ) ^ 2 * heilbronnLevelEnergy p (fun v ↦ v ≤ M) := by
    exact_mod_cast (by simpa only [g] using hvNat)
  have h := weightedHeilbronnOffDiagonal_sq_le_fourier_bound hodd g
  rw [hm] at h
  have hcoef : 0 ≤ (65536 : ℝ) * (p : ℝ) * Real.sqrt (heilbronnEnergy p) :=
    mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 65536) (Nat.cast_nonneg p))
      (Real.sqrt_nonneg _)
  have herror := mul_le_mul_of_nonneg_left hv hcoef
  have herror' := mul_le_mul_of_nonneg_left herror (Nat.cast_nonneg (heilbronnThirdEnergy p))
  have h' :
    (weightedHeilbronnOffDiagonal p (heilbronnLevelWeight p (fun v ↦ v ≤ M)) : ℝ) ^ 2 ≤
      (heilbronnThirdEnergy p : ℝ) *
        (4 * heilbronnEnergy p * (heilbronnLevelEnergy p (fun v ↦ v ≤ M) : ℝ) ^ 2 / (p : ℝ) ^ 2 +
          65536 * (p : ℝ) * Real.sqrt (heilbronnEnergy p) *
            ∑ a : ZMod (p ^ 2), ((heilbronnLevelWeight p (fun v ↦ v ≤ M) a ^ 2 : ℕ) : ℝ) ^ 2) := by
    simpa only [g, Nat.cast_pow] using h
  nlinarith only [h', herror']

/-- Clear the factor p⁻² from the Fourier main term. This scaled form is the
input for the cutoff-weight energy alternatives. -/
theorem truncated_level_offDiagonal_scaled_square_le {p M : ℕ} [Fact p.Prime] (hodd : Odd p) :
    (p : ℝ) ^ 2 *
        (weightedHeilbronnOffDiagonal p (heilbronnLevelWeight p (fun v ↦ v ≤ M)) : ℝ) ^ 2 ≤
      4 * heilbronnThirdEnergy p * heilbronnEnergy p *
          (heilbronnLevelEnergy p (fun v ↦ v ≤ M) : ℝ) ^ 2 +
        65536 * heilbronnThirdEnergy p * (p : ℝ) ^ 3 * Real.sqrt (heilbronnEnergy p) * (M : ℝ) ^ 2 *
          heilbronnLevelEnergy p (fun v ↦ v ≤ M) := by
  have h := truncated_level_offDiagonal_fourier_bound (p := p) (M := M) hodd
  have hp : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hmul := mul_le_mul_of_nonneg_left h (sq_nonneg (p : ℝ))
  have hpne : (p : ℝ) ≠ 0 := ne_of_gt hp
  have heq :
    (p : ℝ) ^ 2 *
        ((heilbronnThirdEnergy p : ℝ) *
          (4 * heilbronnEnergy p * (heilbronnLevelEnergy p (fun v ↦ v ≤ M) : ℝ) ^ 2 / (p : ℝ) ^ 2 +
            65536 * (p : ℝ) * Real.sqrt (heilbronnEnergy p) *
              ((M : ℝ) ^ 2 * heilbronnLevelEnergy p (fun v ↦ v ≤ M)))) =
      4 * heilbronnThirdEnergy p * heilbronnEnergy p *
          (heilbronnLevelEnergy p (fun v ↦ v ≤ M) : ℝ) ^ 2 +
        65536 * heilbronnThirdEnergy p * (p : ℝ) ^ 3 * Real.sqrt (heilbronnEnergy p) * (M : ℝ) ^ 2 *
          heilbronnLevelEnergy p (fun v ↦ v ≤ M) := by
    field_simp [hpne]
  exact le_trans hmul (le_of_eq heq)

/-- The log-free cubic-tail cutoff supplies one full truncated weight whose
retained energy, height budget, amplified comparison and Fourier error bound
hold simultaneously. This is the concrete input package for the no-band
energy alternatives. -/
theorem exists_truncated_weight_comparison {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hd : 4 * (p - 1) ^ 2 ≤ heilbronnEnergy p) :
    ∃ M : ℕ,
      0 < M ∧
        (heilbronnEnergy p : ℝ) ≤ 2 * (heilbronnLevelEnergy p (fun v ↦ v ≤ M) : ℝ) ∧
        (M : ℝ) * heilbronnEnergy p ≤ 2 ^ 22 * (p : ℝ) ^ 3 ∧
        (heilbronnLevelEnergy p (fun v ↦ v ≤ M) : ℝ) ^ 2 * heilbronnEnergy p ≤
          (p : ℝ) ^ 4 * M * heilbronnLevelEnergy p (fun v ↦ v ≤ M) +
            (p : ℝ) ^ 3 * weightedHeilbronnOffDiagonal p (heilbronnLevelWeight p (fun v ↦ v ≤ M)) ∧
        (p : ℝ) ^ 2 *
            (weightedHeilbronnOffDiagonal p (heilbronnLevelWeight p (fun v ↦ v ≤ M)) : ℝ) ^ 2 ≤
          4 * heilbronnThirdEnergy p * heilbronnEnergy p *
              (heilbronnLevelEnergy p (fun v ↦ v ≤ M) : ℝ) ^ 2 +
            65536 * heilbronnThirdEnergy p * (p : ℝ) ^ 3 * Real.sqrt (heilbronnEnergy p) *
              (M : ℝ) ^ 2 *
              heilbronnLevelEnergy p (fun v ↦ v ≤ M) := by
  obtain ⟨M, hM, _, hheight, hretain⟩ := exists_cubic_tail_energy_cutoff hodd hd
  refine ⟨M, hM, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast hretain
  · have hheightReal : (M : ℝ) * heilbronnEnergy p ≤ 5 * (786432 * (p : ℝ) ^ 3) := by
      exact_mod_cast hheight
    have hconst : (5 : ℝ) * 786432 ≤ 2 ^ 22 := by norm_num only
    have hp3 : (0 : ℝ) ≤ (p : ℝ) ^ 3 := pow_nonneg (Nat.cast_nonneg p) 3
    have hscale := mul_le_mul_of_nonneg_right hconst hp3
    nlinarith only [hheightReal, hscale]
  · exact_mod_cast
      level_energy_le_diagonal_add_offDiagonal_powers (p := p) (fun v ↦ v ≤ M) M (fun _ h ↦ h)
  · exact truncated_level_offDiagonal_scaled_square_le (p := p) (M := M) hodd

end PseudoPrime.NumberTheory.Heilbronn

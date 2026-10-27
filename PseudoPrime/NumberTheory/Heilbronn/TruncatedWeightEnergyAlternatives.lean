/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.TruncatedWeightEnergyAlternatives
public import PseudoPrime.Analysis.LogarithmicMomentScales
public import PseudoPrime.NumberTheory.Heilbronn.ThirdEnergyMoments
public import PseudoPrime.NumberTheory.Heilbronn.TruncatedWeightMoments

/-! # Heilbronn energy alternatives from the full truncated weight -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For every odd prime, the full truncated correlation weight gives either a
small-energy cubic bound, a third-moment cubic bound, or the thirteenth-power
bound. The cutoff, amplification, and Fourier estimates are instantiated from
the proved finite-sum package; no dyadic-band selection is used. -/
theorem heilbronn_truncated_weight_energy_alternatives {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (hd : 4 * (p - 1) ^ 2 ≤ heilbronnEnergy p) :
    (heilbronnEnergy p : ℝ) ^ 3 ≤ 2 ^ 28 * (p : ℝ) ^ 7 ∨
      (heilbronnEnergy p : ℝ) ^ 3 ≤ 2 ^ 7 * (p : ℝ) ^ 4 * heilbronnThirdEnergy p ∨
      (heilbronnEnergy p : ℝ) ^ 13 ≤ 2 ^ 132 * (p : ℝ) ^ 26 * (heilbronnThirdEnergy p : ℝ) ^ 2 := by
  have hposNat : 0 < heilbronnEnergy p := by
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    have hbase : 0 < (p - 1) ^ 2 := Nat.pow_pos (Nat.sub_pos_of_lt (by omega))
    omega
  have hpos : (0 : ℝ) < heilbronnEnergy p := Nat.cast_pos.mpr hposNat
  have hp : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  rcases exists_truncated_weight_comparison hodd hd with ⟨M, _, hretain, hcut, hampl, hR⟩
  have hBupper : (heilbronnLevelEnergy p (fun v ↦ v ≤ M) : ℝ) ≤ heilbronnEnergy p := by
    exact_mod_cast heilbronnLevelEnergy_le_energy (p := p) (fun v ↦ v ≤ M)
  have hBpos : (0 : ℝ) < heilbronnLevelEnergy p (fun v ↦ v ≤ M) := by nlinarith only [hretain, hpos]
  exact
    PseudoPrime.Analysis.truncated_weight_energy_alternatives hp hpos hBpos (Nat.cast_nonneg M)
      (Nat.cast_nonneg (heilbronnThirdEnergy p)) hretain hBupper hcut hampl hR

/-- Every odd prime has Heilbronn energy bounded by
2¹⁷⁶ p³²(1+ln p)². This keeps the actual third moment in the full truncated
weight argument and absorbs its known logarithmic bound into the thirteenth
power estimate. -/
theorem heilbronnEnergy_thirteenth_le_log_square {p : ℕ} [Fact p.Prime] (hodd : Odd p) :
    (heilbronnEnergy p : ℝ) ^ 13 ≤ 2 ^ 176 * (p : ℝ) ^ 32 * (1 + Real.log p) ^ 2 := by
  have hpNat : 1 ≤ p := Nat.one_le_cast.mpr (Fact.out : p.Prime).one_lt.le
  have hp : (1 : ℝ) ≤ p := Nat.one_le_cast.mpr (Fact.out : p.Prime).one_lt.le
  have hp0 : 0 ≤ (p : ℝ) := zero_le_one.trans hp
  have hL : (1 : ℝ) ≤ 1 + Real.log p := by linarith only [Real.log_natCast_nonneg p]
  have hL0 : 0 ≤ 1 + Real.log p := zero_le_one.trans hL
  have hE : (0 : ℝ) ≤ heilbronnEnergy p := Nat.cast_nonneg _
  have hEp : (heilbronnEnergy p : ℝ) ≤ (p : ℝ) ^ 3 := by
    exact_mod_cast heilbronnEnergy_le_cube.trans (Nat.pow_le_pow_left (Nat.sub_le p 1) 3)
  have hT := heilbronnThirdEnergy_le_log hodd
  have hT2 : (heilbronnThirdEnergy p : ℝ) ≤ 2 ^ 20 * (p : ℝ) ^ 3 * (1 + Real.log p) := by
    have hc :=
      mul_le_mul_of_nonneg_right (by norm_num only : (786433 : ℝ) ≤ 2 ^ 20)
        (mul_nonneg (pow_nonneg hp0 3) hL0)
    nlinarith only [hT, hc]
  have hL2 := PseudoPrime.Analysis.one_add_log_sq_le_four_mul hpNat
  by_cases hd : 4 * (p - 1) ^ 2 ≤ heilbronnEnergy p
  · exact
      PseudoPrime.Analysis.truncated_weight_alternatives_log_square_budget hp hE
        (Nat.cast_nonneg (heilbronnThirdEnergy p)) hL hEp hT2 hL2
        (heilbronn_truncated_weight_energy_alternatives hodd hd)
  · have hb : heilbronnEnergy p ≤ 4 * p ^ 2 :=
      (lt_of_not_ge hd).le.trans (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (Nat.sub_le p 1) 2))
    have hbr : (heilbronnEnergy p : ℝ) ≤ 4 * (p : ℝ) ^ 2 := by exact_mod_cast hb
    have hs := pow_le_pow_left₀ hE hbr 13
    have hp26 := pow_le_pow_right₀ hp (by decide : 26 ≤ 32)
    have hm :=
      mul_le_mul (by norm_num only : (4 : ℝ) ^ 13 ≤ 2 ^ 176) hp26 (pow_nonneg hp0 26)
        (by norm_num only : (0 : ℝ) ≤ 2 ^ 176)
    have hbase : (heilbronnEnergy p : ℝ) ^ 13 ≤ 2 ^ 176 * (p : ℝ) ^ 32 := by nlinarith only [hs, hm]
    have hLsq : (1 : ℝ) ≤ (1 + Real.log p) ^ 2 := one_le_pow₀ hL (n := 2)
    have hscale :=
      mul_le_mul_of_nonneg_left hLsq
        (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2 ^ 176) (pow_nonneg hp0 32))
    nlinarith only [hbase, hscale]

end PseudoPrime.NumberTheory.Heilbronn

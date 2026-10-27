/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.CubicTailEnergyAlternatives
public import PseudoPrime.Analysis.LogTenEnergyNormalization

/-! # A thirteenth-power Heilbronn energy bound with logarithmic exponent ten -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Every odd prime p satisfies E^13<=2^176 p^32(1+ln p)^10.
Use the proved log-free upper square tail for truncation, while retaining
the actual third moment in the off-diagonal estimate. Normalize all three
alternatives and include the elementary small-energy branch. No new
tail, moment, band or energy hypothesis is assumed. -/
theorem heilbronnEnergy_thirteenth_le_log_ten {p : ℕ} [Fact p.Prime] (hodd : Odd p) :
    (heilbronnEnergy p : ℝ) ^ 13 ≤ 2 ^ 176 * (p : ℝ) ^ 32 * (1 + Real.log p) ^ 10 := by
  have hp : (1 : ℝ) ≤ p := Nat.one_le_cast.mpr (Fact.out : p.Prime).one_lt.le
  have hp0 : (0 : ℝ) ≤ p := zero_le_one.trans hp
  have hL : (1 : ℝ) ≤ 1 + Real.log p := by linarith only [Real.log_natCast_nonneg p]
  have hL0 : (0 : ℝ) ≤ 1 + Real.log p := zero_le_one.trans hL
  have hE : (0 : ℝ) ≤ heilbronnEnergy p := Nat.cast_nonneg _
  have hEp : (heilbronnEnergy p : ℝ) ≤ (p : ℝ) ^ 3 := by
    exact_mod_cast heilbronnEnergy_le_cube.trans (Nat.pow_le_pow_left (Nat.sub_le p 1) 3)
  have hJ := PseudoPrime.Analysis.log2_succ_le_three_halves_one_add_log p
  have hJ0 : (0 : ℝ) ≤ ((Nat.log2 p + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hJ2 : ((Nat.log2 p + 1 : ℕ) : ℝ) ≤ 2 * (1 + Real.log p) := by nlinarith only [hJ, hL0]
  have hT := heilbronnThirdEnergy_le_log hodd
  have hT2 : (heilbronnThirdEnergy p : ℝ) ≤ 2 ^ 20 * (p : ℝ) ^ 3 * (1 + Real.log p) := by
    have hc :=
      mul_le_mul_of_nonneg_right (by norm_num only : (786433 : ℝ) ≤ 2 ^ 20)
        (mul_nonneg (pow_nonneg hp0 3) hL0)
    nlinarith only [hT, hc]
  have hcubic (hc : (heilbronnEnergy p : ℝ) ^ 3 ≤ 2 ^ 34 * (p : ℝ) ^ 7 * (1 + Real.log p) ^ 4) :
    (heilbronnEnergy p : ℝ) ^ 13 ≤ 2 ^ 176 * (p : ℝ) ^ 32 * (1 + Real.log p) ^ 10 :=
    PseudoPrime.Analysis.log_ten_budget_of_cubic hp0 hE hL0 hEp
      (PseudoPrime.Analysis.one_add_log_six_le hp) hc
  by_cases hd : 4 * (p - 1) ^ 2 ≤ heilbronnEnergy p
  · rcases heilbronnEnergy_separated_tail_alternatives hodd hd with hd' | hm | he
    · apply hcubic
      have hj :=
        mul_le_mul_of_nonneg_left hJ2
          (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 40) (pow_nonneg hp0 4))
            (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 786432) (pow_nonneg hp0 3)))
      have hl14 : 1 + Real.log p ≤ (1 + Real.log p) ^ 4 := by
        simpa only [pow_one] using pow_le_pow_right₀ hL (by decide : 1 ≤ 4)
      have hl :=
        mul_le_mul_of_nonneg_left hl14
          (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2 ^ 34) (pow_nonneg hp0 7))
      have hc :=
        mul_le_mul_of_nonneg_right (by norm_num only : (40 : ℝ) * 786432 * 2 ≤ 2 ^ 34)
          (mul_nonneg (pow_nonneg hp0 7) hL0)
      nlinarith only [hd', hj, hl, hc]
    · apply hcubic
      have hj := pow_le_pow_left₀ hJ0 hJ2 3
      have htj :=
        mul_le_mul hT2 hj (pow_nonneg hJ0 3)
          (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2 ^ 20) (pow_nonneg hp0 3)) hL0)
      have hs :=
        mul_le_mul_of_nonneg_left htj
          (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2048) (pow_nonneg hp0 4))
      nlinarith only [hm, hs]
    · exact PseudoPrime.Analysis.log_ten_budget_of_error hp0 (Nat.cast_nonneg _) hJ0 hL0 hT hJ he
  · have hb : heilbronnEnergy p ≤ 4 * p ^ 2 :=
      (lt_of_not_ge hd).le.trans (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (Nat.sub_le p 1) 2))
    have hbr : (heilbronnEnergy p : ℝ) ≤ 4 * (p : ℝ) ^ 2 := by exact_mod_cast hb
    have hs := pow_le_pow_left₀ hE hbr 13
    have hp26 := pow_le_pow_right₀ hp (by decide : 26 ≤ 32)
    have hc :=
      mul_le_mul (by norm_num only : (4 : ℝ) ^ 13 ≤ 2 ^ 176) hp26 (pow_nonneg hp0 26)
        (by norm_num only : (0 : ℝ) ≤ 2 ^ 176)
    have hl :=
      mul_le_mul_of_nonneg_left (one_le_pow₀ hL (n := 10))
        (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2 ^ 176) (pow_nonneg hp0 32))
    nlinarith only [hs, hc, hl]

/-- The logarithm-ten energy estimate gives the corresponding counting budget
whenever the displayed logarithmic slack holds. Raise the energy estimate to
`a`, multiply by `D^(13a)`, and compare with the available prime power. -/
theorem thirteenth_energy_power_lt_of_log_ten_slack {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (a D r : ℕ)
    (hlarge : (2 ^ 176 : ℝ) ^ a * (D : ℝ) ^ (13 * a) * (1 + Real.log p) ^ (10 * a) < (p : ℝ) ^ r) :
    (heilbronnEnergy p * D) ^ (13 * a) < p ^ (32 * a + r) := by
  have he :=
    pow_le_pow_left₀ (pow_nonneg (Nat.cast_nonneg (heilbronnEnergy p)) 13)
      (heilbronnEnergy_thirteenth_le_log_ten hodd) a
  have hb :
    ((heilbronnEnergy p : ℝ) * D) ^ (13 * a) ≤
      ((2 ^ 176 : ℝ) ^ a * (D : ℝ) ^ (13 * a) * (1 + Real.log p) ^ (10 * a)) *
        (p : ℝ) ^ (32 * a) := by
    convert mul_le_mul_of_nonneg_right he (pow_nonneg (Nat.cast_nonneg D) (13 * a)) using 1 <;>
      simp only [mul_pow, ← pow_mul]
    ring
  have hs :=
    mul_lt_mul_of_pos_right hlarge
      (pow_pos (Nat.cast_pos.mpr (Fact.out : p.Prime).pos : (0 : ℝ) < p) (32 * a))
  have hid : (p : ℝ) ^ r * (p : ℝ) ^ (32 * a) = (p : ℝ) ^ (32 * a + r) := by
    rw [← pow_add, Nat.add_comm]
  exact_mod_cast hb.trans_lt (hs.trans_eq hid)

end PseudoPrime.NumberTheory.Heilbronn

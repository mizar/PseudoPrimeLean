/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RationalPart2CutoffBounds

/-! # Certified comparisons for rational logarithmic profile selection

The comparisons remove dominated tuples and tuples ineligible below 10^100.
A strict improvement interval for the rational Part 2 root witnesses that it
remains useful under the input-limit policy.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For L ≥ 8, the squared rational Part 2 root is strictly smaller than
the old constant-five root squared. Compare the positive roots with constants 193/40 and five.
This certifies removal of the old tuple at the same starting value. -/
theorem rationalPart2CutoffRoot_sq_lt_old_of_ge_eight {L : ℝ} (hL : 8 ≤ L) :
    rationalPart2CutoffRoot L ^ 2 < logarithmicCutoffRoot L ^ 2 := by
  have hR0 := eight_lt_rationalPart2CutoffRoot hL
  have hR : rationalPart2CutoffRoot L < logarithmicCutoffRoot L := by
    dsimp only [rationalPart2CutoffRoot, logarithmicCutoffRoot]
    linarith only
  exact
    (sq_lt_sq₀ (show 0 ≤ rationalPart2CutoffRoot L by linarith only [hR0])
          (show 0 ≤ logarithmicCutoffRoot L by linarith only [hR0, hR])).mpr
      hR

/-- For 8 ≤ L ≤ 231, the universal rational Part 1 profile is strictly smaller
than (199/250)(L+216)². Bound log L by six and compare positive roots via 89/100.
This removes the coefficient-0.796 constant-216 tuple below the requested input limit. -/
theorem rationalProfile3000_lt_gamma_plus_216 {L : ℝ} (hL : 8 ≤ L) (hupper : L ≤ 231) :
    (L + (1791 / 250 : ℝ) * Real.log L + 499 / 250) ^ 2 < (199 / 250 : ℝ) * (L + 216) ^ 2 := by
  have hL0 : 0 < L := by linarith only [hL]
  have hz0 := Real.log_nonneg (show 1 ≤ L by linarith only [hL])
  have hz := Real.log_le_log hL0 (show L ≤ (250 : ℝ) by linarith only [hupper])
  have h250 : Real.log (250 : ℝ) < 6 := by
    rw [show (250 : ℝ) = 2 * 5 ^ 3 by norm_num only,
      Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0)
        (pow_ne_zero 3 (by norm_num only : (5 : ℝ) ≠ 0)),
      Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have hR0 : 0 ≤ L + (1791 / 250 : ℝ) * Real.log L + 499 / 250 := by linarith only [hL, hz0]
  have hR : L + (1791 / 250 : ℝ) * Real.log L + 499 / 250 < (89 / 100 : ℝ) * (L + 216) := by
    linarith only [hz, h250, hupper]
  have hs := (sq_lt_sq₀ hR0 (show 0 ≤ (89 / 100 : ℝ) * (L + 216) by linarith only [hL])).mpr hR
  nlinarith only [hs, sq_pos_of_pos (show 0 < L + 216 by linarith only [hL])]

/-- For positive n ≤ 10^100, log n ≤ 231. Take logarithms and bound log ten
using the certified logarithms of two and five.
This converts the input limit to a rational domain. -/
theorem log_nat_le_231_of_le_decimal100 {n : ℕ} (hn : 0 < n) (hupper : n ≤ 10 ^ 100) :
    Real.log n ≤ 231 := by
  have h :=
    Real.log_le_log (Nat.cast_pos.mpr hn) (by exact_mod_cast hupper : (n : ℝ) ≤ (10 : ℝ) ^ 100)
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  have h10 : Real.log (10 : ℝ) < 231 / 100 := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num only,
      Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) (by norm_num only : (5 : ℝ) ≠ 0)]
    linarith only [Real.log_two_lt_d9, Real.log_five_lt_d9]
  linarith only [h, h10]

/-- For n ≥ 1000000, the rational Part 2 squared root is strictly smaller
than (log n)². Bound log n below by twelve and log twelve above 193/80.
This exhibits an improvement interval well below 10^100. -/
theorem rationalPart2CutoffRoot_sq_lt_log_sq_of_million {n : ℕ} (hn : 1000000 ≤ n) :
    rationalPart2CutoffRoot (Real.log n) ^ 2 < Real.log n ^ 2 := by
  have h :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 1000000)
      (by exact_mod_cast hn : (1000000 : ℝ) ≤ n)
  rw [show (1000000 : ℝ) = 2 ^ 6 * 5 ^ 6 by norm_num only,
    Real.log_mul (by norm_num only) (by norm_num only), Real.log_pow, Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  have hL : 12 ≤ Real.log n := by linarith only [h, Real.log_two_gt_d9, Real.log_five_gt_d9]
  have hz := Real.log_le_log (by norm_num only : (0 : ℝ) < 12) hL
  have hz12 : (193 / 80 : ℝ) < Real.log 12 := by
    rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num only,
      Real.log_mul (by norm_num only) (by norm_num only), Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_gt_d9, Real.log_three_gt_d9]
  have hR0 := eight_lt_rationalPart2CutoffRoot (show 8 ≤ Real.log n by linarith only [hL])
  apply
    (sq_lt_sq₀ (show 0 ≤ rationalPart2CutoffRoot (Real.log n) by linarith only [hR0])
        (show 0 ≤ Real.log n by linarith only [hL])).mpr
  unfold rationalPart2CutoffRoot
  linarith only [hz, hz12]

end PseudoPrime.Analysis

namespace PseudoPrime.Analysis

/-- If d > 100 and n ≤ 10^100, a profile starting at 10^d is ineligible.
Use strict monotonicity of natural decimal powers.
This removes large-start tuples independently of numerical exploration. -/
theorem decimal_profile_ineligible_below_hundred {n d : ℕ} (hd : 100 < d) (hn : n ≤ 10 ^ 100) :
    ¬10 ^ d ≤ n := by
  intro hstart
  have h := Nat.pow_lt_pow_right (by decide : (1 : ℕ) < 10) hd
  exact (Nat.not_lt.mpr (hstart.trans hn)) h

/-- For n ≥ 80000, the rational Part 2 squared cutoff is strictly below
the pure logarithmic square. Bound log n by 45/4 and log(45/4) by the certified
logarithms of two, three and five. This gives an improvement interval below 10^100. -/
theorem rationalPart2CutoffRoot_sq_lt_log_sq_of_eightyThousand {n : ℕ} (hn : 80000 ≤ n) :
    rationalPart2CutoffRoot (Real.log n) ^ 2 < Real.log n ^ 2 := by
  have h :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 80000) (by exact_mod_cast hn : (80000 : ℝ) ≤ n)
  rw [show (80000 : ℝ) = 2 ^ 7 * 5 ^ 4 by norm_num only,
    Real.log_mul (by norm_num only) (by norm_num only), Real.log_pow, Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  have hL : (45 / 4 : ℝ) ≤ Real.log n := by
    linarith only [h, Real.log_two_gt_d9, Real.log_five_gt_d9]
  have hz := Real.log_le_log (by norm_num only : (0 : ℝ) < 45 / 4) hL
  have hz45 : (193 / 80 : ℝ) < Real.log (45 / 4 : ℝ) := by
    rw [show (45 / 4 : ℝ) = (3 ^ 2 * 5) / 2 ^ 2 by norm_num only,
      Real.log_div (by norm_num only) (by norm_num only),
      Real.log_mul (by norm_num only) (by norm_num only), Real.log_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_lt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9]
  have hR0 := eight_lt_rationalPart2CutoffRoot (show 8 ≤ Real.log n by linarith only [hL])
  apply
    (sq_lt_sq₀ (show 0 ≤ rationalPart2CutoffRoot (Real.log n) by linarith only [hR0])
        (show 0 ≤ Real.log n by linarith only [hL])).mpr
  unfold rationalPart2CutoffRoot
  linarith only [hz, hz45]

end PseudoPrime.Analysis

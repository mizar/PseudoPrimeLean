/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TwoPoleConductorPrefixBounds

/-! # Prime-power savings within the full Euler prefix through thirteen -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For a positive index n, a positive rational denominator cap b and a lower bound t on its
Mangoldt value, t/b bounds the paired Euler weight below whenever n^5 is at most b^4. Use the
fourth-power envelope and discard only the nonnegative logarithmic term. This handles prime
powers as well as primes without duplicating the real-power argument. -/
theorem pairedEulerPrefixWeight_ge_of_mangoldt_lower {n : ℕ} (hn : 0 < n) {b t : ℝ} (hb : 0 < b)
    (hpow : (n : ℝ) ^ 5 ≤ b ^ 4) (ht : t ≤ ArithmeticFunction.vonMangoldt n) :
    t / b ≤ pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4) n := by
  have hden := rpow_five_fourths_le_of_pow_four (Nat.cast_nonneg n) hb.le hpow
  have hn0 := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) (5 / 4 : ℝ)
  have hdiv :=
    (div_le_div_of_nonneg_right ht hb.le).trans
      (div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg hn0 hden)
  have htail :
    0 ≤ (3 / 4 : ℝ) * Real.log n * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (11 / 4 : ℝ) :=
    div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num only) (Real.log_natCast_nonneg n))
        ArithmeticFunction.vonMangoldt_nonneg)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  dsimp only [pairedEulerPrefixWeight]
  linarith only [hdiv, htail]

/-- The Euler weights at four, eight and nine have the displayed rational lower bounds.
Use the Mangoldt value at powers of two and three and exact fourth-power comparisons. These
terms increase the full-prefix saving without adding more prime data. -/
theorem pairedEuler_small_power_lower :
    (1 / 9 : ℝ) ≤ pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4) 4 ∧
      (1 / 21 : ℝ) ≤ pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4) 8 ∧
      (1 / 16 : ℝ) ≤ pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4) 9 := by
  have h4 :=
    pairedEulerPrefixWeight_ge_of_mangoldt_lower (n := 4) (b := 6) (t := 2 / 3) (by norm_num only)
      (by norm_num only) (by norm_num only [Nat.cast_ofNat])
      (by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num only,
          ArithmeticFunction.vonMangoldt_apply_pow (by norm_num only : (2 : ℕ) ≠ 0),
          ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
        norm_num only [Nat.cast_ofNat]
        linarith only [Real.log_two_gt_d9])
  have h8 :=
    pairedEulerPrefixWeight_ge_of_mangoldt_lower (n := 8) (b := 14) (t := 2 / 3) (by norm_num only)
      (by norm_num only) (by norm_num only [Nat.cast_ofNat])
      (by
        rw [show (8 : ℕ) = 2 ^ 3 by norm_num only,
          ArithmeticFunction.vonMangoldt_apply_pow (by norm_num only : (3 : ℕ) ≠ 0),
          ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
        norm_num only [Nat.cast_ofNat]
        linarith only [Real.log_two_gt_d9])
  have h9 :=
    pairedEulerPrefixWeight_ge_of_mangoldt_lower (n := 9) (b := 16) (t := 1) (by norm_num only)
      (by norm_num only) (by norm_num only [Nat.cast_ofNat])
      (by
        rw [show (9 : ℕ) = 3 ^ 2 by norm_num only,
          ArithmeticFunction.vonMangoldt_apply_pow (by norm_num only : (2 : ℕ) ≠ 0),
          ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three]
        norm_num only [Nat.cast_ofNat]
        linarith only [Real.log_three_gt_d9])
  norm_num only at h4 h8 h9
  exact ⟨h4, h8, h9⟩

end PseudoPrime.AnalyticNumberTheory.Arithmetic

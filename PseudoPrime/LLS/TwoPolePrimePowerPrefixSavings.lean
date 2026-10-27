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

namespace PseudoPrime.LLS

/-- The full Euler prefix through thirteen, minus the prime-two allowance, is at least one.
Retain the six prime lower bounds together with the powers four, eight and nine, and use
nonnegativity for the remaining indices. This improves the effective even-character cost to
87/25 in the conductor-cancelled negative-witness comparison. -/
theorem twoPoleEulerPrefixMass_thirteen_saving_one :
    (1 : ℝ) ≤ twoPoleEulerPrefixMass (Finset.Ioc 0 13) - (1 / 5 : ℝ) * Real.log 2 := by
  have hl9 : (2 : ℝ) ≤ Real.log 9 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_three_gt_d9]
  have hl11 :=
    hl9.trans (Real.log_le_log (by norm_num only : (0 : ℝ) < 9) (by norm_num only : (9 : ℝ) ≤ 11))
  have hl13 :=
    hl9.trans (Real.log_le_log (by norm_num only : (0 : ℝ) < 9) (by norm_num only : (9 : ℝ) ≤ 13))
  have h11 :=
    AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight_prime_ge_rational
      (by norm_num only : Nat.Prime 11) (b := 24) (t := 2) (by norm_num only)
      (by norm_num only [Nat.cast_ofNat]) hl11
  have h13 :=
    AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight_prime_ge_rational
      (by norm_num only : Nat.Prime 13) (b := 26) (t := 2) (by norm_num only)
      (by norm_num only [Nat.cast_ofNat]) hl13
  have hs : ({2,3,4,5,7,8,9,11,13} : Finset ℕ) ⊆ Finset.Ioc 0 13 := by decide
  have hsum :=
    Finset.sum_le_sum_of_subset_of_nonneg hs
      (fun n _ _ ↦
        AnalyticNumberTheory.Arithmetic.pairedEulerPrefixWeight_nonneg (5 / 4) (11 / 4)
          (by norm_num only : (0 : ℝ) ≤ 3 / 4) n)
  rw [Finset.sum_insert (by decide : (2 : ℕ) ∉ {3,4,5,7,8,9,11,13}),
    Finset.sum_insert (by decide : (3 : ℕ) ∉ {4,5,7,8,9,11,13}),
    Finset.sum_insert (by decide : (4 : ℕ) ∉ {5,7,8,9,11,13}),
    Finset.sum_insert (by decide : (5 : ℕ) ∉ {7,8,9,11,13}),
    Finset.sum_insert (by decide : (7 : ℕ) ∉ {8,9,11,13}),
    Finset.sum_insert (by decide : (8 : ℕ) ∉ {9,11,13}),
    Finset.sum_insert (by decide : (9 : ℕ) ∉ {11,13}),
    Finset.sum_insert (by decide : (11 : ℕ) ∉ {13}), Finset.sum_singleton] at hsum
  have h := AnalyticNumberTheory.Arithmetic.pairedEuler_small_prime_lower
  have hp := AnalyticNumberTheory.Arithmetic.pairedEuler_small_power_lower
  dsimp only [twoPoleEulerPrefixMass]
  norm_num only at h11 h13
  linarith only [hsum, h.1, h.2.1, h.2.2.1, h.2.2.2, h11, h13, hp.1, hp.2.1, hp.2.2,
    Real.log_two_lt_d9]

end PseudoPrime.LLS

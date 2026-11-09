/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed19
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Weighted prime table and square-factor bounds through budget 58 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Cumulative counts for the eight-prime supply through budget 58. -/
def primeSeed19Row58 : Array ℕ :=
  #[1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 6, 6, 7, 8, 9, 9, 11, 12, 13, 14, 16, 17,
    19, 22, 23, 25, 27, 30, 31, 35, 38, 40, 43, 48, 52, 54, 60, 64, 68, 73, 81, 85, 91, 99, 107,
    112, 121, 131, 138, 147, 158]

/-- Remaining cumulative-count rows for the weighted supply through budget 58. -/
def primeSeed19Tail58 : List (Array ℕ) :=
  [#[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 10,
      11, 11, 12, 13, 14, 14, 16, 16, 17, 18, 21, 22, 23, 25, 26, 28, 30, 33, 33, 37, 39, 43, 44,
      48, 50, 53, 56, 59],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 5, 5, 7,
      7, 7, 7, 8, 8, 8, 9, 9, 9, 10, 11, 11, 12, 13, 13, 14, 16, 17, 17, 20, 21, 22, 22, 25, 25, 27,
      28, 29],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 4, 4, 4, 4, 6,
      6, 6, 6, 6, 6, 6, 6, 6, 6, 7, 7, 7, 7, 8, 8, 9, 9, 10, 10, 13, 13, 14, 14, 16, 16, 18, 18,
      18],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 5,
      5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 7, 7, 8, 8, 10, 10, 12, 12, 12],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4,
      4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 7, 7, 7],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3,
      3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2,
      2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]

set_option maxRecDepth 8192 in
/-- The finite table satisfies the weighted-count recurrence through budget 58. -/
theorem primeSeed19_checked58 :
    weightedPrimeTableCheck 58 primeSeed19Weights (primeSeed19Row58 :: primeSeed19Tail58) =
      true := by
  decide +kernel

/-- The checked row gives the exact weighted-family count for every budget
through 58, by transfer from the table recurrence to the prime labels. -/
theorem primeSeed19_family58 (H : ℕ) (hH : H ≤ 58) :
    (weightedPrimeFamily primeSeed19Primes.toFinset primeSeed19Weight H).card =
      primeSeed19Row58.getD H 0 :=
  (weightedPrimeCount_weights_eq_card primeSeed19Weight H primeSeed19Primes primeSeed19Weights
        primeSeed19_labels.1 primeSeed19_labels.2.2 primeSeed19_labels.2.1).symm.trans
    ((weightedPrimeTableCheck_sound 58 primeSeed19Weights primeSeed19Row58 primeSeed19Tail58
        primeSeed19_checked58 H hH).symm)

/-- The weighted product family contains exactly 158 elements at budget 58. -/
theorem primeSeed19_card58 :
    (weightedPrimeFamily primeSeed19Primes.toFinset primeSeed19Weight 58).card = 158 := by
  have h :=
    (weightedPrimeCount_weights_eq_card primeSeed19Weight 58 primeSeed19Primes primeSeed19Weights
          primeSeed19_labels.1 primeSeed19_labels.2.2 primeSeed19_labels.2.1).symm.trans
      ((weightedPrimeTableCheck_sound 58 primeSeed19Weights primeSeed19Row58 primeSeed19Tail58
          primeSeed19_checked58 58 (by decide)).symm)
  change (weightedPrimeFamily primeSeed19Primes.toFinset primeSeed19Weight 58).card = 158 at h
  exact h

/-- A prime square dividing an input of logarithm at most 10.059 has base at most 157. -/
theorem square_factor_le_157 {n p : ℕ} (hn : 1 < n) (hdiv : p ^ 2 ∣ n)
    (hU : Real.log n ≤ (10059 / 1000 : ℝ)) : p ≤ 157 := by
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 24649 15 32 (10059 / 1000) 11 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hcert
  have hnle : n ≤ 24649 := by
    have hlog : Real.log (n : ℝ) ≤ Real.log (24649 : ℝ) := hU.trans hcert
    exact_mod_cast
      (Real.log_le_log_iff (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn))
            (by norm_num only : (0 : ℝ) < 24649)).mp
        hlog
  have hpsq : p ^ 2 ≤ 24649 := (Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hdiv).trans hnle
  nlinarith only [hpsq]

/-- The budget 58/10 is below the logarithm of the square of any integer above 19. -/
theorem square_factor_budget_58 {p : ℕ} (hbig : 19 < p) :
    (58 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ) := by
  have h20 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 20 5 32 (291 / 100) 3 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h20
  have hp20 : 20 ≤ p := Nat.succ_le_of_lt hbig
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 20) (Nat.cast_le.mpr hp20)
  rw [Nat.cast_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [h20, hl]

end PseudoPrime.PrimeTestBounds.MillerRabin

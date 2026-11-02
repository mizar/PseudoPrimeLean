/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsPrimeData
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsCellBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsCellChecks

/-! # Largest low square cell using repeated prime products -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- An odd square with `49.855 ≤ log n ≤ 56` has an MR rejecting prime
within the four-ninths bound. Reuse 185 certified primes up to 1103 and
verify the seven-factor multichoose and logarithmic endpoint conditions. -/
theorem exists_prime_witness_last_low_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpow : n = p ^ 2) (hlo : (9971 / 200 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 56) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb : Analysis.rationalLogIntervalCheck 1103 10 12 (7005 / 1000) (7006 / 1000) = true := by
    decide +kernel
  have hc :
    Analysis.rationalLogIntervalCheck 1708566412608 41 12 (2816 / 100) (2817 / 100) = true := by
    decide +kernel
  have h :=
    square_cell_checked_logs (a := (9971 / 200 : ℚ)) (b := (56 : ℚ)) (k := 7) hb hc
      (by norm_num only) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hchoose : 1708566412608 ≤ Nat.choose (185 + 7) 7 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 7)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.reduceAdd, Nat.descFactorial, Nat.factorial, Nat.mul_succ, Nat.mul_zero,
      Nat.add_zero]
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 1708566412608) (Nat.cast_le.mpr hchoose)
  have hcount : (56 : ℝ) < 2 * Real.log (Nat.choose (185 + 7) 7 : ℝ) := by linarith only [h.2, hl]
  apply
    square_cell_multichoose hn ho hp hp2 hpow (B := 1103) (M := 185) (k := 7) (by norm_num only)
      primeCount_1103_ge_185 (by norm_num only) hlo hhi h.1 hcount
  norm_num only

end PseudoPrime.PrimeTestBounds.MillerRabin

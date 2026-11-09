/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareSeed43Stage133
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed43Count197

/-! # Weighted square-divisor supply and factor bounds -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A prime-square divisor of an input with logarithm at most 25 has base at
most 335463. A rational logarithm certificate bounds the input by its square. -/
theorem square_factor_le_335463 {n p : ℕ} (hn : 1 < n) (hdiv : p ^ 2 ∣ n)
    (hU : Real.log n ≤ (25 : ℝ)) : p ≤ 335463 := by
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 112535424369 37 32 25 27 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at hcert
  have hnle : n ≤ 112535424369 := by
    have hlog : Real.log (n : ℝ) ≤ Real.log (112535424369 : ℝ) := hU.trans hcert
    exact_mod_cast
      (Real.log_le_log_iff (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn))
            (by norm_num only : (0 : ℝ) < 112535424369)).mp
        hlog
  have hpsq : p ^ 2 ≤ 112535424369 := (Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hdiv).trans hnle
  nlinarith only [hpsq]

/-- The square of an integer at least 19640 has logarithm strictly above the
third-stage budget 197/10, by a rational lower bound for `log 19640`. -/
theorem square_factor_budget_197 {p : ℕ} (hbig : 19640 ≤ p) :
    (197 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ) := by
  have h19640 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 19640 15 32 (986 / 100) 11 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h19640
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 19640) (Nat.cast_le.mpr hbig)
  rw [Nat.cast_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [h19640, hl]

set_option maxRecDepth 16384 in
/-- The third-stage weighted table gives a rejecting prime at most 43 for a
prime-square divisor of base at most 335463 when its logarithm exceeds the
budget. The table count exceeds the original-input kernel cardinality. -/
theorem exists_prime_reject_square_seed43_197 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hbound : p ≤ 335463)
    (hbudget : (197 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ r ≤ 43 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
  have hp2 : p ≠ 2 := ho.ne_two_of_dvd_nat hpn
  have hcount : p - 1 < primeSeed43Row197.getD 197 0 := by
    change p - 1 < 335463
    exact (Nat.sub_lt hp.pos (by decide : 0 < 1)).trans_le hbound
  exact
    exists_prime_reject_prime_pow_table hn ho hp hp2 (by decide : 0 < 2) hdiv primeSeed43Primes
      primeSeed43Weights 43 197 197 primeSeed43Weight 10 (by norm_num only) primeSeed43_labels.1
      (fun r hr ↦ (primeSeed43_prime_supply r hr).1) (fun r hr ↦ (primeSeed43_prime_supply r hr).2)
      primeSeed43_labels.2.2 primeSeed43_weight_bounds primeSeed43_labels.2.1 (by decide)
      primeSeed43Row197 primeSeed43Tail197 primeSeed43Table197_checked hbudget hcount

end PseudoPrime.PrimeTestBounds.MillerRabin

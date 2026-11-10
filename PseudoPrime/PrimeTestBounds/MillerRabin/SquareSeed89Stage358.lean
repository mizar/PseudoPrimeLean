/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed89Count358
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedPrimePowerTable

/-! # Weighted square-divisor supply and factor bounds -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A prime-square divisor at logarithmic scale at most 39.4 has base at
most 1054033525, by a rational logarithm certificate. -/
theorem square_factor_le_1054033525 {n p : ℕ} (hn : 1 < n) (hdiv : p ^ 2 ∣ n)
    (hU : Real.log n ≤ (197 / 5 : ℝ)) : p ≤ 1054033525 := by
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 1110986671823925625 60 32 (197 / 5) 43 = true from
          by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hcert
  have hnle : n ≤ 1110986671823925625 := by
    have hlog : Real.log (n : ℝ) ≤ Real.log (1110986671823925625 : ℝ) := hU.trans hcert
    exact_mod_cast
      (Real.log_le_log_iff (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn))
            (by norm_num only : (0 : ℝ) < 1110986671823925625)).mp
        hlog
  have hpsq : p ^ 2 ≤ 1110986671823925625 := (Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hdiv).trans hnle
  nlinarith only [hpsq]

/-- The square of an integer at least 59789535 exceeds budget 358/10
logarithmically, by a rational logarithm lower bound. -/
theorem square_factor_budget_358 {p : ℕ} (hbig : 59789535 ≤ p) :
    (358 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ) := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 59789535 26 32 (17901 / 1000) 19 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 59789535) (Nat.cast_le.mpr hbig)
  rw [Nat.cast_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [h, hl]

set_option maxRecDepth 32768 in
/-- The checked prime supply through 89 gives a rejecting prime when its
budget is below the square-divisor logarithm and its count exceeds the kernel. -/
theorem exists_prime_reject_square_seed89_358 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hbound : p ≤ 1054033525)
    (hbudget : (358 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ r ≤ 89 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
  have hp2 : p ≠ 2 := ho.ne_two_of_dvd_nat hpn
  have hcount : p - 1 < primeSeed89Row358.getD 358 0 := by
    change p - 1 < 1054033525
    exact (Nat.sub_lt hp.pos (by decide : 0 < 1)).trans_le hbound
  exact
    exists_prime_reject_prime_pow_table hn ho hp hp2 (by decide : 0 < 2) hdiv primeSeed89Primes
      primeSeed89Weights 89 358 358 primeSeed89Weight 10 (by norm_num only) primeSeed89_labels.1
      (fun r hr ↦ (primeSeed89_prime_supply r hr).1) (fun r hr ↦ (primeSeed89_prime_supply r hr).2)
      primeSeed89_labels.2.2 primeSeed89_weight_bounds primeSeed89_labels.2.1 (by decide)
      primeSeed89Row358 primeSeed89Tail358 primeSeed89_checked358 hbudget hcount

end PseudoPrime.PrimeTestBounds.MillerRabin

/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed89Count197
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedPrimePowerTable

/-! # Weighted square-divisor supply and factor bounds -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A prime-square divisor at logarithmic scale at most 28 has base at most
1372508, by a rational logarithm certificate. -/
theorem square_factor_le_1372508 {n p : ℕ} (hn : 1 < n) (hdiv : p ^ 2 ∣ n)
    (hU : Real.log n ≤ (28 : ℝ)) : p ≤ 1372508 := by
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 1883778210064 41 32 28 30 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at hcert
  have hnle : n ≤ 1883778210064 := by
    have hlog : Real.log (n : ℝ) ≤ Real.log (1883778210064 : ℝ) := hU.trans hcert
    exact_mod_cast
      (Real.log_le_log_iff (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn))
            (by norm_num only : (0 : ℝ) < 1883778210064)).mp
        hlog
  have hpsq : p ^ 2 ≤ 1883778210064 := (Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hdiv).trans hnle
  nlinarith only [hpsq]

set_option maxRecDepth 16384 in
/-- The checked 89-prime supply gives a rejecting prime when the square
divisor lies within its count bound and exceeds the budget logarithmically. -/
theorem exists_prime_reject_square_seed89_197 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hbound : p ≤ 1372508)
    (hbudget : (197 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ r ≤ 89 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
  have hp2 : p ≠ 2 := ho.ne_two_of_dvd_nat hpn
  have hcount : p - 1 < primeSeed89Row197.getD 197 0 := by
    change p - 1 < 1372508
    exact (Nat.sub_lt hp.pos (by decide : 0 < 1)).trans_le hbound
  exact
    exists_prime_reject_prime_pow_table hn ho hp hp2 (by decide : 0 < 2) hdiv primeSeed89Primes
      primeSeed89Weights 89 197 197 primeSeed89Weight 10 (by norm_num only) primeSeed89_labels.1
      (fun r hr ↦ (primeSeed89_prime_supply r hr).1) (fun r hr ↦ (primeSeed89_prime_supply r hr).2)
      primeSeed89_labels.2.2 primeSeed89_weight_bounds primeSeed89_labels.2.1 (by decide)
      primeSeed89Row197 primeSeed89Tail197 primeSeed89_checked197 hbudget hcount

end PseudoPrime.PrimeTestBounds.MillerRabin

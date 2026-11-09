/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedPrimePowerCount
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed1849
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed1849Count

/-! # Weighted and grouped square-divisor witnesses -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxRecDepth 32768 in
/-- The checked count through 373 yields an original-input rejecting prime
when its budget is below the prime-square logarithm and its count covers the
prime divisor. -/
theorem exists_prime_reject_square_seed373 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (A : ℕ) (hA : A ≤ 500) (hpC : p ≤ primeSeed373Row14.getD A 0)
    (hbudget : (A : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ r ≤ 373 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
  have hp2 : p ≠ 2 := ho.ne_two_of_dvd_nat hpn
  have hc : p - 1 < primeSeed373Row14.getD A 0 :=
    (Nat.sub_lt hp.pos (by decide : 0 < 1)).trans_le hpC
  exact
    exists_prime_reject_prime_pow_count hn ho hp hp2 (by decide : 0 < 2) hdiv primeSeed373Primes
      primeSeed373Weights 373 A (primeSeed373Row14.getD A 0) primeSeed373Weight 10
      (by norm_num only) primeSeed373_labels.1 (fun r hr ↦ (primeSeed373_prime_supply r hr).1)
      (fun r hr ↦ (primeSeed373_prime_supply r hr).2) primeSeed373_labels.2.2
      primeSeed373_weight_bounds primeSeed373_labels.2.1 hbudget hc (primeSeed373_count_lower A hA)

/-- The grouped count through 1849 yields an original-input rejecting prime
when its budget is below the prime-square logarithm and its count covers the
prime divisor. -/
theorem exists_prime_reject_square_seed1849 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (A k : ℕ) (hA : A ≤ 500)
    (hpC : p ≤ Nat.choose (209 + k) k * primeSeed373Row14.getD A 0)
    (hbudget : ((A + k * 76 : ℕ) : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ r ≤ 1849 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
  have hp2 : p ≠ 2 := ho.ne_two_of_dvd_nat hpn
  have hc : p - 1 < Nat.choose (209 + k) k * primeSeed373Row14.getD A 0 :=
    (Nat.sub_lt hp.pos (by decide : 0 < 1)).trans_le hpC
  exact
    exists_prime_reject_prime_pow_count hn ho hp hp2 (by decide : 0 < 2) hdiv primeSeed1849Primes
      primeSeed1849Weights 1849 (A + k * 76) (Nat.choose (209 + k) k * primeSeed373Row14.getD A 0)
      primeSeed1849Weight 10 (by norm_num only) primeSeed1849_labels.1
      (fun r hr ↦ (primeSeed1849_prime_supply r hr).1)
      (fun r hr ↦ (primeSeed1849_prime_supply r hr).2) primeSeed1849_labels.2.2
      primeSeed1849_weight_bounds primeSeed1849_labels.2.1 hbudget hc
      (primeSeed1849_group_lower A k hA)

end PseudoPrime.PrimeTestBounds.MillerRabin

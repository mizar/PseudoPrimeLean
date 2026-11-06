/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedPrimePowerCount
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Seed1849
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Seed1849Count

/-! # Weighted and grouped square-divisor witnesses -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxRecDepth 32768 in
/-- The checked count through 373 yields an original-input rejecting prime
when its budget is below the prime-square logarithm and its count covers the
prime divisor. -/
theorem exists_prime_reject_square_seed373 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (A : ℕ) (hA : A ≤ 500) (hpC : p ≤ target030Seed373Row14.getD A 0)
    (hbudget : (A : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ r ≤ 373 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
  have hp2 : p ≠ 2 := ho.ne_two_of_dvd_nat hpn
  have hc : p - 1 < target030Seed373Row14.getD A 0 :=
    (Nat.sub_lt hp.pos (by decide : 0 < 1)).trans_le hpC
  exact
    exists_prime_reject_prime_pow_count hn ho hp hp2 (by decide : 0 < 2) hdiv target030Seed373Primes
      target030Seed373Weights 373 A (target030Seed373Row14.getD A 0) target030Seed373Weight 10
      (by norm_num only) target030Seed373_labels.1
      (fun r hr ↦ (target030Seed373_prime_supply r hr).1)
      (fun r hr ↦ (target030Seed373_prime_supply r hr).2) target030Seed373_labels.2.2
      target030Seed373_weight_bounds target030Seed373_labels.2.1 hbudget hc
      (target030Seed373_count_lower A hA)

/-- The grouped count through 1849 yields an original-input rejecting prime
when its budget is below the prime-square logarithm and its count covers the
prime divisor. -/
theorem exists_prime_reject_square_seed1849 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (A k : ℕ) (hA : A ≤ 500)
    (hpC : p ≤ Nat.choose (209 + k) k * target030Seed373Row14.getD A 0)
    (hbudget : ((A + k * 76 : ℕ) : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ r ≤ 1849 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
  have hp2 : p ≠ 2 := ho.ne_two_of_dvd_nat hpn
  have hc : p - 1 < Nat.choose (209 + k) k * target030Seed373Row14.getD A 0 :=
    (Nat.sub_lt hp.pos (by decide : 0 < 1)).trans_le hpC
  exact
    exists_prime_reject_prime_pow_count hn ho hp hp2 (by decide : 0 < 2) hdiv
      target030Seed1849Primes target030Seed1849Weights 1849 (A + k * 76)
      (Nat.choose (209 + k) k * target030Seed373Row14.getD A 0) target030Seed1849Weight 10
      (by norm_num only) target030Seed1849_labels.1
      (fun r hr ↦ (target030Seed1849_prime_supply r hr).1)
      (fun r hr ↦ (target030Seed1849_prime_supply r hr).2) target030Seed1849_labels.2.2
      target030Seed1849_weight_bounds target030Seed1849_labels.2.1 hbudget hc
      (target030Seed1849_group_lower A k hA)

end PseudoPrime.PrimeTestBounds.MillerRabin

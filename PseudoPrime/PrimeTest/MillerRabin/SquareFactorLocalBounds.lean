/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.LocalFermatIndexSize

/-! # Prime-square local arithmetic for finite-index MR bounds -/

@[expose] public section

namespace PseudoPrime.PrimeTest

/-- If an odd prime square divides n>1, the local (n-1)-power kernel at p²
has index at least p. The prime p cannot divide n-1, so the exact prime-power
image formula retains a factor p; the remaining gcd quotient is positive.
This controls the prime factor by the ambient finite subgroup index. -/
theorem prime_le_local_square_powerKernel_index {n p : ℕ} (hn : 1 < n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hdiv : p ^ 2 ∣ n) :
    p ≤ (powMonoidHom (n - 1) : (ZMod (p ^ 2))ˣ →* (ZMod (p ^ 2))ˣ).ker.index := by
  have hpn : p ∣ n := dvd_trans ⟨p, by rw [pow_two]⟩ hdiv
  have hpE : ¬p ∣ n - 1 := by
    intro hd
    have hone := Nat.dvd_sub hpn hd
    rw [Nat.sub_sub_self hn.le] at hone
    exact hp.ne_one (Nat.dvd_one.mp hone)
  have hi := NumberTheory.card_unitPowerImage_prime_pow_of_not_dvd hp hp2 (by decide : 0 < 2) hpE
  rw [Subgroup.index_ker, hi]
  norm_num only [pow_one]
  have hkg : (p - 1) / (p - 1).gcd (n - 1) * (p - 1).gcd (n - 1) = p - 1 :=
    Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
  have hk : 1 ≤ (p - 1) / (p - 1).gcd (n - 1) := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro hzero
    rw [hzero, zero_mul] at hkg
    exact Nat.sub_ne_zero_of_lt hp.one_lt hkg.symm
  exact (by rw [Nat.mul_one] : p = p * 1).trans_le (Nat.mul_le_mul_left p hk)

/-- For p≤10^9 and n≥10^141, the prime-square local modulus satisfies
(p²)²≤10^9*n. Compare fourth powers and use n≥10^27.
This supplies the explicit arithmetic size gate for the local LLS transfer. -/
theorem local_prime_square_size_of_finite_index {n p : ℕ} (hp : p ≤ 10 ^ 9) (hn : 10 ^ 141 ≤ n) :
    (p ^ 2) ^ 2 ≤ 10 ^ 9 * n := by
  have hb := Nat.pow_le_pow_left hp 4
  have hn27 : 10 ^ 27 ≤ n :=
    (Nat.pow_le_pow_right (by decide : 0 < 10) (by decide : 27 ≤ 141)).trans hn
  have hm := Nat.mul_le_mul_left (10 ^ 9) hn27
  rw [← pow_mul]
  norm_num only at hb hm ⊢
  exact hb.trans hm

end PseudoPrime.PrimeTest

/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.ProductFermatKernel
public import PseudoPrime.PrimeTestBounds.MillerRabin.UnbalancedProductBounds

/-! # Pointwise small MR bases from a local Fermat-kernel exponent -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Let p divide odd n>1. If 1<b<p and the local kernel exponent divides
positive g with b^g-1<p, then b rejects MR modulo n. A pass would give
order dividing gcd(p-1,n-1), hence b^g=1 modulo p, contradicting the size bound.
This is a pointwise criterion without GRH or asymptotic input. -/
theorem not_strongMillerRabinPass_of_local_power_bound {n p b g : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hpn : p ∣ n) (hb : 1 < b) (hbp : b < p) (hg : 0 < g)
    (hd : (p - 1).gcd (n - 1) ∣ g) (hsize : b ^ g - 1 < p) :
    ¬PrimeTest.StrongMillerRabinPass n (b : ZMod n) := by
  let : Fact p.Prime := ⟨hp⟩
  have hbzero : (b : ZMod p) ≠ 0 := by
    intro h
    exact
      (not_le_of_gt hbp)
        (Nat.le_of_dvd (Nat.zero_lt_of_lt hb) ((ZMod.natCast_eq_zero_iff b p).mp h))
  intro hpass
  have hlocal :=
    congrArg (ZMod.castHom hpn (ZMod p)) (PrimeTest.strongMillerRabinPass_pow hn ho hpass)
  simp only [map_pow, map_natCast, map_one] at hlocal
  have hord :=
    (Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hbzero))
          (orderOf_dvd_of_pow_eq_one hlocal)).trans
      hd
  have hpow : (b : ZMod p) ^ g = 1 := orderOf_dvd_iff_pow_eq_one.mp hord
  have hcast : ((b ^ g : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
    simpa only [Nat.cast_pow, Nat.cast_one] using hpow
  have hgt : 1 < b ^ g := Nat.one_lt_pow hg.ne' hb
  have hmod := (ZMod.natCast_eq_natCast_iff (b ^ g) 1 p).mp hcast
  have hdiv := (Nat.modEq_iff_dvd' hgt.le).mp hmod.symm
  exact (not_le_of_gt hsize) (Nat.le_of_dvd (Nat.sub_pos_of_lt hgt) hdiv)

/-- For odd prime p and odd m>p with 2^(m-p)-1<p, two is the least prime
MR witness for pm. The ambient local kernel divides the positive gap.
This closes the small-gap branch with no logarithmic threshold or GRH. -/
theorem two_is_least_prime_witness_of_close_product {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : Odd m) (hpm : p < m) (hsize : 2 ^ (m - p) - 1 < p) :
    Nat.Prime 2 ∧
      ¬PrimeTest.StrongMillerRabinPass (p * m) (2 : ZMod (p * m)) ∧
      ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass (p * m) (r : ZMod (p * m)) → 2 ≤ r := by
  have hm0 := hp.pos.trans hpm
  have hn : 1 < p * m := hp.one_lt.trans_le (Nat.le_mul_of_pos_right p hm0)
  have hf :=
    not_strongMillerRabinPass_of_local_power_bound hn ((hp.odd_of_ne_two hp2).mul hm) hp
      (dvd_mul_right p m) (by decide) (lt_of_le_of_ne hp.two_le hp2.symm) (Nat.sub_pos_of_lt hpm)
      (NumberTheory.gcd_predecessor_product_dvd_gap hp.pos hpm) hsize
  exact ⟨Nat.prime_two, hf, fun r hr _ ↦ hr.two_le⟩

/-- For every odd prime p, the least prime MR witness for p(p+2) is two.
For p>3 the gap criterion is 3<p; reuse the proved 3*5 case at p=3.
Primality of p+2 is unnecessary, so the statement covers the twin-prime subfamily. -/
theorem two_is_least_prime_witness_prime_mul_add_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Nat.Prime 2 ∧
      ¬PrimeTest.StrongMillerRabinPass (p * (p + 2)) (2 : ZMod (p * (p + 2))) ∧
      ∀ r : ℕ,
        r.Prime →
          ¬PrimeTest.StrongMillerRabinPass (p * (p + 2)) (r : ZMod (p * (p + 2))) → 2 ≤ r := by
  by_cases hp3 : p = 3
  · subst p
    exact two_is_least_prime_witness_three_mul (by decide : Nat.Prime 5) (by decide)
  have hgt : 3 < p := lt_of_lt_of_le (by decide : 3 < 5) (hp.five_le_of_ne_two_of_ne_three hp2 hp3)
  apply
    two_is_least_prime_witness_of_close_product hp hp2
      ((hp.odd_of_ne_two hp2).add_even (by decide : Even 2))
      (Nat.lt_add_of_pos_right (by decide : 0 < 2))
  simpa only [Nat.add_sub_cancel_left, show (2 : ℕ) ^ 2 - 1 = 3 by decide] using hgt

end PseudoPrime.PrimeTestBounds.MillerRabin

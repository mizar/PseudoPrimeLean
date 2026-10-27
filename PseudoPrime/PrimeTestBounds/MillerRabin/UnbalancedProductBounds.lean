/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
public import Mathlib.FieldTheory.Finite.Basic

/-! # Unconditional small witnesses for unbalanced odd products -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For odd p>1 and odd prime q, a base 1<b<q with b^(p-1)-1<q
rejects the strong test modulo p*q. Reduce the Fermat equation modulo q,
use n-1=p(q-1)+(p-1), and compare the remaining natural power with q.
Primality of p and GRH are unnecessary. -/
theorem not_strongMillerRabinPass_of_unbalanced_product {p q b : ℕ} (hp : 1 < p) (hpo : Odd p)
    (hq : q.Prime) (hqo : Odd q) (hb : 1 < b) (hbq : b < q) (hsize : b ^ (p - 1) - 1 < q) :
    ¬PrimeTest.StrongMillerRabinPass (p * q) (b : ZMod (p * q)) := by
  let : Fact q.Prime := ⟨hq⟩
  have hpow1 : 1 < b ^ (p - 1) :=
    hb.trans_le (le_self_pow₀ hb.le (Nat.ne_of_gt (Nat.sub_pos_of_lt hp)))
  have hbzero : (b : ZMod q) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff b q).mp h
    exact (not_le_of_gt hbq) (Nat.le_of_dvd (Nat.zero_lt_of_lt hb) hd)
  have hfermat := ZMod.pow_card_sub_one_eq_one hbzero
  have he : p * q - 1 = (q - 1) * p + (p - 1) := by
    have hsp := Nat.sub_add_cancel hp.le
    have hsq := Nat.sub_add_cancel hq.one_lt.le
    have hsn := Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.mul_pos (Nat.zero_lt_of_lt hp) hq.pos))
    nlinarith only [hsp, hsq, hsn]
  intro hpass
  have hn : 1 < p * q := lt_of_lt_of_le hp (Nat.le_mul_of_pos_right p hq.pos)
  have hlocal :=
    congrArg (ZMod.castHom (dvd_mul_left q p) (ZMod q))
      (PrimeTest.strongMillerRabinPass_pow hn (hpo.mul hqo) hpass)
  simp only [map_pow, map_natCast, map_one] at hlocal
  rw [he, pow_add, pow_mul, hfermat, one_pow, one_mul] at hlocal
  have hcast : ((b ^ (p - 1) : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by
    simpa only [Nat.cast_pow, Nat.cast_one] using hlocal
  have hm := (ZMod.natCast_eq_natCast_iff (b ^ (p - 1)) 1 q).mp hcast
  have hd := (Nat.modEq_iff_dvd' hpow1.le).mp hm.symm
  exact (not_le_of_gt hsize) (Nat.le_of_dvd (Nat.sub_pos_of_lt hpow1) hd)

/-- For odd p>1 and odd prime q>2^(p-1)-1, base two rejects modulo p*q.
Specialize the general small-base lemma; primality of p is unnecessary.
This proves the unbalanced-product family without GRH. -/
theorem not_strongMillerRabinPass_two_of_unbalanced_product {p q : ℕ} (hp : 1 < p) (hpo : Odd p)
    (hq : q.Prime) (hq2 : q ≠ 2) (hsize : 2 ^ (p - 1) - 1 < q) :
    ¬PrimeTest.StrongMillerRabinPass (p * q) (2 : ZMod (p * q)) := by
  exact
    not_strongMillerRabinPass_of_unbalanced_product hp hpo hq (hq.odd_of_ne_two hq2) (by decide)
      (lt_of_le_of_ne hq.two_le hq2.symm) hsize

/-- In the unbalanced-product family, two is the least prime MR witness.
Use the proved rejection and the lower bound two for every prime.
No asymptotic range or analytic hypothesis remains. -/
theorem two_is_least_prime_witness_of_unbalanced_product {p q : ℕ} (hp : 1 < p) (hpo : Odd p)
    (hq : q.Prime) (hq2 : q ≠ 2) (hsize : 2 ^ (p - 1) - 1 < q) :
    Nat.Prime 2 ∧
      ¬PrimeTest.StrongMillerRabinPass (p * q) (2 : ZMod (p * q)) ∧
      ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass (p * q) (r : ZMod (p * q)) → 2 ≤ r := by
  exact
    ⟨Nat.prime_two, not_strongMillerRabinPass_two_of_unbalanced_product hp hpo hq hq2 hsize,
      fun r hr _ ↦ hr.two_le⟩

/-- For every prime q>3, the least prime MR witness for 3q is two.
The general product-size condition reduces to q>3.
This handles an infinite squarefree family without GRH or finite certificates. -/
theorem two_is_least_prime_witness_three_mul {q : ℕ} (hq : q.Prime) (hq3 : 3 < q) :
    Nat.Prime 2 ∧
      ¬PrimeTest.StrongMillerRabinPass (3 * q) (2 : ZMod (3 * q)) ∧
      ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass (3 * q) (r : ZMod (3 * q)) → 2 ≤ r := by
  apply
    two_is_least_prime_witness_of_unbalanced_product (by decide : 1 < 3) (by decide : Odd 3) hq
      (Nat.ne_of_gt ((by decide : 2 < 3).trans hq3))
  norm_num only
  exact hq3

end PseudoPrime.PrimeTestBounds.MillerRabin

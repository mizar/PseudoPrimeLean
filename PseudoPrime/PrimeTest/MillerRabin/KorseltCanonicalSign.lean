/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.KorseltHalfExponent
public import PseudoPrime.PrimeTest.MillerRabin.PairedQuadraticAnnihilator

/-! # Canonical sign exponents from Korselt odd parts

Local half-exponent factorizations and paired annihilator membership do not
require equality with the ambient predecessor two-adic valuation.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/-- For odd p,n greater than one, Korselt divisibility implies that the odd
part of n-1 is an odd multiple of that of p-1. Cancel the coprime power of two,
then use oddness of the ambient odd part. This supplies local sign exponents. -/
theorem odd_part_korselt {p n : ℕ} (hp : 1 < p) (hpOdd : Odd p) (hn : 1 < n) (hnOdd : Odd n)
    (hdiv : p - 1 ∣ n - 1) :
    ∃ k : ℕ, Odd k ∧ Nat.divMaxPow (n - 1) 2 = Nat.divMaxPow (p - 1) 2 * k := by
  obtain ⟨_, ha, hpFac⟩ := odd_sub_canonical_decomp hp hpOdd
  obtain ⟨_, hd, hnFac⟩ := odd_sub_canonical_decomp hn hnOdd
  have haDiv : Nat.divMaxPow (p - 1) 2 ∣ p - 1 :=
    ⟨2 ^ padicValNat 2 (p - 1), Nat.divMaxPow_mul_pow_padicValNat 2 (p - 1) |>.symm⟩
  have htarget : Nat.divMaxPow (p - 1) 2 ∣ 2 ^ padicValNat 2 (n - 1) * Nat.divMaxPow (n - 1) 2 :=
    hnFac ▸ haDiv.trans hdiv
  obtain ⟨k, hk⟩ := (ha.coprime_two_right.pow_right _).dvd_of_dvd_mul_left htarget
  exact ⟨k, (Nat.odd_mul.mp (hk ▸ hd)).2, hk⟩

/-- Under Korselt divisibility for odd p,n greater than one, the canonical
sign exponent based on p is an odd multiple of p/2. Factor the odd parts and
divide the local two-adic decomposition by two. Ambient and local two-adic
valuations need not agree. This is used for the uniform-valuation branch. -/
theorem canonical_sign_exponent_local_half {p n : ℕ} (hp : 1 < p) (hpOdd : Odd p) (hn : 1 < n)
    (hnOdd : Odd n) (hdiv : p - 1 ∣ n - 1) :
    ∃ k : ℕ, Odd k ∧ 2 ^ (padicValNat 2 (p - 1) - 1) * Nat.divMaxPow (n - 1) 2 = (p / 2) * k := by
  obtain ⟨k, hkOdd, hk⟩ := odd_part_korselt hp hpOdd hn hnOdd hdiv
  refine ⟨k, hkOdd, ?_⟩
  rw [hk, ← mul_assoc, ← half_exponent_eq_canonical_sign_exponent hp hpOdd]
  have hhalf : (p - 1) / 2 = p / 2 := by
    obtain ⟨j, hj⟩ := hpOdd
    rw [hj, Nat.add_sub_cancel_right, Nat.mul_add_div (by decide : 0 < 2)]
    simp only [Nat.div_eq_of_lt (by decide : 1 < 2), Nat.add_zero,
      Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  exact congrArg (fun x : ℕ ↦ x * k) hhalf

/-- For two odd prime divisors satisfying Korselt divisibility and equal
predecessor two-adic valuations, their paired quadratic character annihilates
the canonical sign subgroup. Construct both odd local half-exponent factors
internally. This supplies the paired character for the four-factor branch. -/
theorem paired_quadraticCharacter_mem_canonical_sign_annihilator {n p q : ℕ} [NeZero n]
    [Fact p.Prime] [Fact q.Prime] [Fact (2 < p)] [Fact (2 < q)] (hn : 1 < n) (hnOdd : Odd n)
    (hpOdd : Odd p) (hqOdd : Odd q) (hpn : p ∣ n) (hqn : q ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hv : padicValNat 2 (q - 1) = padicValNat 2 (p - 1)) :
    (NumberTheory.complexJacobiNumeratorCharacter p hpOdd).changeLevel hpn *
        (NumberTheory.complexJacobiNumeratorCharacter q hqOdd).changeLevel hqn ∈
      NumberTheory.subgroupAnnihilator
        (signSubgroup n (2 ^ (padicValNat 2 (p - 1) - 1) * Nat.divMaxPow (n - 1) 2)) := by
  obtain ⟨kp, hkp, hEp⟩ :=
    canonical_sign_exponent_local_half (Fact.out : p.Prime).one_lt hpOdd hn hnOdd hpK
  obtain ⟨kq, hkq, hEq⟩ :=
    canonical_sign_exponent_local_half (Fact.out : q.Prime).one_lt hqOdd hn hnOdd hqK
  rw [hv] at hEq
  exact paired_quadraticCharacter_mem_signSubgroup_annihilator hpOdd hqOdd hpn hqn hkp hkq hEp hEq

end PseudoPrime.PrimeTest

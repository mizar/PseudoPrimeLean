/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Construction
public import PseudoPrime.PrimeTest.MillerRabin.WitnessSubgroup

/-! # Korselt half exponents and canonical sign-subgroup containment

Korselt divisibility gives local half-exponent factorizations.
Equal two-adic valuations identify the ambient half exponent with the
canonical sign exponent and transport every strong pass into that subgroup.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/-- For an odd local modulus p with p-1 dividing n-1, the ambient half exponent
equals p/2 times the Korselt quotient. Double the local half exponent and
cancel the division by two. This supplies the local exponent factorization. -/
theorem half_exponent_eq_local_half_mul_korselt_quotient {p n : ℕ} (hpOdd : Odd p)
    (hdiv : p - 1 ∣ n - 1) : (n - 1) / 2 = (p / 2) * ((n - 1) / (p - 1)) := by
  have hp2 : p / 2 * 2 = p - 1 := by
    obtain ⟨k, hk⟩ := hpOdd
    rw [hk, Nat.mul_add_div (by decide : 0 < 2)]
    simp only [Nat.div_eq_of_lt (by decide : 1 < 2), Nat.add_zero]
    rw [Nat.add_sub_cancel_right]
    exact Nat.mul_comm k 2
  have hnfac : n - 1 = (p - 1) * ((n - 1) / (p - 1)) := (Nat.mul_div_cancel' hdiv).symm
  calc
    (n - 1) / 2 = ((p - 1) * ((n - 1) / (p - 1))) / 2 := congrArg (fun x : ℕ ↦ x / 2) hnfac
    _ = (((p / 2) * ((n - 1) / (p - 1))) * 2) / 2 := by
      rw [← hp2]
      ring_nf
    _ = (p / 2) * ((n - 1) / (p - 1)) := Nat.mul_div_cancel _ (by decide)

/-- For odd n>1, the canonical last negative-stage exponent is (n-1)/2.
Use the canonical two-adic decomposition and divide its positive power of two.
This connects the canonical MR sign exponent to the local half-exponent arithmetic. -/
theorem half_exponent_eq_canonical_sign_exponent {n : ℕ} (hn : 1 < n) (hnOdd : Odd n) :
    (n - 1) / 2 = 2 ^ (padicValNat 2 (n - 1) - 1) * Nat.divMaxPow (n - 1) 2 := by
  obtain ⟨hs, _, hd⟩ := odd_sub_canonical_decomp hn hnOdd
  have he : padicValNat 2 (n - 1) - 1 + 1 = padicValNat 2 (n - 1) := Nat.sub_add_cancel hs
  have hpow : 2 ^ padicValNat 2 (n - 1) = 2 ^ (padicValNat 2 (n - 1) - 1) * 2 := by
    conv_lhs => rw [← he, pow_succ]
  calc
    (n - 1) / 2 = (2 ^ padicValNat 2 (n - 1) * Nat.divMaxPow (n - 1) 2) / 2 :=
      congrArg (fun x : ℕ ↦ x / 2) hd
    _ = ((2 ^ (padicValNat 2 (n - 1) - 1) * Nat.divMaxPow (n - 1) 2) * 2) / 2 := by
      rw [hpow]
      ring_nf
    _ = _ := Nat.mul_div_cancel _ (by decide)

/-- If a prime divisor's predecessor has the same two-adic valuation as n-1,
every strong MR pass lies in the half-exponent sign subgroup. Identify the
canonical local sign exponent with the ambient half exponent, then apply the
existing prime-factor sign-subgroup containment. This removes the pass premise
from the equal-valuation three-prime Gaussian branch. -/
theorem strongMillerRabinPass_mem_half_signSubgroup_of_equal_twoAdic {n p : ℕ} {x : ZMod n}
    (hn : 1 < n) (hnOdd : Odd n) (hp : p.Prime) (hpOdd : Odd p) (hpn : p ∣ n)
    (hval : padicValNat 2 (p - 1) = padicValNat 2 (n - 1)) (hpass : StrongMillerRabinPass n x) :
    ∃ u : (ZMod n)ˣ, u ∈ signSubgroup n ((n - 1) / 2) ∧ (u : ZMod n) = x := by
  have hhalf := half_exponent_eq_canonical_sign_exponent hn hnOdd
  rw [← hval] at hhalf
  obtain ⟨u, hu, hx⟩ := strongMillerRabinPass_mem_signSubgroup hn hnOdd hpass hp hpOdd hpn
  rw [← hhalf] at hu
  exact ⟨u, hu, hx⟩

end PseudoPrime.PrimeTest

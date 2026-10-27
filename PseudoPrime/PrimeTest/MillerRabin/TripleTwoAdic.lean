/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Construction

/-! # Equal two-adic predecessor valuations for three odd factors

An odd triple with the same positive predecessor valuation preserves that
valuation in the product predecessor. This removes the ambient valuation
premises of the Korselt three-prime Gaussian branch.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/-- Three factors 1+2^t*d with odd d and positive t have product predecessor
of valuation t. Factor the predecessor by 2^t; the remaining polynomial is odd.
This is the algebraic parity step behind the actual three-factor valuation theorem. -/
theorem twoAdic_triple_pred_of_odd_parts {p q r t dp dq dr : ℕ} (ht : 0 < t)
    (hp : p = 2 ^ t * dp + 1) (hq : q = 2 ^ t * dq + 1) (hr : r = 2 ^ t * dr + 1) (hdp : Odd dp)
    (hdq : Odd dq) (hdr : Odd dr) : padicValNat 2 (p * q * r - 1) = t := by
  let C := dp + dq + dr + 2 ^ t * (dp * dq + dp * dr + dq * dr) + (2 ^ t) ^ 2 * (dp * dq * dr)
  have hpow : 2 ^ t = 2 * 2 ^ (t - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel ht, pow_succ]
    exact Nat.mul_comm _ _
  have hC : Odd C := by
    obtain ⟨a, ha⟩ := hdp
    obtain ⟨b, hb⟩ := hdq
    obtain ⟨c, hc⟩ := hdr
    refine
      ⟨a + b + c + 1 + 2 ^ (t - 1) * (dp * dq + dp * dr + dq * dr) +
          2 * (2 ^ (t - 1)) ^ 2 * (dp * dq * dr),
        ?_⟩
    dsimp only [C]
    rw [hpow]
    nlinarith only [ha, hb, hc]
  have hprod : p * q * r = 2 ^ t * C + 1 := by
    rw [hp, hq, hr]
    dsimp only [C]
    ring
  rw [hprod, Nat.add_sub_cancel_right,
    padicValNat.mul (pow_ne_zero t (by decide : (2 : ℕ) ≠ 0)) hC.pos.ne', padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hC.not_two_dvd_nat, Nat.add_zero]

/-- Three odd numbers greater than one with equal predecessor two-adic
valuations have product predecessor of the same valuation. Apply their
canonical odd decompositions and the odd-part polynomial identity.
This identifies the ambient MR exponent with all three local sign exponents. -/
theorem twoAdic_triple_pred_eq_of_equal_predecessor_valuations {p q r : ℕ} (hp : 1 < p) (hq : 1 < q)
    (hr : 1 < r) (hpOdd : Odd p) (hqOdd : Odd q) (hrOdd : Odd r)
    (hpq : padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hpr : padicValNat 2 (p - 1) = padicValNat 2 (r - 1)) :
    padicValNat 2 (p * q * r - 1) = padicValNat 2 (p - 1) := by
  obtain ⟨ht, hdp, hpdec⟩ := odd_sub_canonical_decomp hp hpOdd
  obtain ⟨_, hdq, hqdec⟩ := odd_sub_canonical_decomp hq hqOdd
  obtain ⟨_, hdr, hrdec⟩ := odd_sub_canonical_decomp hr hrOdd
  rw [← hpq] at hqdec
  rw [← hpr] at hrdec
  have heq :
    ∀ m d : ℕ,
      1 < m → m - 1 = 2 ^ padicValNat 2 (p - 1) * d → m = 2 ^ padicValNat 2 (p - 1) * d + 1 := by
    intro m d hm hd
    have h := congrArg (fun x : ℕ ↦ x + 1) hd
    rw [Nat.sub_add_cancel (Nat.le_of_lt hm)] at h
    exact h
  exact
    twoAdic_triple_pred_of_odd_parts ht (heq p _ hp hpdec) (heq q _ hq hqdec) (heq r _ hr hrdec) hdp
      hdq hdr

end PseudoPrime.PrimeTest

/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Nat.PadicValNat
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-! # Odd parts and gcd identities for two-adic decomposition -/

@[expose] public section

namespace PseudoPrime.NumberTheory.TwoAdic

/--
For a nonzero numerator, removing all factors of two leaves a positive odd part.
The factorization identity excludes zero; reciprocity uses this positive divisor.
-/
theorem oddPart_pos (a : ℕ) (ha : a ≠ 0) : 0 < Nat.divMaxPow a 2 := by
  apply Nat.pos_of_ne_zero
  intro hz
  have h := Nat.divMaxPow_mul_pow_padicValNat 2 a
  rw [hz, zero_mul] at h
  exact ha h.symm

/--
For a nonzero numerator, its odd part is at most the original numerator.
Divisibility supplies the bound required by the divisor-reducing Fibonacci interface.
-/
theorem oddPart_le (a : ℕ) (ha : a ≠ 0) : Nat.divMaxPow a 2 ≤ a :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero ha)
    ⟨2 ^ padicValNat 2 a, (Nat.divMaxPow_mul_pow_padicValNat 2 a).symm⟩

/--
For a nonzero numerator, its maximal-power quotient is odd.
Maximality excludes divisibility by two, so the next Jacobi modulus remains odd.
-/
theorem oddPart_odd (a : ℕ) (ha : a ≠ 0) : Nat.divMaxPow a 2 % 2 = 1 := by
  apply Nat.mod_two_ne_zero.mp
  intro he
  exact Nat.not_dvd_divMaxPow (by decide : 1 < 2) ha (Nat.dvd_iff_mod_eq_zero.mpr he)

/-- Removing the numerator's maximal two-power leaves the gcd unchanged for an odd denominator.
Coprimality with every power of two and the maximal-power factorization give this identity.
It certifies the gcd component of a shared batched round. -/
theorem gcd_oddPart_right (c m : ℕ) (hc : Odd c) : Nat.gcd c (Nat.divMaxPow m 2) = Nat.gcd c m := by
  exact
    (Nat.Coprime.gcd_mul_right_cancel_right (Nat.divMaxPow m 2)
          ((hc.coprime_two_right.pow_right (padicValNat 2 m)).symm)).symm.trans
      (congrArg (Nat.gcd c) (Nat.divMaxPow_mul_pow_padicValNat 2 m))

/-- When the first two-adic exponent is smaller, factor it out of the gcd.
The residual two-power is coprime to the odd first operand.
This supplies one branch of the symmetric restoration identity. -/
theorem gcd_two_pow_mul_odd_of_le (alpha beta A N : ℕ) (hA : Odd A) (hab : alpha ≤ beta) :
    Nat.gcd (2 ^ alpha * A) (2 ^ beta * N) = 2 ^ alpha * Nat.gcd A N := by
  have hp : 2 ^ beta = 2 ^ alpha * 2 ^ (beta - alpha) :=
    (congrArg (fun k : ℕ ↦ 2 ^ k) (Nat.add_sub_of_le hab).symm).trans
      (pow_add 2 alpha (beta - alpha))
  rw [hp, mul_assoc, Nat.gcd_mul_left]
  exact
    congrArg (fun k ↦ 2 ^ alpha * k)
      (Nat.Coprime.gcd_mul_left_cancel_right N
        ((hA.coprime_two_right.pow_right (beta - alpha)).symm))

/-- Extracting a common power of two leaves the gcd of the odd parts.
Both residual operands are odd; after factoring the smaller exponent, the remaining
power of two is coprime to the opposite operand. This restores the exact integer gcd. -/
theorem gcd_two_pow_mul_odd (alpha beta A N : ℕ) (hA : Odd A) (hN : Odd N) :
    Nat.gcd (2 ^ alpha * A) (2 ^ beta * N) = 2 ^ min alpha beta * Nat.gcd A N := by
  exact
    if hab : alpha ≤ beta then
      (show _ by
        rw [Nat.min_eq_left hab]
        exact gcd_two_pow_mul_odd_of_le alpha beta A N hA hab)
    else
      (show _ by
        rw [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge hab)), Nat.gcd_comm (2 ^ alpha * A),
          gcd_two_pow_mul_odd_of_le beta alpha N A hN (Nat.le_of_lt (Nat.lt_of_not_ge hab)),
          Nat.gcd_comm N A])

/-- Nonzero integer inputs admit exact gcd restoration from their odd parts.
Maximal two-power factorization reduces this statement to the common-power identity.
This gives the second component of the executable integer entry point. -/
theorem gcd_natAbs_two_adic (a n : ℤ) (ha : a ≠ 0) (hn : n ≠ 0) :
    Nat.gcd a.natAbs n.natAbs =
      2 ^ min (padicValNat 2 a.natAbs) (padicValNat 2 n.natAbs) *
        Nat.gcd (Nat.divMaxPow a.natAbs 2) (Nat.divMaxPow n.natAbs 2) := by
  have h :=
    gcd_two_pow_mul_odd (padicValNat 2 a.natAbs) (padicValNat 2 n.natAbs) (Nat.divMaxPow a.natAbs 2)
      (Nat.divMaxPow n.natAbs 2)
      (Nat.odd_iff.mpr (oddPart_odd a.natAbs (Int.natAbs_ne_zero.mpr ha)))
      (Nat.odd_iff.mpr (oddPart_odd n.natAbs (Int.natAbs_ne_zero.mpr hn)))
  simpa only [Nat.pow_padicValNat_mul_divMaxPow] using h

/-- An odd natural denominator has no two-power factor.
Nondivisibility by two makes its valuation zero; maximal-power factorization then
identifies the odd quotient with the original denominator. -/
theorem odd_decomposition (N : ℕ) (hN : Odd N) : padicValNat 2 N = 0 ∧ Nat.divMaxPow N 2 = N := by
  have he := padicValNat.eq_zero_of_not_dvd (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hN))
  exact
    ⟨he,
      (show Nat.divMaxPow N 2 = N by
        simpa only [he, pow_zero, one_mul] using Nat.pow_padicValNat_mul_divMaxPow 2 N)⟩

end PseudoPrime.NumberTheory.TwoAdic

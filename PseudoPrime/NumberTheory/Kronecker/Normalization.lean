/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Jacobi.Normalization
public import PseudoPrime.NumberTheory.Jacobi.Sign
public import PseudoPrime.NumberTheory.Kronecker.Basic
public import PseudoPrime.NumberTheory.Kronecker.Sign

/-! # Two-adic normalization for simultaneous Kronecker and gcd computation -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- Coefficient accumulated before the shared odd Jacobi-and-gcd trajectory.
The denominator sign, negative-numerator correction, and both two-power factors account
for the removed signs and powers. A zero coefficient does not terminate gcd computation. -/
def kroneckerNormalizationSign (a n : ℤ) (alpha beta N : ℕ) : ℤ :=
  kroneckerDenominatorSign a n * (if a < 0 ∧ N % 4 = 3 then -1 else 1) *
    Jacobi.twoPowerSign N alpha *
    kroneckerTwoPowerFactor a beta

/-- At a nonzero denominator, the normalized coefficient recovers the Kronecker symbol.
The independent specification and signed numerator factorization identify the odd-part value.
This proves the symbol component without using the executable trajectory. -/
theorem kroneckerSym_two_adic (a n : ℤ) (hn : n ≠ 0) :
    kroneckerSym a n =
      kroneckerNormalizationSign a n (padicValNat 2 a.natAbs) (padicValNat 2 n.natAbs)
          (Nat.divMaxPow n.natAbs 2) *
        jacobiSym (Nat.divMaxPow a.natAbs 2 : ℤ) (Nat.divMaxPow n.natAbs 2) := by
  rw [kroneckerSym, ite_eq_right hn,
    jacobiSym_two_adic_left a (Nat.divMaxPow n.natAbs 2)
      (Nat.odd_iff.mpr (TwoAdic.oddPart_odd n.natAbs (Int.natAbs_ne_zero.mpr hn)))]
  dsimp only [kroneckerNormalizationSign]
  rw [Jacobi.twoPowerSign_eq, kroneckerTwoPowerFactor_eq]
  ac_rfl

/-- A zero numerator gives symbol one precisely at denominator absolute value one.
The two-power and odd-denominator factors recombine into the natural Jacobi symbol.
This certifies the direct zero-numerator branch of the executable entry point. -/
theorem kroneckerSym_zero_left (n : ℤ) (hn : n ≠ 0) :
    kroneckerSym 0 n = (if n.natAbs = 1 then 1 else 0) := by
  let : NeZero (Nat.divMaxPow n.natAbs 2) :=
    ⟨Nat.ne_of_gt (TwoAdic.oddPart_pos n.natAbs (Int.natAbs_ne_zero.mpr hn))⟩
  rw [kroneckerSym, ite_eq_right hn]
  simp only [kroneckerDenominatorSign, kroneckerAtTwo, Int.lt_irrefl, false_and, ite_false,
    Int.zero_emod, ite_true, one_mul]
  change (0 : ℤ) ^ padicValNat 2 n.natAbs * jacobiSym 0 (Nat.divMaxPow n.natAbs 2) = _
  nth_rw 1 [← (jacobiSym.zero_left (by decide : 1 < 2))]
  rw [← jacobiSym.pow_right, ← jacobiSym.mul_right, Nat.pow_padicValNat_mul_divMaxPow]
  exact
    if h : n.natAbs = 1 then (show _ by simp only [h, jacobiSym.one_right, ite_true])
    else
      (show _ by
        rw [ite_eq_right h]
        exact
          jacobiSym.zero_left
            (Nat.lt_of_le_of_ne (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hn)) (Ne.symm h)))

/-- On odd natural denominators, the Kronecker specification is the usual Jacobi symbol.
The denominator is positive, its sign is trivial, and its two-adic exponent is zero.
This is the specification-level compatibility needed by existing odd-modulus consumers. -/
theorem kroneckerSym_eq_jacobiSym (a : ℤ) (N : ℕ) (hN : Odd N) :
    kroneckerSym a (N : ℤ) = jacobiSym a N := by
  have hz : N ≠ 0 := Nat.ne_of_gt hN.pos
  rw [kroneckerSym, ite_eq_right (Int.natCast_ne_zero.mpr hz)]
  simp only [kroneckerDenominatorSign, Int.not_lt_of_ge (Int.natCast_nonneg N), and_false,
    ite_false, Int.natAbs_natCast, (TwoAdic.odd_decomposition N hN).1,
    (TwoAdic.odd_decomposition N hN).2, pow_zero, one_mul]

end PseudoPrime.NumberTheory

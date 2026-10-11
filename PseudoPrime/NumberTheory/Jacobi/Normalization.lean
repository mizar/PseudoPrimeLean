/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Jacobi.Computation

/-! # Sign and two-power decompositions of the Jacobi symbol -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- The sign of an integer numerator contributes the mod-four Jacobi factor.
At an odd denominator, the certified signed reference procedure identifies this factor.
This separates sign handling from two-adic normalization. -/
theorem jacobiSym_signed_natAbs (a : ℤ) (N : ℕ) (hN : Odd N) :
    jacobiSym a N = (if a < 0 ∧ N % 4 = 3 then -1 else 1) * jacobiSym (a.natAbs : ℤ) N := by
  have h := Jacobi.jacobiSigned_eq a N (Nat.odd_iff.mp hN)
  rw [Jacobi.jacobiSigned, Jacobi.jacobiNat_eq _ _ (Nat.odd_iff.mp hN)] at h
  exact h.symm

/-- Extracting the numerator's two-power contributes the mod-eight Jacobi factor.
The natural maximal-power factorization and multiplicativity identify the odd-part value.
This identity retains the sign correction for negative integer numerators. -/
theorem jacobiSym_two_adic_left (a : ℤ) (N : ℕ) (hN : Odd N) :
    jacobiSym a N =
      (if a < 0 ∧ N % 4 = 3 then -1 else 1) *
        (if N % 8 = 3 ∨ N % 8 = 5 then (-1 : ℤ) else 1) ^ padicValNat 2 a.natAbs *
        jacobiSym (Nat.divMaxPow a.natAbs 2 : ℤ) N := by
  rw [jacobiSym_signed_natAbs a N hN]
  nth_rw 1 [← Nat.pow_padicValNat_mul_divMaxPow 2 a.natAbs]
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, jacobiSym.mul_left, jacobiSym.pow_left,
    Jacobi.jacobiSign2 N (Nat.odd_iff.mp hN), mul_assoc]

/-- The natural Jacobi specification splits into two-power and odd-denominator factors.
A positive denominator and maximal-power factorization justify multiplicativity.
This isolates the sole extra factor needed for Kronecker compatibility. -/
theorem jacobiSym_two_adic_right (a : ℤ) (n : ℕ) (hn : 0 < n) :
    jacobiSym a n = jacobiSym a 2 ^ padicValNat 2 n * jacobiSym a (Nat.divMaxPow n 2) := by
  nth_rw 1 [← Nat.pow_padicValNat_mul_divMaxPow 2 n]
  rw [jacobiSym.mul_right' a (Nat.ne_of_gt (Nat.pow_pos (by decide : 0 < 2)))
      (Nat.ne_of_gt (TwoAdic.oddPart_pos n (Nat.ne_of_gt hn))),
    jacobiSym.pow_right]

end PseudoPrime.NumberTheory

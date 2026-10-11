/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Kronecker.Normalization

/-! # Compatibility of the Kronecker and natural-denominator Jacobi specifications -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- Squaring the Kronecker factor at two gives the natural Jacobi value at denominator two.
The even numerator branch is zero; odd numerators give one after squaring either sign.
This accounts for the difference between the two symbols at even denominators. -/
theorem kroneckerAtTwo_sq_eq_jacobiSym_two (a : ℤ) : kroneckerAtTwo a ^ 2 = jacobiSym a 2 := by
  rw [jacobiSym.mod_left a 2]
  simp only [Nat.cast_ofNat]
  exact
    if ha : a % 2 = 0 then
      (show _ by
        simp only [kroneckerAtTwo, ha, ite_true, zero_pow (by decide : (2 : ℕ) ≠ 0),
          jacobiSym.zero_left (by decide : 1 < 2)])
    else
      (show _ by
        rw [Or.resolve_left (Int.emod_two_eq_zero_or_one a) ha, jacobiSym.one_left]
        simp only [kroneckerAtTwo, ha, ite_false, ite_pow, neg_one_sq, one_pow, ite_self])

/-- The natural Jacobi symbol equals the Kronecker symbol with its factor-at-two repeated.
At positive natural denominators the denominator sign is trivial; squaring the Kronecker
factor converts it to the natural Jacobi factor at two. Zero denominator is excluded. -/
theorem jacobiSym_eq_kronecker (a : ℤ) (n : ℕ) (hn : 0 < n) :
    jacobiSym a n = kroneckerTwoPowerFactor a (padicValNat 2 n) * kroneckerSym a (n : ℤ) := by
  rw [kroneckerTwoPowerFactor_eq, kroneckerSym,
    ite_eq_right (Int.natCast_ne_zero.mpr (Nat.ne_of_gt hn))]
  simp only [kroneckerDenominatorSign, Int.not_lt_of_ge (Int.natCast_nonneg n), and_false,
    ite_false, one_mul, Int.natAbs_natCast]
  rw [← mul_assoc, ← mul_pow, ← pow_two, kroneckerAtTwo_sq_eq_jacobiSym_two]
  exact jacobiSym_two_adic_right a n hn

end PseudoPrime.NumberTheory

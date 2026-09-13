/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.NumberTheory.MulChar.Basic

/-!
# Parity expansion for quadratic multiplicative characters

For a quadratic multiplicative character with values in a commutative ring, nonzero powers
depend only on the parity of the exponent.
-/

namespace PseudoPrime.NumberTheory

/--
Input/assumptions: a quadratic multiplicative character and a nonzero exponent.
Conclusion: the value at a power reduces to the value itself when the exponent is odd, and to its
square when the exponent is even.
Content: a quadratic character takes values in `{0, 1, -1}`; raising any of these to an odd power
reproduces the base value, and to an even power reproduces its square.
Role: gives exact character values in prime-power sums without replacing them by norm bounds.
-/
theorem isQuadratic_pow_apply {M R : Type*} [CommMonoid M] [CommRing R] {χ : MulChar M R}
    (hχ : χ.IsQuadratic) (a : M) {k : ℕ} (hk : k ≠ 0) :
    χ a ^ k = if Odd k then χ a else χ a ^ 2 := by
  rcases hχ a with h0 | h1 | hm1
  · simp only [h0, zero_pow hk, zero_pow (n := 2) (by decide), ite_self]
  · simp only [h1, one_pow, ite_self]
  · rw [hm1]
    split_ifs with hodd
    · exact hodd.neg_one_pow
    · rw [Nat.not_odd_iff_even] at hodd
      rw [hodd.neg_one_pow]
      norm_num only

end PseudoPrime.NumberTheory

/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import PseudoPrime.PrimeTest.Selfridge.Candidates

/-!
# Selfridge reciprocity for PrimeTest

This module provides the unconditional Jacobi reciprocity identity for the
signed Selfridge discriminant.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
Signed Selfridge reciprocity for arbitrary odd natural `i` and `n`.
The conclusion is `jacobiSym (selfridgeD i) n = jacobiSym n i`; neither argument is assumed
prime or coprime. Split odd residues modulo four and combine ordinary quadratic reciprocity
with the sign correction in `selfridgeD`. This connects executable discriminant tests to
neutral witness sets whose numerator is `n`.
-/
theorem jacobi_selfridgeD {i n : ℕ} (hi : Odd i) (hn : Odd n) :
    jacobiSym (selfridgeD i) n = jacobiSym n i := by
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hi) with hi1 | hi3
  · rw [selfridgeD_of_mod_four_eq_one hi1]
    exact jacobiSym.quadratic_reciprocity_one_mod_four hi1 hn
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hn) with hn1 | hn3
  · rw [selfridgeD_of_mod_four_eq_three hi3, jacobiSym.neg (i : ℤ) hn, ZMod.χ₄_nat_one_mod_four hn1,
      one_mul]
    exact jacobiSym.quadratic_reciprocity_one_mod_four' hi hn1
  · rw [selfridgeD_of_mod_four_eq_three hi3, jacobiSym.neg (i : ℤ) hn,
      ZMod.χ₄_nat_three_mod_four hn3, neg_one_mul,
      jacobiSym.quadratic_reciprocity_three_mod_four hi3 hn3, neg_neg]

end PseudoPrime.PrimeTest

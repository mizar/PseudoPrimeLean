/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import PseudoPrime.PrimeTest.Selfridge.Candidates

/-!
# Selfridge reciprocity for PrimeTest

This module provides the unconditional Jacobi reciprocity identity for the
signed Selfridge discriminant.
-/

namespace PseudoPrime.PrimeTest

/-- The Selfridge sign converts quadratic reciprocity into `J(n | i)`. -/
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

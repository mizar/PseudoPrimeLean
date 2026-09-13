/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.PrimeTest.Lucas.Defs

/-! # Lucas sequence specifications -/

namespace PseudoPrime.PrimeTest

/-- Casting a Lucas `U` value to `ZMod` agrees with the dedicated definition. -/
theorem lucasUZMod_eq_cast (n : ℕ) (P Q : ℤ) (k : ℕ) :
    lucasUZMod n P Q k = (lucasU P Q k : ZMod n) := by rfl

/-- Casting a Lucas `V` value to `ZMod` agrees with the dedicated definition. -/
theorem lucasVZMod_eq_cast (n : ℕ) (P Q : ℤ) (k : ℕ) :
    lucasVZMod n P Q k = (lucasV P Q k : ZMod n) := by rfl

/-- The `ZMod` image of `U` satisfies the same recurrence. -/
theorem lucasUZMod_succ_succ (n : ℕ) (P Q : ℤ) (k : ℕ) :
    lucasUZMod n P Q (k + 2) =
      (P : ZMod n) * lucasUZMod n P Q (k + 1) - (Q : ZMod n) * lucasUZMod n P Q k := by
  change (lucasU P Q (k + 2) : ZMod n) = _
  rw [lucasU_succ_succ]
  simp only [lucasUZMod, Int.cast_mul, Int.cast_sub]

/-- The `ZMod` image of `V` satisfies the same recurrence. -/
theorem lucasVZMod_succ_succ (n : ℕ) (P Q : ℤ) (k : ℕ) :
    lucasVZMod n P Q (k + 2) =
      (P : ZMod n) * lucasVZMod n P Q (k + 1) - (Q : ZMod n) * lucasVZMod n P Q k := by
  change (lucasV P Q (k + 2) : ZMod n) = _
  rw [lucasV_succ_succ]
  simp only [lucasVZMod, Int.cast_mul, Int.cast_sub]

/-- The `ZMod` image preserves the `U` doubling identity. -/
theorem lucasUZMod_two_mul (n : ℕ) (P Q : ℤ) (k : ℕ) :
    lucasUZMod n P Q (2 * k) = lucasUZMod n P Q k * lucasVZMod n P Q k := by
  change (lucasU P Q (2 * k) : ZMod n) = _
  rw [lucasU_two_mul]
  simp only [lucasUZMod, lucasVZMod, Int.cast_mul]

/-- The `ZMod` image preserves the `U` doubling-plus-one identity. -/
theorem lucasUZMod_two_mul_add_one (n : ℕ) (P Q : ℤ) (k : ℕ) :
    lucasUZMod n P Q (2 * k + 1) =
      lucasUZMod n P Q (k + 1) ^ 2 - (Q : ZMod n) * lucasUZMod n P Q k ^ 2 := by
  change (lucasU P Q (2 * k + 1) : ZMod n) = _
  rw [lucasU_two_mul_add_one]
  simp only [lucasUZMod, Int.cast_sub, Int.cast_pow, Int.cast_mul]

/-- The `ZMod` image preserves the `V` doubling identity. -/
theorem lucasVZMod_two_mul (n : ℕ) (P Q : ℤ) (k : ℕ) :
    lucasVZMod n P Q (2 * k) = lucasVZMod n P Q k ^ 2 - 2 * (lucasQPow Q k : ZMod n) := by
  change (lucasV P Q (2 * k) : ZMod n) = _
  rw [lucasV_two_mul]
  simp only [lucasVZMod, Int.cast_sub, Int.cast_pow, Int.cast_mul, Int.cast_ofNat]

/-- The `ZMod` image preserves the `V` doubling-plus-one identity. -/
theorem lucasVZMod_two_mul_add_one (n : ℕ) (P Q : ℤ) (k : ℕ) :
    lucasVZMod n P Q (2 * k + 1) =
      lucasVZMod n P Q (k + 1) * lucasVZMod n P Q k - (P : ZMod n) * (lucasQPow Q k : ZMod n) := by
  change (lucasV P Q (2 * k + 1) : ZMod n) = _
  rw [lucasV_two_mul_add_one]
  simp only [lucasVZMod, Int.cast_sub, Int.cast_mul]

end PseudoPrime.PrimeTest

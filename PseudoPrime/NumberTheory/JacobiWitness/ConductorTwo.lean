/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.ConductorSupport
public import PseudoPrime.NumberTheory.JacobiCharacterArithmetic

/-! # Canonical quadratic conductor reduction for a nonzero value at two -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- For odd n, a nonzero canonical primitive value at two implies that the
quadratic conductor divides n. Remove 2^2 from divisibility into 4*n using the
generic support theorem. No nonsquare or discriminant certificate is required. -/
theorem primitiveQuadratic_conductor_dvd_of_two_ne_zero {n : ℕ} (hn : Odd n)
    (h2 : primitiveQuadraticCharacter n hn 2 ≠ 0) :
    (complexQuadraticCharacter n hn).conductor ∣ n := by
  let _ : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  have hd : 4 * n ∣ (2 : ℕ) ^ 2 * n := by
    norm_num only [Nat.reducePow]
    exact dvd_refl _
  exact
    conductor_dvd_of_level_dvd_power_mul_of_primitive_ne_zero (complexQuadraticCharacter n hn) hd h2

/-- For odd n and nonzero primitive value at two, the canonical conductor is
at most n. Combine divisibility with positivity of odd n. This replaces the
uniform 4*n upper bound in the nonzero value-at-two branches. -/
theorem primitiveQuadratic_conductor_le_of_two_ne_zero {n : ℕ} (hn : Odd n)
    (h2 : primitiveQuadraticCharacter n hn 2 ≠ 0) :
    (complexQuadraticCharacter n hn).conductor ≤ n := by
  have hd := primitiveQuadratic_conductor_dvd_of_two_ne_zero hn h2
  exact Nat.le_of_dvd hn.pos hd

end PseudoPrime.NumberTheory

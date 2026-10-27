/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.DirichletCharacter

/-! # Removing powers coprime to the primitive conductor from the original level -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- For a complex Dirichlet character, a nonzero primitive value at a forces
coprimality between a and the conductor. Nonzero character values occur only on
units; use the ZMod unit criterion. No quadraticity or primitivity input is needed. -/
theorem conductor_coprime_of_primitive_apply_ne_zero {N a : ℕ} (χ : DirichletCharacter ℂ N)
    (ha : χ.primitiveCharacter a ≠ 0) : Nat.Coprime χ.conductor a := by
  have hu : IsUnit (a : ZMod χ.conductor) := MulChar.apply_ne_zero_iff.mp ha
  exact ((ZMod.isUnit_iff_coprime a χ.conductor).mp hu).symm

/-- If the nonzero original level divides a^k*m and the primitive value at a
is nonzero, the conductor divides m. It is coprime to a^k, so remove this factor
from conductor divisibility. This generalizes the odd-conductor reduction at two
without discriminant data or a quadraticity assumption. -/
theorem conductor_dvd_of_level_dvd_power_mul_of_primitive_ne_zero {N a m k : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hN : N ∣ a ^ k * m) (ha : χ.primitiveCharacter a ≠ 0) :
    χ.conductor ∣ m := by
  have hc := conductor_coprime_of_primitive_apply_ne_zero χ ha
  exact (hc.pow_right k).dvd_of_dvd_mul_left (dvd_trans χ.conductor_dvd_level hN)

end PseudoPrime.NumberTheory

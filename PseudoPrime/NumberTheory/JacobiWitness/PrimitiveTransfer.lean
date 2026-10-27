/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.JacobiCharacterArithmetic
public import PseudoPrime.NumberTheory.JacobiWitness.Existence

/-! # Odd-prime non-one transfer from the canonical primitive character to Jacobi -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- At an odd prime, a non-one value of the canonical primitive quadratic
character implies a non-one Jacobi symbol. If the prime divides n, use the zero
Jacobi value; otherwise use the primitive evaluation identity. This transfer does
not assert coprimality or negativity, and requires no nonsquare assumption. -/
theorem jacobi_ne_one_of_primitiveQuadraticCharacter_ne_one {n p : ℕ} (hn : Odd n) (hp : p.Prime)
    (ho : Odd p) (hv : primitiveQuadraticCharacter n hn p ≠ 1) : jacobiSym n p ≠ 1 := by
  by_cases hpn : p ∣ n
  · exact (primeNeOneWitness_mem_of_dvd hp ho hpn).2.2
  · have he := primitiveQuadraticCharacter_apply_odd_prime hn hp ho hpn
    simp only [Int.cast_natCast] at he
    intro hj
    rw [hj, Int.cast_one] at he
    exact hv he

end PseudoPrime.NumberTheory

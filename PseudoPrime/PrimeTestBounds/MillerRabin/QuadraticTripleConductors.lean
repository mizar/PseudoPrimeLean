/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticPairSign
public import Mathlib.Tactic.Ring

/-! # Exact conductor logarithm sum for the three pair characters -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For a product of three nonzero natural factors, the logarithms of the
three pair levels add to twice the logarithm of the product. Expand products
under the logarithm. This is the arithmetic conductor-saving identity. -/
theorem pair_level_log_sum {n p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] (hn : n = p * q * r) :
    Real.log (p * q : ℕ) + Real.log (p * r : ℕ) + Real.log (q * r : ℕ) = 2 * Real.log n := by
  have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  have hq : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hr : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  rw [hn]
  simp only [Nat.cast_mul, Real.log_mul (mul_ne_zero hp hq) hr, Real.log_mul hp hq,
    Real.log_mul hp hr, Real.log_mul hq hr]
  ring

/-- For odd pair levels dividing a squarefree three-factor modulus, the
actual Jacobi character conductors have logarithm sum twice the ambient
logarithm. Primitivity fixes each conductor exactly, then the pair-level
identity applies. This discharges the conductor price in the Gamma branch. -/
theorem pair_conductor_log_sum {n p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] (hn : n = p * q * r)
    (hsq : Squarefree n) (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpqn : p * q ∣ n)
    (hprn : p * r ∣ n) (hqrn : q * r ∣ n) :
    Real.log (NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)).conductor +
        Real.log (NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)).conductor +
        Real.log (NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)).conductor =
      2 * Real.log n := by
  have hA := pair_character_primitive hsq hpqn (hp.mul hq)
  have hB := pair_character_primitive hsq hprn (hp.mul hr)
  have hC := pair_character_primitive hsq hqrn (hq.mul hr)
  change (NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)).conductor = p * q at hA
  change (NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)).conductor = p * r at hB
  change (NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)).conductor = q * r at hC
  rw [hA, hB, hC]
  exact pair_level_log_sum hn

end PseudoPrime.PrimeTestBounds.MillerRabin

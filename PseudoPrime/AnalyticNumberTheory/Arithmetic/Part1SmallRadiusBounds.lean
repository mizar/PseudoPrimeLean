/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Statement
public import PseudoPrime.Analysis.LogTaylorBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactors

/-! # Uniform finite caps for the original LLS Part 1 radius -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Input: any natural modulus. Claim: its prime-support logarithmic sum is nonnegative.
Proof: each prime factor has nonnegative logarithm and positive denominator.
Role: bound auxiliary corrections without evaluating factorizations. -/
theorem primeFactorLogSum_nonneg (q : ℕ) : 0 ≤ primeFactorLogSum q := by
  apply Finset.sum_nonneg
  intro p hp
  have hR : (2 : ℝ) ≤ p := Nat.cast_le.mpr (Nat.prime_of_mem_primeFactors hp).two_le
  exact div_nonneg (Real.log_natCast_nonneg p) (by linarith only [hR])

end PseudoPrime.AnalyticNumberTheory.Arithmetic

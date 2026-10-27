/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterExclusionProducts

/-! # Exclusion cost supported on ramified primes and two -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- If a character vanishes on the prime support of nonzero d, excluding
2d costs at most log(4d). Bound the contribution at two by twice log two
and the ramified support by log d. This is independent of primitivity and
of any additional square factors in a later input. -/
theorem characterExclusionCost_two_mul_le_log_four_mul {f d : ℕ} (χ : DirichletCharacter ℂ f)
    (hd : d ≠ 0) (hz : ∀ p ∈ d.primeFactors, χ p = 0) :
    characterExclusionCost χ (2 * d) ≤ Real.log ((4 * d : ℕ) : ℝ) := by
  have hm := characterExclusionCost_mul_le χ (by norm_num only : (2 : ℕ) ≠ 0) hd
  have hr := characterExclusionCost_le_log_of_zero χ hd hz
  have ht := characterExclusionCost_le_twice χ 2
  rw [Nat.prime_two.primeFactors, Finset.sum_singleton] at ht
  norm_num only [Nat.cast_ofNat] at ht
  have hl : Real.log ((4 * d : ℕ) : ℝ) = 2 * Real.log 2 + Real.log d := by
    rw [Nat.cast_mul, Nat.cast_ofNat,
      Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0) (Nat.cast_ne_zero.mpr hd)]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  linarith only [hm, hr, ht, hl]

end PseudoPrime.AnalyticNumberTheory.Arithmetic

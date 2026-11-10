/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerPrefix

/-! # Euler prefix at cutoff 328 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- Kernel evaluation uses the existing checked prime-power data.
set_option maxRecDepth 4096 in
-- Rational reduction traverses the checked prime-power prefix.
/-- The rational Euler prefix through 328 exceeds 2.3704. -/
theorem quarter_euler_cap328_check :
    (23704 / 10000 : ℚ) <
      ∑ n ∈ quarterEulerPrefix 328, refinedEulerAtomLower n (refinedEulerData n) := by
  decide +kernel

/-- The exact rational prefix bounds the Euler sum through cutoff 328 below. -/
theorem quarter_euler_cap328 :
    (23704 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊(328 : ℝ)⌋₊,
        ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
  have h := (Rat.cast_lt (K := ℝ)).mpr quarter_euler_cap328_check
  simp only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h.le.trans (quarter_euler_prefix_lower 328 (by norm_num only))

end PseudoPrime.PrimeTestBounds.MillerRabin

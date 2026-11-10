/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerPrefix

/-! # Euler prefix at cutoff 350 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- Kernel evaluation uses the existing checked prime-power data.
set_option maxRecDepth 4096 in
-- Rational reduction traverses the checked prime-power prefix.
/-- The rational Euler prefix through 350 exceeds 2.3898. -/
theorem quarter_euler_cap350_check :
    (23898 / 10000 : ℚ) <
      ∑ n ∈ quarterEulerPrefix 350, refinedEulerAtomLower n (refinedEulerData n) := by
  decide +kernel

/-- The exact rational prefix bounds the Euler sum through cutoff 350 below. -/
theorem quarter_euler_cap350 :
    (23898 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊(350 : ℝ)⌋₊,
        ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
  have h := (Rat.cast_lt (K := ℝ)).mpr quarter_euler_cap350_check
  simp only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h.le.trans (quarter_euler_prefix_lower 350 (by norm_num only))

end PseudoPrime.PrimeTestBounds.MillerRabin

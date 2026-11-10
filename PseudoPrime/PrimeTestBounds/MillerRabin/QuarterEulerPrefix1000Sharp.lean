/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerPrefix1000

/-! # Sharp lower Euler prefix at 1000 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- Exact rational arithmetic checks the already certified row endpoints.
/-- The rational prefix exceeds the normalized constant `178404/100000`. -/
theorem quarter_euler_prefix1000_sharp_check :
    (178404 / 100000 : ℚ) * (27 / 25 : ℚ) ^ 5 <
      ∑ n ∈ refinedEulerPrefixSet, refinedEulerAtomLower n (refinedEulerData n) := by
  decide +kernel

/-- The certified finite Euler prefix exceeds `178404/100000` times the
kernel normalization. Existing row checks transfer the rational estimate. -/
theorem quarter_euler_prefix1000_sharp :
    (178404 / 100000 : ℝ) * (27 / 25 : ℝ) ^ 5 <
      ∑ n ∈ refinedEulerPrefixSet, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
  have hc :=
    refined_euler_prefix_sound refinedEulerPrefixSet refinedEulerData refined_euler_prefix_check
  have hl :
    ((178404 / 100000 : ℚ) * (27 / 25 : ℚ) ^ 5 : ℝ) <
      ((∑ n ∈ refinedEulerPrefixSet, refinedEulerAtomLower n (refinedEulerData n) : ℚ) : ℝ) := by
    exact_mod_cast quarter_euler_prefix1000_sharp_check
  norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] at hl ⊢
  exact hl.trans_le hc

end PseudoPrime.PrimeTestBounds.MillerRabin

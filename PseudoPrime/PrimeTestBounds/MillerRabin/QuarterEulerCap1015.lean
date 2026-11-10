/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerPrefixAt

/-! # Euler prefix at cutoff 1015 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The certified prefix bounds the Euler sum through cutoff 1015 below. -/
theorem quarter_euler_cap1015 :
    (26212 / 10000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊(1015 : ℝ)⌋₊,
        ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
  have h := refined_euler_prefix_1000_at (X := 1015) (by norm_num only)
  norm_num only at h ⊢
  linarith only [h]

end PseudoPrime.PrimeTestBounds.MillerRabin

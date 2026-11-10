/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedDigammaSquareBlock0
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedDigammaSquareBlock1
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedDigammaSquareBlock2
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedDigammaSquareBlock3
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedDigammaSquareBlock4
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedDigammaSquareBlock5
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedDigammaSquareBlock6
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedDigammaSquareBlock7

/-! # Digamma reciprocal-square prefix certificate -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The first 256 reciprocal-square terms exceed 2.34. Eight independently
verified blocks are combined without repeating their finite checks. -/
theorem refined_digamma_square_prefix :
    (234 / 100 : ℝ) < ∑ n ∈ Finset.range 256, ((79 / 100 : ℝ) + (n : ℝ))⁻¹ ^ 2 := by
  rw [show (256 : ℕ) = 224 + 32 by norm_num only, Finset.sum_range_add]
  rw [show (224 : ℕ) = 192 + 32 by norm_num only, Finset.sum_range_add]
  rw [show (192 : ℕ) = 160 + 32 by norm_num only, Finset.sum_range_add]
  rw [show (160 : ℕ) = 128 + 32 by norm_num only, Finset.sum_range_add]
  rw [show (128 : ℕ) = 96 + 32 by norm_num only, Finset.sum_range_add]
  rw [show (96 : ℕ) = 64 + 32 by norm_num only, Finset.sum_range_add]
  rw [show (64 : ℕ) = 32 + 32 by norm_num only, Finset.sum_range_add]
  have h0 := refined_digamma_square_block0
  have h1 := refined_digamma_square_block1
  have h2 := refined_digamma_square_block2
  have h3 := refined_digamma_square_block3
  have h4 := refined_digamma_square_block4
  have h5 := refined_digamma_square_block5
  have h6 := refined_digamma_square_block6
  have h7 := refined_digamma_square_block7
  simp only [Nat.add_zero] at h0
  linarith only [h0, h1, h2, h3, h4, h5, h6, h7]

end PseudoPrime.PrimeTestBounds.MillerRabin

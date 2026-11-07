/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.GaussianMomentGridValidity

/-! # Integer caps for Gaussian moment grid sums -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The outer exponential upper endpoint, rounded upward at scale 10^8.
Its positive denominator is the certified fixed-point lower endpoint of the
opposite exponent. Integer sums of these caps are kernel-checkable. -/
def gaussianGridOuterCap (i k : ℕ) : ℕ :=
  let lower :=
    Analysis.expFixedPointSignedLower (gaussianGridOuterNegNum i k) (5120 * 10 ^ 24) (10 ^ 24) 401
  (10 ^ 24 * 10 ^ 8 + lower - 1) / lower

/-- The rounded integer cap bounds the reciprocal fixed-point endpoint.
Use the positive denominator and the natural ceiling-division inequality. -/
theorem gaussian_grid_outer_cap_sound (i k : ℕ) (hk : k ∈ ({1, 3} : Finset ℕ)) :
    (10 ^ 24 : ℝ) /
        (Analysis.expFixedPointSignedLower (gaussianGridOuterNegNum i k) (5120 * 10 ^ 24) (10 ^ 24)
            401 :
          ℝ) ≤
      (gaussianGridOuterCap i k : ℝ) / 10 ^ 8 := by
  have hp := gaussian_grid_outer_fixed_pos i k 401 hk (by norm_num only)
  have h :=
    Analysis.div_le_cast_ceilDiv (10 ^ 24 * 10 ^ 8)
      (Analysis.expFixedPointSignedLower (gaussianGridOuterNegNum i k) (5120 * 10 ^ 24) (10 ^ 24)
        401)
      hp
  change
    ((10 ^ 24 * 10 ^ 8 : ℕ) : ℝ) /
        (Analysis.expFixedPointSignedLower (gaussianGridOuterNegNum i k) (5120 * 10 ^ 24) (10 ^ 24)
            401 :
          ℝ) ≤
      (gaussianGridOuterCap i k : ℝ) at h
  norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h
  norm_num only at h ⊢
  apply (le_div_iff₀ (by norm_num only : (0 : ℝ) < 100000000)).2
  convert h using 1
  ring

/-- Both finite Gaussian moment integrals are bounded by sums of executable
integer caps with a common rational coefficient. Each cap is rounded upward,
and the uniform fixed-point bounds justify every cell. -/
theorem gaussian_grid_256_integer_caps :
    (∫ v in (-4 : ℝ)..4, Analysis.gaussianGammaProfileIntegrand (21 / 10) v) ≤
        (113 / (6400 * 10 ^ 8) : ℝ) * (∑ i ∈ Finset.range 256, gaussianGridOuterCap i 1 : ℕ) ∧
      (∫ v in (-4 : ℝ)..4, gaussianEndpointDensity (21 / 10) v) ≤
        (113 / (6400 * 10 ^ 8) : ℝ) * (∑ i ∈ Finset.range 256, gaussianGridOuterCap i 3 : ℕ) := by
  have h := gaussian_grid_256_executable_bounds
  constructor
  · refine h.1.trans ?_
    rw [Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hm := gaussian_grid_outer_cap_sound i 1 (by simp only [Finset.mem_insert, true_or])
    have ht := mul_le_mul_of_nonneg_left hm (by norm_num only : (0 : ℝ) ≤ (1 / 32) * (113 / 200))
    convert ht using 1 <;> ring
  · refine h.2.trans ?_
    rw [Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hm :=
      gaussian_grid_outer_cap_sound i 3
        (by simp only [Finset.mem_insert, Finset.mem_singleton, or_true])
    have ht := mul_le_mul_of_nonneg_left hm (by norm_num only : (0 : ℝ) ≤ (1 / 32) * (113 / 200))
    convert ht using 1 <;> ring

end PseudoPrime.LLS.PaperStatements

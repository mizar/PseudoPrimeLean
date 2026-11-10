/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectedFiniteMoments
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentLowerCap0
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentLowerCap1
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentLowerCap2
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentLowerCap3
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentLowerCap4
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentLowerCap5

/-! # Certified lower bound for the reflected Euler prefix -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Polynomial formed from six certified lower finite Mangoldt moments.
At nonnegative arguments it bounds the reflected prefix from below. -/
noncomputable def quarterMomentLowerPolynomial (z : ℝ) : ℝ :=
  (1222 / 1000 : ℝ) * z ^ 5 + 5 * (2662 / 1000 : ℝ) * z ^ 4 + 10 * (8498 / 1000 : ℝ) * z ^ 3 +
    10 * (35559 / 1000 : ℝ) * z ^ 2 +
    5 * (176804 / 1000 : ℝ) * z +
    (981502 / 1000 : ℝ)

/-- At each scale at least one, the reflected Euler prefix through 2701
is at least the explicit polynomial built from the six lower moments.
The finite moment identity retains the exact normalization of the kernel. -/
theorem quarter_reflected_prefix_lower {x : ℝ} (hx : 1 ≤ x) :
    ((((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) * x ^ (-(27 / 25 : ℝ))) *
        quarterMomentLowerPolynomial ((21 / 8 : ℝ) + Real.log x) ≤
      ∑ n ∈ Finset.Ioc 0 2701, refinedDualWeight x n := by
  let z : ℝ := 21 / 8 + Real.log x
  have hz : 0 ≤ z := by
    dsimp only [z]
    have h := Real.log_nonneg hx
    linarith only [h]
  have h0 := mul_le_mul_of_nonneg_left quarter_moment_lower_real0 (pow_nonneg hz 5)
  have h1 := mul_le_mul_of_nonneg_left quarter_moment_lower_real1 (pow_nonneg hz 4)
  have h2 := mul_le_mul_of_nonneg_left quarter_moment_lower_real2 (pow_nonneg hz 3)
  have h3 := mul_le_mul_of_nonneg_left quarter_moment_lower_real3 (pow_nonneg hz 2)
  have h4 := mul_le_mul_of_nonneg_left quarter_moment_lower_real4 hz
  have h5 := quarter_moment_lower_real5
  have hp :
    quarterMomentLowerPolynomial z ≤
      ∑ j ∈ Finset.range 6,
        ((Nat.choose 5 j : ℕ) : ℝ) * z ^ (5 - j) *
          ∑ n ∈ Finset.Ioc 0 2701, quarterMangoldtMoment j n := by
    dsimp only [quarterMomentLowerPolynomial]
    norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.reduceSub,
      Nat.reduceAdd, Nat.cast_ofNat, pow_zero, pow_one, mul_one, add_zero, zero_add]
    linarith only [h0, h1, h2, h3, h4, h5]
  rw [quarter_reflected_finite_moments hx]
  exact mul_le_mul_of_nonneg_left hp (by positivity)

end PseudoPrime.PrimeTestBounds.MillerRabin

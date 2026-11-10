/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectedMoments

/-! # Finite reflected Euler moments -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For a scale at least one, the reflected Euler weight is exactly the
binomial combination of six Mangoldt moments. The zero index is included. -/
theorem quarter_reflected_moment_identity {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    refinedDualWeight x n =
      ((((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) *
          x ^ (-(27 / 25 : ℝ))) *
        ∑ j ∈ Finset.range 6,
          ((Nat.choose 5 j : ℕ) : ℝ) * ((21 / 8 : ℝ) + Real.log x) ^ (5 - j) *
            quarterMangoldtMoment j n := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  by_cases hn : n = 0
  · subst n
    simp only [refinedDualWeight, ArithmeticFunction.map_zero, zero_div, zero_mul,
      quarterMangoldtMoment, Finset.sum_const_zero, mul_zero]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have he :
      ((((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) *
            x ^ (-(27 / 25 : ℝ))) *
          (∑ j ∈ Finset.range 6,
            ((Nat.choose 5 j : ℕ) : ℝ) * ((21 / 8 : ℝ) + Real.log x) ^ (5 - j) *
              quarterMangoldtMoment j n) =
        (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) *
          ((21 / 8 : ℝ) + Real.log x + Real.log n) ^ 5 *
          (x ^ (-(27 / 25 : ℝ)) * quarterMangoldtMoment 0 n) := by
      dsimp only [quarterMangoldtMoment]
      norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.reduceSub,
        Nat.reduceAdd, Nat.cast_ofNat, pow_zero, pow_one, mul_one, add_zero, zero_add]
      ring
    rw [he, refined_dual_weight_explicit hx hn1, ← quarter_scaled_mangoldt hx0 n]
    ring

/-- A finite reflected Euler prefix is the same binomial combination of its
six finite Mangoldt moments. The order of the finite sums may be exchanged. -/
theorem quarter_reflected_finite_moments {x : ℝ} (hx : 1 ≤ x) (s : Finset ℕ) :
    (∑ n ∈ s, refinedDualWeight x n) =
      ((((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) *
          x ^ (-(27 / 25 : ℝ))) *
        ∑ j ∈ Finset.range 6,
          ((Nat.choose 5 j : ℕ) : ℝ) * ((21 / 8 : ℝ) + Real.log x) ^ (5 - j) *
            ∑ n ∈ s, quarterMangoldtMoment j n := by
  simp only [quarter_reflected_moment_identity hx, Finset.mul_sum]
  rw [Finset.sum_comm]

end PseudoPrime.PrimeTestBounds.MillerRabin

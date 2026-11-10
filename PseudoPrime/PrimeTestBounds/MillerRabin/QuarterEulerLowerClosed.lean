/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerVariationIntegrable
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerSqrtIntegral
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerEndpointPower

/-! Explicit cutoff-1000 Euler tail lower bound. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The closed form of the refined Euler weight integral above 1000, used in the lower bound. -/
noncomputable def quarterEulerWeightTail : ℝ :=
  (1000 : ℝ) ^ (-(29 / 50 : ℝ)) / 8 *
    (3 / (29 / 50 : ℝ) + (81 / 25 : ℝ) * (Real.log 1000 / (29 / 50 : ℝ) + 1 / (29 / 50 : ℝ) ^ 2) +
      (729 / 625 : ℝ) *
        ((Real.log 1000) ^ 2 / (29 / 50 : ℝ) + 2 * Real.log 1000 / (29 / 50 : ℝ) ^ 2 +
          2 / (29 / 50 : ℝ) ^ 3))

/-- The closed form of the square-root variation integral above 1000, used in the tail error. -/
noncomputable def quarterEulerSqrtTail : ℝ :=
  (1000 : ℝ) ^ (-(27 / 25 : ℝ)) / 8 *
    ((4549689 / 1562500 : ℝ) *
          ((Real.log 1000) ^ 2 / (27 / 25 : ℝ) + 2 * Real.log 1000 / (27 / 25 : ℝ) ^ 2 +
            2 / (27 / 25 : ℝ) ^ 3) +
        (44793 / 62500 : ℝ) * (Real.log 1000 / (27 / 25 : ℝ) + 1 / (27 / 25 : ℝ) ^ 2) -
      (1041 / 2500 : ℝ) / (27 / 25 : ℝ))

/-- Under RH, the Euler sum exceeds the cutoff-1000 expression with its improper integrals
replaced by exact closed forms. This is the input to the rational endpoint certificate. -/
theorem quarter_euler_lower_1000_closed (hRH : RiemannHypothesis) :
    (178404 / 100000 : ℝ) * (27 / 25 : ℝ) ^ 5 +
            refinedEulerRealWeight 1000 * (1000 - Chebyshev.psi 1000) +
            refinedEulerSlope 1000 *
              (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 1000 - 1000) +
            quarterEulerWeightTail -
          (231 / 5000 : ℝ) * quarterEulerSqrtTail -
          (1839 / 1000 : ℝ) *
            (refinedEulerRealWeight 1000 - Real.log 1000 * refinedEulerSlope 1000) +
        2 * refinedEulerSlope 1000 <
      ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
  have h := quarter_euler_lower_1000_boundary hRH
  rw [refined_weight_integral_eq (by norm_num only : (1 : ℝ) ≤ 1000),
    refined_sqrt_variation_integral_eq (by norm_num only : (1 : ℝ) ≤ 1000)] at h
  exact h

/-- The closed weight tail at cutoff 1000 exceeds the stated rational lower bound. The proof uses
the checked negative-power interval and a lower bound for the logarithm. -/
theorem quarter_euler_weight_tail_lower : (4758776 / 10000000 : ℝ) ≤ quarterEulerWeightTail := by
  have hl := refined_log_1000_lower
  have hs := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 6907755 / 1000000) hl 2
  let q : ℝ :=
    3 / (29 / 50 : ℝ) +
      (81 / 25 : ℝ) * ((6907755 / 1000000 : ℝ) / (29 / 50 : ℝ) + 1 / (29 / 50 : ℝ) ^ 2) +
      (729 / 625 : ℝ) *
        (((6907755 / 1000000 : ℝ) ^ 2) / (29 / 50 : ℝ) +
          2 * (6907755 / 1000000 : ℝ) / (29 / 50 : ℝ) ^ 2 +
          2 / (29 / 50 : ℝ) ^ 3)
  have hq :
    q ≤
      3 / (29 / 50 : ℝ) + (81 / 25 : ℝ) * (Real.log 1000 / (29 / 50 : ℝ) + 1 / (29 / 50 : ℝ) ^ 2) +
        (729 / 625 : ℝ) *
          ((Real.log 1000) ^ 2 / (29 / 50 : ℝ) + 2 * Real.log 1000 / (29 / 50 : ℝ) ^ 2 +
            2 / (29 / 50 : ℝ) ^ 3) := by
    dsimp only [q]
    norm_num only at hl hs ⊢
    nlinarith only [hl, hs]
  have hq0 : 0 ≤ q := by
    dsimp only [q]; norm_num only
  have hp0 : 0 ≤ (1000 : ℝ) ^ (-(29 / 50 : ℝ)) := Real.rpow_nonneg (by norm_num only) _
  have hm := mul_le_mul quarter_euler_power_bounds.1 hq hq0 hp0
  dsimp only [quarterEulerWeightTail, q] at hm ⊢
  nlinarith only [hm]

/-- Under RH, substitute the rational weight-tail lower bound into the closed Euler estimate.
The remaining terms are the endpoint corrections and the square-root error tail. -/
theorem quarter_euler_lower_1000_weight (hRH : RiemannHypothesis) :
    (178404 / 100000 : ℝ) * (27 / 25 : ℝ) ^ 5 +
            refinedEulerRealWeight 1000 * (1000 - Chebyshev.psi 1000) +
            refinedEulerSlope 1000 *
              (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 1000 - 1000) +
            (4758776 / 10000000 : ℝ) -
          (231 / 5000 : ℝ) * quarterEulerSqrtTail -
          (1839 / 1000 : ℝ) *
            (refinedEulerRealWeight 1000 - Real.log 1000 * refinedEulerSlope 1000) +
        2 * refinedEulerSlope 1000 <
      ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
  linarith only [quarter_euler_lower_1000_closed hRH, quarter_euler_weight_tail_lower]

/-- The square-root variation tail at cutoff 1000 is at most the stated rational number.
The power and logarithm enclosures bound the closed polynomial expression. -/
theorem quarter_euler_sqrt_tail_upper : quarterEulerSqrtTail ≤ (12414 / 1000000 : ℝ) := by
  have hu := refined_log_1000_upper
  have hl : 0 ≤ Real.log 1000 := Real.log_nonneg (by norm_num only)
  have hs := pow_le_pow_left₀ hl hu 2
  let q : ℝ :=
    (4549689 / 1562500 : ℝ) *
          ((6907756 / 1000000 : ℝ) ^ 2 / (27 / 25 : ℝ) +
            2 * (6907756 / 1000000 : ℝ) / (27 / 25 : ℝ) ^ 2 +
            2 / (27 / 25 : ℝ) ^ 3) +
        (44793 / 62500 : ℝ) * ((6907756 / 1000000 : ℝ) / (27 / 25 : ℝ) + 1 / (27 / 25 : ℝ) ^ 2) -
      (1041 / 2500 : ℝ) / (27 / 25 : ℝ)
  have hq :
    (4549689 / 1562500 : ℝ) *
            ((Real.log 1000) ^ 2 / (27 / 25 : ℝ) + 2 * Real.log 1000 / (27 / 25 : ℝ) ^ 2 +
              2 / (27 / 25 : ℝ) ^ 3) +
          (44793 / 62500 : ℝ) * (Real.log 1000 / (27 / 25 : ℝ) + 1 / (27 / 25 : ℝ) ^ 2) -
        (1041 / 2500 : ℝ) / (27 / 25 : ℝ) ≤
      q := by
    dsimp only [q]
    norm_num only at hu hs ⊢
    nlinarith only [hu, hs]
  have hq0 :
    0 ≤
      (4549689 / 1562500 : ℝ) *
            ((Real.log 1000) ^ 2 / (27 / 25 : ℝ) + 2 * Real.log 1000 / (27 / 25 : ℝ) ^ 2 +
              2 / (27 / 25 : ℝ) ^ 3) +
          (44793 / 62500 : ℝ) * (Real.log 1000 / (27 / 25 : ℝ) + 1 / (27 / 25 : ℝ) ^ 2) -
        (1041 / 2500 : ℝ) / (27 / 25 : ℝ) := by
    norm_num only
    nlinarith only [hl, sq_nonneg (Real.log 1000)]
  have hm :=
    mul_le_mul quarter_euler_power_bounds.2.2.2.1 hq hq0
      (by norm_num only : (0 : ℝ) ≤ 575439938 / 1000000000000)
  dsimp only [quarterEulerSqrtTail, q] at hm ⊢
  nlinarith only [hm]

/-- Under RH, both Euler-tail integrals in the cutoff-1000 estimate admit certified rational
bounds. Only the endpoint terms remain to be estimated numerically. -/
theorem quarter_euler_lower_1000_tails (hRH : RiemannHypothesis) :
    (178404 / 100000 : ℝ) * (27 / 25 : ℝ) ^ 5 +
            refinedEulerRealWeight 1000 * (1000 - Chebyshev.psi 1000) +
            refinedEulerSlope 1000 *
              (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 1000 - 1000) +
            (4758776 / 10000000 : ℝ) -
          (231 / 5000 : ℝ) * (12414 / 1000000 : ℝ) -
          (1839 / 1000 : ℝ) *
            (refinedEulerRealWeight 1000 - Real.log 1000 * refinedEulerSlope 1000) +
        2 * refinedEulerSlope 1000 <
      ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
  linarith only [quarter_euler_lower_1000_weight hRH, quarter_euler_sqrt_tail_upper]

end PseudoPrime.PrimeTestBounds.MillerRabin

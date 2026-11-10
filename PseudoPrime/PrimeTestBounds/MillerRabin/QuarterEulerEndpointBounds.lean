/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerEndpointPower
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsi1000Sharp
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSmoothUpper1000

/-! Rational endpoint enclosures for the refined Euler kernel. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The Euler weight and slope at 1000 lie in narrow rational intervals. The checked power and
logarithm enclosures bound their explicit polynomial expressions. -/
theorem quarter_euler_endpoint_bounds :
    (184331 / 1000000000 : ℝ) ≤ refinedEulerRealWeight 1000 ∧
      refinedEulerRealWeight 1000 ≤ 184333 / 1000000000 ∧
      -(247222 / 1000000000 : ℝ) ≤ refinedEulerSlope 1000 ∧
      refinedEulerSlope 1000 ≤ -(247219 / 1000000000 : ℝ) := by
  have hl := refined_log_1000_lower
  have hu := refined_log_1000_upper
  have hs1 := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 6907755 / 1000000) hl 2
  have hs2 := pow_le_pow_left₀ (Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 1000)) hu 2
  let q : ℝ := 3 + (81 / 25 : ℝ) * Real.log 1000 + (729 / 625 : ℝ) * (Real.log 1000) ^ 2
  let d : ℝ := (79 / 50 : ℝ) * q - (81 / 25 : ℝ) - (1458 / 625 : ℝ) * Real.log 1000
  have hql : (8103832 / 100000 : ℝ) ≤ q := by
    dsimp only [q]
    norm_num only at hl hs1 ⊢
    nlinarith only [hl, hs1]
  have hqu : q ≤ (8103835 / 100000 : ℝ) := by
    dsimp only [q]
    norm_num only at hu hs2 ⊢
    nlinarith only [hu, hs2]
  have hdl : (1086861 / 10000 : ℝ) ≤ d := by
    dsimp only [d, q]
    norm_num only at hl hu hs1 hs2 ⊢
    nlinarith only [hl, hu, hs1, hs2]
  have hdu : d ≤ (1086862 / 10000 : ℝ) := by
    dsimp only [d, q]
    norm_num only at hl hu hs1 hs2 ⊢
    nlinarith only [hl, hu, hs1, hs2]
  have hp0 : 0 ≤ (1000 : ℝ) ^ (-(79 / 50 : ℝ)) := Real.rpow_nonneg (by norm_num only) _
  have hpl := quarter_euler_power_bounds.2.2.2.2.1
  have hpu := quarter_euler_power_bounds.2.2.2.2.2
  have hq0 : 0 ≤ q := by linarith only [hql]
  have hd0 : 0 ≤ d := by linarith only [hdl]
  have h1 := mul_le_mul hpl hql (by norm_num only : (0 : ℝ) ≤ 8103832 / 100000) hp0
  have h2 := mul_le_mul hpu hqu hq0 (by norm_num only : (0 : ℝ) ≤ 18197008587 / 1000000000000000)
  have h3 := mul_le_mul hpl hdl (by norm_num only : (0 : ℝ) ≤ 1086861 / 10000) hp0
  have h4 := mul_le_mul hpu hdu hd0 (by norm_num only : (0 : ℝ) ≤ 18197008587 / 1000000000000000)
  dsimp only [refinedEulerRealWeight, refinedEulerSlope]
  dsimp only [d, q] at h1 h2 h3 h4
  constructor
  · nlinarith only [h1]
  constructor
  · nlinarith only [h2]
  constructor
  · nlinarith only [h4]
  · nlinarith only [h3]

/-- The cutoff-1000 boundary corrections exceed a positive rational lower bound. The estimate
combines checked bounds for the Euler kernel, Chebyshev function and smoothed Mangoldt sum. -/
theorem quarter_euler_boundary_lower :
    (567 / 100000000 : ℝ) ≤
      refinedEulerRealWeight 1000 * (1000 - Chebyshev.psi 1000) +
            refinedEulerSlope 1000 *
              (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 1000 - 1000) -
          (1839 / 1000 : ℝ) *
            (refinedEulerRealWeight 1000 - Real.log 1000 * refinedEulerSlope 1000) +
        2 * refinedEulerSlope 1000 := by
  obtain ⟨hw, _, hs, hs'⟩ := quarter_euler_endpoint_bounds
  have hw0 : 0 ≤ refinedEulerRealWeight 1000 := by linarith only [hw]
  have hs0 : refinedEulerSlope 1000 ≤ 0 := by linarith only [hs']
  have hp : (33 / 10 : ℝ) ≤ 1000 - Chebyshev.psi 1000 := by linarith only [quarter_psi1000_997]
  have hm :
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 1000 - 1000 ≤ -(13637 / 1000 : ℝ) := by
    linarith only [quarter_smooth_1000_upper]
  have h1 := mul_le_mul_of_nonneg_left hp hw0
  have h2 := mul_le_mul_of_nonpos_left hm hs0
  have h3 := mul_le_mul_of_nonpos_left refined_log_1000_upper hs0
  norm_num only at hw hs h1 h2 h3 ⊢
  nlinarith only [hw, hs, h1, h2, h3]

end PseudoPrime.PrimeTestBounds.MillerRabin

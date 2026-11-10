/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerMomentEnvelope
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerTotalLog
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerTotalPower

/-! # Lower bound for the total refined Euler mass -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The independently certified large-cutoff endpoints bound the exact
Euler moment increment. The bound uses no enumeration up to the cutoff. -/
theorem quarter_euler_total_moment (k : ℕ) :
    quarterEulerMomentEnvelope k 28 (1 / 1000000) ≤ quarterEulerMomentLower k 1000000000000 := by
  exact
    quarter_euler_moment_envelope k (by norm_num only) quarter_euler_total_log
      quarter_euler_total_power

/-- Under RH, the total refined Euler mass is at least `2.05` times the
kernel normalization. A large analytic cutoff and summand nonnegativity
transfer the finite lower bound to the convergent total. -/
theorem quarter_euler_total_lower (hRH : RiemannHypothesis) :
    (205 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 ≤
      ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
  have h0 := quarter_euler_total_moment 0
  have h1 := quarter_euler_total_moment 1
  have h2 := quarter_euler_total_moment 2
  have hc :
    (205 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 ≤
      (223 / 125 : ℝ) * (27 / 25 : ℝ) ^ 5 +
        (3 / 8 : ℝ) * quarterEulerMomentEnvelope 0 28 (1 / 1000000) +
        (81 / 200 : ℝ) * quarterEulerMomentEnvelope 1 28 (1 / 1000000) +
        (729 / 5000 : ℝ) * quarterEulerMomentEnvelope 2 28 (1 / 1000000) := by
    norm_num only [quarterEulerMomentEnvelope, Analysis.logPowerTailPoly]
  have hp := quarter_euler_prefix_from_increment hRH (b := 1000000000000) (by norm_num only)
  have hl :
    (205 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 ≤
      ∑ n ∈ Finset.Ioc 0 ⌊(1000000000000 : ℝ)⌋₊,
        ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
    linarith only [h0, h1, h2, hc, hp]
  exact
    hl.trans
      (refined_six_euler_weight_summable.sum_le_tsum _
        (fun n _ ↦
          mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (refined_six_euler_weight_nonneg_all n)))

end PseudoPrime.PrimeTestBounds.MillerRabin

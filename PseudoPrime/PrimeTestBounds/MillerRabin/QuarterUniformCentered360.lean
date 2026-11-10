/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredCell175
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredCell178
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerPrefix26896
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerPrefix31684

/-! # Uniform triples from logarithm 350 to 360 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a uniform Korselt triple with logarithm between 350 and 360
has a quarter-square rejecting prime. Two analytic Euler-prefix bounds and
two independent endpoint certificates cover the interval. -/
theorem quarter_uniform_350_360 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hlo : (350 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ 360) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  let r : ℝ := Real.log n / 2
  have hr : (175 : ℝ) ≤ r := by
    dsimp only [r]; linarith only [hlo]
  have hrU : r ≤ 180 := by
    dsimp only [r]; linarith only [hhi]
  have hr34 : (34 : ℝ) ≤ r := by linarith only [hr]
  have hU : Real.log n ≤ 2 * r := by
    dsimp only [r]; linarith only
  have hcut : r ^ 2 ≤ (1 / 4 : ℝ) * Real.log n ^ 2 := by
    dsimp only [r]
    ring_nf
    exact le_rfl
  by_cases h : r ≤ 178
  · have hr2 : (26896 : ℝ) ≤ r ^ 2 := by nlinarith only [hr]
    have hP := quarter_euler_prefix_26896_strong hGRH.riemann hr2
    exact
      quarter_uniform_of_residual_prefix hn ho hu hGRH hr34 hU hcut hP
        (quarter_centered_gap_175_178 hr h)
  · have hr' : (178 : ℝ) ≤ r := le_of_not_ge h
    have hr2 : (31684 : ℝ) ≤ r ^ 2 := by nlinarith only [hr']
    have hP := quarter_euler_prefix_31684 hGRH.riemann hr2
    exact
      quarter_uniform_of_residual_prefix hn ho hu hGRH hr34 hU hcut hP
        (quarter_centered_gap_178_180 hr' hrU)

end PseudoPrime.PrimeTestBounds.MillerRabin

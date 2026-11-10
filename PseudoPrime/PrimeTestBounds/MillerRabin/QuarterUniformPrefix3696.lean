/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformPrefixBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredPrefix1848
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerPrefix31684

/-! # Uniform Korselt triples through logarithm 369.6 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a uniform Korselt triple with logarithm between 366 and 369.6
has a rejecting prime below one quarter of its squared logarithm. The bound
uses both the first Gamma-pole and the finite reflected Euler savings. -/
theorem quarter_uniform_366_3696 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hlo : (366 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ 1848 / 5) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  let r : ℝ := Real.log n / 2
  have hr : (183 : ℝ) ≤ r := by
    dsimp only [r]; linarith only [hlo]
  have hrU : r ≤ 924 / 5 := by
    dsimp only [r]; linarith only [hhi]
  have hU : Real.log n ≤ 2 * r := by
    dsimp only [r]; linarith only
  have hcut : r ^ 2 ≤ (1 / 4 : ℝ) * Real.log n ^ 2 := by
    dsimp only [r]
    ring_nf
    exact le_rfl
  have hr2 : (31684 : ℝ) ≤ r ^ 2 := by nlinarith only [hr]
  have hP := quarter_euler_prefix_31684 hGRH.riemann hr2
  exact
    quarter_uniform_residual_prefix hn ho hu hGRH (by linarith only [hr]) (by linarith only [hrU])
      hU hcut hP (quarter_centered_prefix_183_1848 hr hrU)

end PseudoPrime.PrimeTestBounds.MillerRabin

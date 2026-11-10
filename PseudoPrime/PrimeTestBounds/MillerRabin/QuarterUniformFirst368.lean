/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformFirstBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredFirstCell183
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerPrefix31684

/-! # Uniform Korselt triples between logarithms 366 and 368 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a uniform Korselt triple with logarithm between `366` and
`368` has a rejecting prime below one quarter of its squared logarithm.
The corrected centered cell and the certified Euler prefix discharge the gap. -/
theorem quarter_uniform_366_368 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hlo : (366 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ 368) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  let r : ℝ := Real.log n / 2
  have hr : (183 : ℝ) ≤ r := by
    dsimp only [r]; linarith only [hlo]
  have hrU : r ≤ 184 := by
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
    quarter_uniform_residual_first hn ho hu hGRH (by linarith only [hr]) (by linarith only [hrU]) hU
      hcut hP (quarter_centered_first_183_184 hr hrU)

end PseudoPrime.PrimeTestBounds.MillerRabin

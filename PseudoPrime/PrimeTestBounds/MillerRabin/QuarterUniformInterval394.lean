/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformKorseltTriple
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformClosedBounds
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredClosed197

/-! # Independent uniform Korselt interval -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, the closed-tail residual proves the quarter-square witness for a uniform
Korselt triple when its logarithm is between 392 and 394. -/
theorem quarter_uniform_392_394 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hlo : (392 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ 394) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  let r : ℝ := Real.log n / 2
  have hr : (196 : ℝ) ≤ r := by
    dsimp only [r]; linarith only [hlo]
  have hrU : r ≤ 197 := by
    dsimp only [r]; linarith only [hhi]
  have hU : Real.log n ≤ 2 * r := by
    dsimp only [r]; linarith only
  have hcut : r ^ 2 ≤ (1 / 4 : ℝ) * Real.log n ^ 2 := by
    dsimp only [r]
    ring_nf
    exact le_rfl
  exact
    quarter_uniform_residual_closed hn ho hu hGRH (by linarith only [hr]) (by linarith only [hrU])
      hU hcut (quarter_closed_residual_196_197 hr hrU)

end PseudoPrime.PrimeTestBounds.MillerRabin

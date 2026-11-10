/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformAnchor
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformAnchor9
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformAnchor10
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformAnchor1125

/-! # Integration of independent quarter-square uniform anchors -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, uniform Korselt triples with logarithms between 15.621 and
22.62 have a quarter-square rejecting prime. The independently certified
local anchors cover the interval with overlaps. -/
theorem quarter_uniform_anchor_range {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (15621 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 1131 / 50) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases h1 : Real.log n ≤ 9749 / 500
  · exact quarter_uniform_anchor hn ho hu hGRH hL h1
  by_cases h2 : Real.log n ≤ 1029 / 50
  · exact quarter_uniform_anchor9 hn ho hu hGRH (by linarith only [h1]) h2
  by_cases h3 : Real.log n ≤ 108 / 5
  · exact quarter_uniform_anchor10 hn ho hu hGRH (by linarith only [h2]) h3
  · exact quarter_uniform_anchor1125 hn ho hu hGRH (by linarith only [h3]) hU

end PseudoPrime.PrimeTestBounds.MillerRabin

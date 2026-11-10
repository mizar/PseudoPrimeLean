/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformKorseltTriple
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredClosed188
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredClosed192
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredClosed194
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredClosed195

/-! # Uniform quarter-bound witnesses on logarithmic scales 366 to 390 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The four independently checked closed-tail cells cover radii 183 through 195. -/
private theorem quarter_closed_residual_183_195 {r : ℝ} (hlo : 183 ≤ r) (hhi : r ≤ 195) :
    quarterCenteredClosedResidual r - 57 / 500 - 7 / 250 - (27 / 25 : ℝ) ^ 5 * (33 / 500) ≤
      (27 / 25 : ℝ) ^ 5 * (24439 / 50000 : ℝ) * r - (3 / 4 : ℝ) * r -
        (27 / 25 : ℝ) ^ 5 * (108 / 1000 : ℝ) * Real.sqrt r := by
  by_cases h1 : r ≤ 188
  · exact quarter_closed_residual_183_188 hlo h1
  · by_cases h2 : r ≤ 192
    · exact quarter_closed_residual_188_192 (by linarith only [h1]) h2
    · by_cases h3 : r ≤ 194
      · exact quarter_closed_residual_192_194 (by linarith only [h2]) h3
      · exact quarter_closed_residual_194_195 (by linarith only [h3]) hhi

/-- Under GRH, a uniform Korselt triple with logarithm between 366 and 390 has a prime
Miller–Rabin witness within one quarter of the logarithm squared. -/
theorem quarter_uniform_366_390 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hlo : (366 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ 390) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  let r : ℝ := Real.log n / 2
  have hr : (183 : ℝ) ≤ r := by
    dsimp only [r]; linarith only [hlo]
  have hrU : r ≤ 195 := by
    dsimp only [r]; linarith only [hhi]
  have hU : Real.log n ≤ 2 * r := by
    dsimp only [r]; linarith only
  have hcut : r ^ 2 ≤ (1 / 4 : ℝ) * Real.log n ^ 2 := by
    dsimp only [r]
    ring_nf
    exact le_rfl
  exact
    quarter_uniform_residual_closed hn ho hu hGRH (by linarith only [hr]) (by linarith only [hrU])
      hU hcut (quarter_closed_residual_183_195 hr hrU)

end PseudoPrime.PrimeTestBounds.MillerRabin

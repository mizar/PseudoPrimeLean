/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformKorseltTriple
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeElevenCount
import PseudoPrime.PrimeTestBounds.MillerRabin.ThreeEleventhsGRHCount

/-! # Uniform middle interval under GRH -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a uniform Korselt triple with `10300 ≤ log n ≤ 4000000`
has a rejecting prime at most `(3/11) * log n ^ 2`. The proved RH zero-count
estimate supplies the analytic input of the middle-interval theorem. -/
theorem uniform_three_eleven_middle_grh {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (10300 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 4000000) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 11 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  exact
    uniform_three_eleven_count_middle hn ho hu hGRH (positive_zero_count_log_of_RH hGRH.riemann) hL
      hU

end PseudoPrime.PrimeTestBounds.MillerRabin

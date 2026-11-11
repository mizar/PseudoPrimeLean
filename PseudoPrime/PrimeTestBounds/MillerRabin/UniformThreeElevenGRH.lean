/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeElevenCumulative
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeElevenMiddleGRH
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeElevenLow

/-! # Cumulative uniform three-elevenths bound under GRH -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, every uniform Korselt triple with logarithm at most four
million has a rejecting prime within the `3/11` cutoff. The RH zero count
discharges the middle-interval input of the cumulative uniform theorem. -/
theorem uniform_three_eleven_to4m_grh {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hU : Real.log n ≤ 4000000) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 11 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases h10300 : Real.log n ≤ 10300
  · exact uniform_three_eleven_to10300 hn ho hu hGRH h10300
  · exact uniform_three_eleven_middle_grh hn ho hu hGRH (le_of_not_ge h10300) hU

end PseudoPrime.PrimeTestBounds.MillerRabin

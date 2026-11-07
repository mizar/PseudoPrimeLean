/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaAnalyticNext

/-! # Coverage through the next analytic cells -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, consecutive certified analytic cells extend the `3/10`
rejecting-prime bound for odd composites from logarithmic scale eight through
100.71. Closed endpoint comparisons connect the five cells. -/
theorem exists_reject_03_analytic10071 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ (10071 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  by_cases h0 : Real.log n ≤ (10021 / 100 : ℝ)
  · exact exists_reject_03_analytic10021 hn ho hc hGRH hL h0
  · by_cases h1 : Real.log n ≤ (10031 / 100 : ℝ)
    · exact gammaAnalyticNext0_witness hn ho hc hGRH hL (le_of_not_ge h0) h1
    · by_cases h2 : Real.log n ≤ (10041 / 100 : ℝ)
      · exact gammaAnalyticNext1_witness hn ho hc hGRH hL (le_of_not_ge h1) h2
      · by_cases h3 : Real.log n ≤ (10051 / 100 : ℝ)
        · exact gammaAnalyticNext2_witness hn ho hc hGRH hL (le_of_not_ge h2) h3
        · by_cases h4 : Real.log n ≤ (10061 / 100 : ℝ)
          · exact gammaAnalyticNext3_witness hn ho hc hGRH hL (le_of_not_ge h3) h4
          · exact gammaAnalyticNext4_witness hn ho hc hGRH hL (le_of_not_ge h4) hU

end PseudoPrime.PrimeTestBounds.MillerRabin

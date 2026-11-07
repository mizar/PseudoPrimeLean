/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaAnalyticMore

/-! # Coverage through twenty further analytic cells -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, twenty certified analytic cells extend the `3/10` witness
bound for odd composites through logarithmic scale 105.1. Adjacent closed
endpoints connect each cell to the previous coverage. -/
theorem exists_reject_03_analytic1051 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ (1051 / 10 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  by_cases hprev : Real.log n ≤ (10071 / 100 : ℝ)
  · exact exists_reject_03_analytic10071 hn ho hc hGRH hL hprev
  by_cases h0 : Real.log n ≤ (2522 / 25 : ℝ)
  · exact gammaAnalyticMore0_witness hn ho hc hGRH hL (le_of_not_ge hprev) h0
  by_cases h1 : Real.log n ≤ (5053 / 50 : ℝ)
  · exact gammaAnalyticMore1_witness hn ho hc hGRH hL (le_of_not_ge h0) h1
  by_cases h2 : Real.log n ≤ (10123 / 100 : ℝ)
  · exact gammaAnalyticMore2_witness hn ho hc hGRH hL (le_of_not_ge h1) h2
  by_cases h3 : Real.log n ≤ (5071 / 50 : ℝ)
  · exact gammaAnalyticMore3_witness hn ho hc hGRH hL (le_of_not_ge h2) h3
  by_cases h4 : Real.log n ≤ (508 / 5 : ℝ)
  · exact gammaAnalyticMore4_witness hn ho hc hGRH hL (le_of_not_ge h3) h4
  by_cases h5 : Real.log n ≤ (10179 / 100 : ℝ)
  · exact gammaAnalyticMore5_witness hn ho hc hGRH hL (le_of_not_ge h4) h5
  by_cases h6 : Real.log n ≤ (10199 / 100 : ℝ)
  · exact gammaAnalyticMore6_witness hn ho hc hGRH hL (le_of_not_ge h5) h6
  by_cases h7 : Real.log n ≤ (10219 / 100 : ℝ)
  · exact gammaAnalyticMore7_witness hn ho hc hGRH hL (le_of_not_ge h6) h7
  by_cases h8 : Real.log n ≤ (10239 / 100 : ℝ)
  · exact gammaAnalyticMore8_witness hn ho hc hGRH hL (le_of_not_ge h7) h8
  by_cases h9 : Real.log n ≤ (10261 / 100 : ℝ)
  · exact gammaAnalyticMore9_witness hn ho hc hGRH hL (le_of_not_ge h8) h9
  by_cases h10 : Real.log n ≤ (10283 / 100 : ℝ)
  · exact gammaAnalyticMore10_witness hn ho hc hGRH hL (le_of_not_ge h9) h10
  by_cases h11 : Real.log n ≤ (5153 / 50 : ℝ)
  · exact gammaAnalyticMore11_witness hn ho hc hGRH hL (le_of_not_ge h10) h11
  by_cases h12 : Real.log n ≤ (10329 / 100 : ℝ)
  · exact gammaAnalyticMore12_witness hn ho hc hGRH hL (le_of_not_ge h11) h12
  by_cases h13 : Real.log n ≤ (10353 / 100 : ℝ)
  · exact gammaAnalyticMore13_witness hn ho hc hGRH hL (le_of_not_ge h12) h13
  by_cases h14 : Real.log n ≤ (10377 / 100 : ℝ)
  · exact gammaAnalyticMore14_witness hn ho hc hGRH hL (le_of_not_ge h13) h14
  by_cases h15 : Real.log n ≤ (5201 / 50 : ℝ)
  · exact gammaAnalyticMore15_witness hn ho hc hGRH hL (le_of_not_ge h14) h15
  by_cases h16 : Real.log n ≤ (10429 / 100 : ℝ)
  · exact gammaAnalyticMore16_witness hn ho hc hGRH hL (le_of_not_ge h15) h16
  by_cases h17 : Real.log n ≤ (2091 / 20 : ℝ)
  · exact gammaAnalyticMore17_witness hn ho hc hGRH hL (le_of_not_ge h16) h17
  by_cases h18 : Real.log n ≤ (10483 / 100 : ℝ)
  · exact gammaAnalyticMore18_witness hn ho hc hGRH hL (le_of_not_ge h17) h18
  exact gammaAnalyticMore19_witness hn ho hc hGRH hL (le_of_not_ge h18) hU

end PseudoPrime.PrimeTestBounds.MillerRabin

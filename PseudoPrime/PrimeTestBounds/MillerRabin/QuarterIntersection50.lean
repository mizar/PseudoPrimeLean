/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprimeRange50
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSquareRange55
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformClosed398375
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFactorDispatch

/-! # Common quarter-bound range for all factor types -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, every odd composite with logarithm between 8 and 50 has a
quarter-square rejecting prime. The factor classification combines the type ranges. -/
theorem quarter_all_8_50 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 50) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply quarter_of_factor_cases hn ho hc hGRH
  · intro hu
    exact quarter_uniform_8_398375 hn ho hu hGRH (by linarith only [hU])
  · intro p hp hd
    exact quarter_square_8_55 hn ho hp hd hL (by linarith only [hU])
  · intro p q hp hq hpq hprod
    exact quarter_semiprime_8_50 hn ho hp hq hpq hprod hGRH hL hU
  · exact le_rfl

end PseudoPrime.PrimeTestBounds.MillerRabin

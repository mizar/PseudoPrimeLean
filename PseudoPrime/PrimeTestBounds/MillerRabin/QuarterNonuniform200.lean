/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformKorseltTriple
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFactorDispatch
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSquareRange200
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprimeRange200

/-! # Nonuniform quarter witnesses through logarithmic scale 200 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, nonuniform odd composites with logarithm from 8 to 200 have a
quarter-square rejecting prime. Factor classification uses the square and
semiprime cumulative bounds without uniform interval certificates. -/
theorem quarter_nonuniform_8_200 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hu : ¬UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (8 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 200) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply quarter_of_factor_cases hn ho hc hGRH
  · intro h
    exact False.elim (hu h)
  · intro p hp hdiv
    exact quarter_square_8_200 hn ho hp hdiv hGRH hL hU
  · intro p q hp hq hpq hprod
    exact quarter_semiprime_8_200 hn ho hp hq hpq hprod hGRH hL hU
  · exact le_rfl

end PseudoPrime.PrimeTestBounds.MillerRabin

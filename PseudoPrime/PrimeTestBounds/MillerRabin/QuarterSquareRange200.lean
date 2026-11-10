/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSquareLow
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSquareFourth
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSquare425
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSquare55
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSquare63
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSquare68
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSquare68200

/-! # Square-factor quarter-bound witnesses from 8 to 200 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- An odd input with a prime-square divisor and logarithm from 8 to 200 has a
quarter-square rejecting prime. Independent square-factor intervals cover the range. -/
theorem quarter_square_8_200 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hdiv : p ^ 2 ∣ n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 200) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h96 : Real.log n ≤ 48 / 5
  · exact quarter_square_8_96 hn ho hp hdiv hL h96
  by_cases h20 : Real.log n ≤ 20
  · exact quarter_square_fourth hn ho hp hdiv (le_of_not_ge h96) h20
  by_cases h425 : Real.log n ≤ 85 / 2
  · exact quarter_square_20_425 hn ho hp hdiv (le_of_not_ge h20) h425
  by_cases h55 : Real.log n ≤ 55
  · exact quarter_square_425_55 hn ho hp hdiv (le_of_not_ge h425) h55
  by_cases h63 : Real.log n ≤ 63
  · exact quarter_square_55_63 hn ho hp hdiv (le_of_not_ge h55) h63
  by_cases h68 : Real.log n ≤ 68
  · exact quarter_square_63_68 hn ho hp hdiv (le_of_not_ge h63) h68
  exact quarter_square_68_200 hn ho hp hdiv hGRH (le_of_not_ge h68) hU

end PseudoPrime.PrimeTestBounds.MillerRabin

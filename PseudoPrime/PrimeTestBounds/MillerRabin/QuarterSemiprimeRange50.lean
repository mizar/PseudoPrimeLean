/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprimeFirst
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprimeSecond
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprimeThird
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprimeFourth
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprimeFifth
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprimeSixth
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprimeSeventh
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprimeEighth
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprimeNinth
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprimeTenth
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprimeEleventh
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprimeTwelfth
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprimeThirteenth
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprimeFourteenth
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprimeFifteenth
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprimeThrough20
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprime247
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprime282
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprime315
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprime34
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprime366
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprime386
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprime402
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprime439
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprime472
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprime50

/-! # Semiprime quarter-bound witnesses from logarithmic scale 8 to 50 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an odd product of two ordered distinct primes with logarithm from 8 to
50 has a quarter-square rejecting prime. Independent semiprime intervals cover the range. -/
theorem quarter_semiprime_8_50 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (8 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 50) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h10649 : Real.log n ≤ 10649 / 1000
  · exact quarter_semiprime_first hn ho hp hq hpq hprod hL h10649
  by_cases h1269 : Real.log n ≤ 1269 / 100
  · exact quarter_semiprime_second hn ho hp hq hpq hprod (le_of_not_ge h10649) h1269
  by_cases h1381 : Real.log n ≤ 1381 / 100
  · exact quarter_semiprime_third hn ho hp hq hpq hprod (le_of_not_ge h1269) h1381
  by_cases h143 : Real.log n ≤ 143 / 10
  · exact quarter_semiprime_fourth hn ho hp hq hpq hprod (le_of_not_ge h1381) h143
  by_cases h731 : Real.log n ≤ 731 / 50
  · exact quarter_semiprime_fifth hn ho hp hq hpq hprod (le_of_not_ge h143) h731
  by_cases h74 : Real.log n ≤ 74 / 5
  · exact quarter_semiprime_sixth hn ho hp hq hpq hprod (le_of_not_ge h731) h74
  by_cases h1496 : Real.log n ≤ 374 / 25
  · exact quarter_semiprime_seventh hn ho hp hq hpq hprod (le_of_not_ge h74) h1496
  by_cases h15 : Real.log n ≤ 15
  · exact quarter_semiprime_eighth hn ho hp hq hpq hprod (le_of_not_ge h1496) h15
  by_cases h1504 : Real.log n ≤ 376 / 25
  · exact quarter_semiprime_ninth hn ho hp hq hpq hprod (by linarith only [h15]) h1504
  by_cases h1529 : Real.log n ≤ 1529 / 100
  · exact quarter_semiprime_tenth hn ho hp hq hpq hprod (le_of_not_ge h1504) h1529
  by_cases h1537 : Real.log n ≤ 1537 / 100
  · exact quarter_semiprime_eleventh hn ho hp hq hpq hprod (le_of_not_ge h1529) h1537
  by_cases h1543 : Real.log n ≤ 1543 / 100
  · exact quarter_semiprime_twelfth hn ho hp hq hpq hprod (le_of_not_ge h1537) h1543
  by_cases h1550 : Real.log n ≤ 31 / 2
  · exact quarter_semiprime_thirteenth hn ho hp hq hpq hprod (le_of_not_ge h1543) h1550
  by_cases h1557 : Real.log n ≤ 1557 / 100
  · exact quarter_semiprime_fourteenth hn ho hp hq hpq hprod (le_of_not_ge h1550) h1557
  by_cases h1563 : Real.log n ≤ 1563 / 100
  · exact quarter_semiprime_fifteenth hn ho hp hq hpq hprod (le_of_not_ge h1557) h1563
  by_cases h20 : Real.log n ≤ 20
  · exact quarter_semiprime_through20 hn ho hp hq hpq hprod hGRH (le_of_not_ge h1563) h20
  by_cases h247 : Real.log n ≤ 247 / 10
  · exact quarter_semiprime_20_247 hn ho hp hq hpq hprod hGRH (le_of_not_ge h20) h247
  by_cases h282 : Real.log n ≤ 141 / 5
  · exact quarter_semiprime_247_282 hn ho hp hq hpq hprod hGRH (le_of_not_ge h247) h282
  by_cases h315 : Real.log n ≤ 63 / 2
  · exact quarter_semiprime_282_315 hn ho hp hq hpq hprod hGRH (le_of_not_ge h282) h315
  by_cases h34 : Real.log n ≤ 34
  · exact quarter_semiprime_315_34 hn ho hp hq hpq hprod hGRH (le_of_not_ge h315) h34
  by_cases h366 : Real.log n ≤ 183 / 5
  · exact quarter_semiprime_34_366 hn ho hp hq hpq hprod hGRH (le_of_not_ge h34) h366
  by_cases h386 : Real.log n ≤ 193 / 5
  · exact quarter_semiprime_366_386 hn ho hp hq hpq hprod hGRH (le_of_not_ge h366) h386
  by_cases h402 : Real.log n ≤ 201 / 5
  · exact quarter_semiprime_386_402 hn ho hp hq hpq hprod hGRH (le_of_not_ge h386) h402
  by_cases h439 : Real.log n ≤ 439 / 10
  · exact quarter_semiprime_402_439 hn ho hp hq hpq hprod hGRH (le_of_not_ge h402) h439
  by_cases h472 : Real.log n ≤ 236 / 5
  · exact quarter_semiprime_439_472 hn ho hp hq hpq hprod hGRH (le_of_not_ge h439) h472
  exact quarter_semiprime_472_50 hn ho hp hq hpq hprod hGRH (le_of_not_ge h472) hU

end PseudoPrime.PrimeTestBounds.MillerRabin

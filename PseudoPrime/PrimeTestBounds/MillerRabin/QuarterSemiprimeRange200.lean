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
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprime521
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprime539
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprime552
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprime563
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprime573
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprime580
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprime586
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprime591
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprime600
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprime609
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprime616
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprime622
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprime627
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprime630
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprime643
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprime654
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprime663
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprime670
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprime676
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprime680
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSemiprime68200

/-! # Semiprime quarter-bound witnesses from logarithmic scale 8 to 200 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an odd product of two ordered distinct primes with logarithm from 8 to
200 has a quarter-square rejecting prime. Independent semiprime intervals cover the range. -/
theorem quarter_semiprime_8_200 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (8 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 200) :
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
  by_cases h50 : Real.log n ≤ 50
  · exact quarter_semiprime_472_50 hn ho hp hq hpq hprod hGRH (le_of_not_ge h472) h50
  by_cases h521 : Real.log n ≤ 521 / 10
  · exact quarter_semiprime_50_521 hn ho hp hq hpq hprod hGRH (le_of_not_ge h50) h521
  by_cases h539 : Real.log n ≤ 539 / 10
  · exact quarter_semiprime_521_539 hn ho hp hq hpq hprod hGRH (le_of_not_ge h521) h539
  by_cases h552 : Real.log n ≤ 552 / 10
  · exact quarter_semiprime_539_552 hn ho hp hq hpq hprod hGRH (le_of_not_ge h539) h552
  by_cases h563 : Real.log n ≤ 563 / 10
  · exact quarter_semiprime_552_563 hn ho hp hq hpq hprod hGRH (by linarith only [h552]) h563
  by_cases h573 : Real.log n ≤ 573 / 10
  · exact quarter_semiprime_563_573 hn ho hp hq hpq hprod hGRH (le_of_not_ge h563) h573
  by_cases h580 : Real.log n ≤ 58
  · exact quarter_semiprime_573_580 hn ho hp hq hpq hprod hGRH (le_of_not_ge h573) h580
  by_cases h586 : Real.log n ≤ 293 / 5
  · exact quarter_semiprime_580_586 hn ho hp hq hpq hprod hGRH (le_of_not_ge h580) h586
  by_cases h591 : Real.log n ≤ 591 / 10
  · exact quarter_semiprime_586_591 hn ho hp hq hpq hprod hGRH (le_of_not_ge h586) h591
  by_cases h600 : Real.log n ≤ 60
  · exact quarter_semiprime_591_600 hn ho hp hq hpq hprod hGRH (le_of_not_ge h591) h600
  by_cases h609 : Real.log n ≤ 609 / 10
  · exact quarter_semiprime_600_609 hn ho hp hq hpq hprod hGRH (le_of_not_ge h600) h609
  by_cases h616 : Real.log n ≤ 308 / 5
  · exact quarter_semiprime_609_616 hn ho hp hq hpq hprod hGRH (le_of_not_ge h609) h616
  by_cases h622 : Real.log n ≤ 311 / 5
  · exact quarter_semiprime_616_622 hn ho hp hq hpq hprod hGRH (le_of_not_ge h616) h622
  by_cases h627 : Real.log n ≤ 627 / 10
  · exact quarter_semiprime_622_627 hn ho hp hq hpq hprod hGRH (le_of_not_ge h622) h627
  by_cases h630 : Real.log n ≤ 63
  · exact quarter_semiprime_627_630 hn ho hp hq hpq hprod hGRH (le_of_not_ge h627) h630
  by_cases h643 : Real.log n ≤ 643 / 10
  · exact quarter_semiprime_630_643 hn ho hp hq hpq hprod hGRH (le_of_not_ge h630) h643
  by_cases h654 : Real.log n ≤ 327 / 5
  · exact quarter_semiprime_643_654 hn ho hp hq hpq hprod hGRH (le_of_not_ge h643) h654
  by_cases h663 : Real.log n ≤ 663 / 10
  · exact quarter_semiprime_654_663 hn ho hp hq hpq hprod hGRH (le_of_not_ge h654) h663
  by_cases h670 : Real.log n ≤ 67
  · exact quarter_semiprime_663_670 hn ho hp hq hpq hprod hGRH (le_of_not_ge h663) h670
  by_cases h676 : Real.log n ≤ 338 / 5
  · exact quarter_semiprime_670_676 hn ho hp hq hpq hprod hGRH (le_of_not_ge h670) h676
  by_cases h680 : Real.log n ≤ 68
  · exact quarter_semiprime_676_680 hn ho hp hq hpq hprod hGRH (le_of_not_ge h676) h680
  exact quarter_semiprime_68_200 hn ho hp hq hpq hprod hGRH (le_of_not_ge h680) hU

end PseudoPrime.PrimeTestBounds.MillerRabin

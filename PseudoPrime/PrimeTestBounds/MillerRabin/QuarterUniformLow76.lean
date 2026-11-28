/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformKorseltTriple
public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformLow
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformCell56
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformCell58
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformCell59
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformAnchorRange
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformCell109
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformCell141
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformCell184
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformCell243
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformCell277
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformCell292
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformCell328
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformCell350
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformCell378
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformCell411
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformCell453
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformCell499
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformCell547
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformCell598
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformCell651
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformCell706
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformCell763
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformCell823
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformCell885
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformCell949
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformCell1015
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredCell34
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Uniform Korselt witnesses at logarithms up to 76 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an odd uniform Korselt triple with logarithm at most 76 has
a prime Miller–Rabin witness bounded by one quarter of the squared logarithm.
The proof joins the low arithmetic, anchor and fixed-cutoff leaves, then uses
the first centered comparison on radii 34 through 38. -/
theorem quarter_uniform_low76 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hU : Real.log n ≤ (76 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  by_cases h0 : Real.log n ≤ (76 / 5 : ℝ)
  · exact uniformKorselt_reject_quarter_low hn ho hu h0
  by_cases h1 : Real.log n ≤ (9577 / 625 : ℝ)
  · exact quarter_uniform_152_153232 hn ho hu hGRH (by linarith only [h0]) (by linarith only [h1])
  by_cases h2 : Real.log n ≤ (154413 / 10000 : ℝ)
  · exact
      quarter_uniform_153232_154413 hn ho hu hGRH (by linarith only [h1]) (by linarith only [h2])
  by_cases h3 : Real.log n ≤ (15621 / 1000 : ℝ)
  · exact
      quarter_uniform_154413_159963 hn ho hu hGRH (by linarith only [h2]) (by linarith only [h3])
  by_cases h4 : Real.log n ≤ (1131 / 50 : ℝ)
  · exact quarter_uniform_anchor_range hn ho hu hGRH (by linarith only [h3]) (by linarith only [h4])
  by_cases h5 : Real.log n ≤ (2379 / 100 : ℝ)
  · exact quarter_uniform_2262_2379 hn ho hu hGRH (by linarith only [h4]) (by linarith only [h5])
  by_cases h6 : Real.log n ≤ (2717 / 100 : ℝ)
  · exact quarter_uniform_2379_2717 hn ho hu hGRH (by linarith only [h5]) (by linarith only [h6])
  by_cases h7 : Real.log n ≤ (38997 / 1250 : ℝ)
  · exact quarter_uniform_2717_311976 hn ho hu hGRH (by linarith only [h6]) (by linarith only [h7])
  by_cases h8 : Real.log n ≤ (86153 / 2500 : ℝ)
  · exact
      quarter_uniform_311976_344612 hn ho hu hGRH (by linarith only [h7]) (by linarith only [h8])
  by_cases h9 : Real.log n ≤ (36 : ℝ)
  · exact quarter_uniform_344612_36 hn ho hu hGRH (by linarith only [h8]) (by linarith only [h9])
  by_cases h10 : Real.log n ≤ (37 : ℝ)
  · exact quarter_uniform_36_37 hn ho hu hGRH (by linarith only [h9]) (by linarith only [h10])
  by_cases h11 : Real.log n ≤ (387 / 10 : ℝ)
  · exact quarter_uniform_37_387 hn ho hu hGRH (by linarith only [h10]) (by linarith only [h11])
  by_cases h12 : Real.log n ≤ (404 / 10 : ℝ)
  · exact quarter_uniform_387_404 hn ho hu hGRH (by linarith only [h11]) (by linarith only [h12])
  by_cases h13 : Real.log n ≤ (421 / 10 : ℝ)
  · exact quarter_uniform_404_421 hn ho hu hGRH (by linarith only [h12]) (by linarith only [h13])
  by_cases h14 : Real.log n ≤ (439 / 10 : ℝ)
  · exact quarter_uniform_421_439 hn ho hu hGRH (by linarith only [h13]) (by linarith only [h14])
  by_cases h15 : Real.log n ≤ (462 / 10 : ℝ)
  · exact quarter_uniform_439_462 hn ho hu hGRH (by linarith only [h14]) (by linarith only [h15])
  by_cases h16 : Real.log n ≤ (488 / 10 : ℝ)
  · exact quarter_uniform_462_488 hn ho hu hGRH (by linarith only [h15]) (by linarith only [h16])
  by_cases h17 : Real.log n ≤ (507 / 10 : ℝ)
  · exact quarter_uniform_488_507 hn ho hu hGRH (by linarith only [h16]) (by linarith only [h17])
  by_cases h18 : Real.log n ≤ (529 / 10 : ℝ)
  · exact quarter_uniform_507_529 hn ho hu hGRH (by linarith only [h17]) (by linarith only [h18])
  by_cases h19 : Real.log n ≤ (554 / 10 : ℝ)
  · exact quarter_uniform_529_554 hn ho hu hGRH (by linarith only [h18]) (by linarith only [h19])
  by_cases h20 : Real.log n ≤ (573 / 10 : ℝ)
  · exact quarter_uniform_554_573 hn ho hu hGRH (by linarith only [h19]) (by linarith only [h20])
  by_cases h21 : Real.log n ≤ (596 / 10 : ℝ)
  · exact quarter_uniform_573_596 hn ho hu hGRH (by linarith only [h20]) (by linarith only [h21])
  by_cases h22 : Real.log n ≤ (617 / 10 : ℝ)
  · exact quarter_uniform_596_617 hn ho hu hGRH (by linarith only [h21]) (by linarith only [h22])
  by_cases h23 : Real.log n ≤ (643 / 10 : ℝ)
  · exact quarter_uniform_617_643 hn ho hu hGRH (by linarith only [h22]) (by linarith only [h23])
  by_cases h24 : Real.log n ≤ (659 / 10 : ℝ)
  · exact quarter_uniform_643_659 hn ho hu hGRH (by linarith only [h23]) (by linarith only [h24])
  by_cases h25 : Real.log n ≤ (68 : ℝ)
  · exact quarter_uniform_659_681 hn ho hu hGRH (by linarith only [h24]) (by linarith only [h25])
  let r : ℝ := Real.log n / 2
  have hlo : 34 ≤ r := by
    dsimp only [r]
    linarith only [le_of_not_ge h25]
  have hhi : r ≤ 70 := by
    dsimp only [r]
    linarith only [hU]
  have hcut : r ^ 2 ≤ (1 / 4 : ℝ) * Real.log n ^ 2 := by
    dsimp only [r]
    exact (by ring : (Real.log n / 2) ^ 2 = (1 / 4 : ℝ) * Real.log n ^ 2).le
  exact
    quarter_uniform_of_residual hn ho hu hGRH hlo
      (by
        dsimp only [r]; linarith only)
      hcut (quarter_centered_gap_34_70 hlo hhi)

end PseudoPrime.PrimeTestBounds.MillerRabin

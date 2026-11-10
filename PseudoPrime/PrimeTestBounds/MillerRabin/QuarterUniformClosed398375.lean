/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformKorseltTriple
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
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformCentered250
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformCentered328
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformCentered350
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformCentered360
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformFirst366
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformInterval390
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformInterval392
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformInterval394
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformInterval396
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformInterval397
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformInterval39725
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformInterval39775
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformInterval398
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformInterval398125
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformInterval39825
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformInterval398375

/-! # Uniform Korselt bound through logarithm 398.375 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a uniform Korselt triple with logarithm at most 398.375 admits a
prime Miller–Rabin witness below one quarter of the squared logarithm. -/
theorem quarter_uniform_8_398375 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hU : Real.log n ≤ (3187 / 8 : ℝ)) :
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
  by_cases h26 : Real.log n ≤ (250 : ℝ)
  · exact quarter_uniform_68_250 hn ho hu hGRH (by linarith only [h25]) (by linarith only [h26])
  by_cases h27 : Real.log n ≤ (328 : ℝ)
  · exact quarter_uniform_250_328 hn ho hu hGRH (by linarith only [h26]) (by linarith only [h27])
  by_cases h28 : Real.log n ≤ (350 : ℝ)
  · exact quarter_uniform_328_350 hn ho hu hGRH (by linarith only [h27]) (by linarith only [h28])
  by_cases h29 : Real.log n ≤ (360 : ℝ)
  · exact quarter_uniform_350_360 hn ho hu hGRH (by linarith only [h28]) (by linarith only [h29])
  by_cases h30 : Real.log n ≤ (366 : ℝ)
  · exact quarter_uniform_360_366 hn ho hu hGRH (by linarith only [h29]) (by linarith only [h30])
  by_cases h31 : Real.log n ≤ (390 : ℝ)
  · exact quarter_uniform_366_390 hn ho hu hGRH (by linarith only [h30]) (by linarith only [h31])
  by_cases h32 : Real.log n ≤ (392 : ℝ)
  · exact quarter_uniform_390_392 hn ho hu hGRH (by linarith only [h31]) (by linarith only [h32])
  by_cases h33 : Real.log n ≤ (394 : ℝ)
  · exact quarter_uniform_392_394 hn ho hu hGRH (by linarith only [h32]) (by linarith only [h33])
  by_cases h34 : Real.log n ≤ (396 : ℝ)
  · exact quarter_uniform_394_396 hn ho hu hGRH (by linarith only [h33]) (by linarith only [h34])
  by_cases h35 : Real.log n ≤ (397 : ℝ)
  · exact quarter_uniform_396_397 hn ho hu hGRH (by linarith only [h34]) (by linarith only [h35])
  by_cases h36 : Real.log n ≤ (1589 / 4 : ℝ)
  · exact quarter_uniform_397_39725 hn ho hu hGRH (by linarith only [h35]) (by linarith only [h36])
  by_cases h37 : Real.log n ≤ (1591 / 4 : ℝ)
  · exact
      quarter_uniform_39725_39775 hn ho hu hGRH (by linarith only [h36]) (by linarith only [h37])
  by_cases h38 : Real.log n ≤ (398 : ℝ)
  · exact quarter_uniform_39775_398 hn ho hu hGRH (by linarith only [h37]) (by linarith only [h38])
  by_cases h39 : Real.log n ≤ (3185 / 8 : ℝ)
  · exact quarter_uniform_398_398125 hn ho hu hGRH (by linarith only [h38]) (by linarith only [h39])
  by_cases h40 : Real.log n ≤ (1593 / 4 : ℝ)
  · exact
      quarter_uniform_398125_39825 hn ho hu hGRH (by linarith only [h39]) (by linarith only [h40])
  exact quarter_uniform_39825_398375 hn ho hu hGRH (by linarith only [h40]) hU

end PseudoPrime.PrimeTestBounds.MillerRabin

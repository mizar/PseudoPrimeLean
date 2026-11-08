/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell02
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell03
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell04
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell05
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell06
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell07
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell08
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell09
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell10
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell11
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell12
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell13
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell14
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell15
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell16
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell17
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell18
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell19
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell20
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell21
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell22
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell23
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell24
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell25
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell26
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell27
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell28
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell29
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell30
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell31
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell32
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell33
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell34
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell35
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell36
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell37
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell38
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell39
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Cell40

/-! # Connected uniform analytic cells -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, the checked finite cells from 30.461 to 100 each
give a 0.28 witness for a uniform three-prime Korselt product. -/
theorem target028_pair_cells_30461_100 {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) (hL : (30461 / 1000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 100000 / 1000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  by_cases h02 : Real.log n ≤ (30960 / 1000 : ℝ)
  · exact
      target028_cell02_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr hL h02
  by_cases h03 : Real.log n ≤ (31484 / 1000 : ℝ)
  · exact
      target028_cell03_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h02) h03
  by_cases h04 : Real.log n ≤ (32304 / 1000 : ℝ)
  · exact
      target028_cell04_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h03) h04
  by_cases h05 : Real.log n ≤ (33274 / 1000 : ℝ)
  · exact
      target028_cell05_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h04) h05
  by_cases h06 : Real.log n ≤ (34267 / 1000 : ℝ)
  · exact
      target028_cell06_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h05) h06
  by_cases h07 : Real.log n ≤ (35392 / 1000 : ℝ)
  · exact
      target028_cell07_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h06) h07
  by_cases h08 : Real.log n ≤ (36776 / 1000 : ℝ)
  · exact
      target028_cell08_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h07) h08
  by_cases h09 : Real.log n ≤ (38351 / 1000 : ℝ)
  · exact
      target028_cell09_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h08) h09
  by_cases h10 : Real.log n ≤ (40225 / 1000 : ℝ)
  · exact
      target028_cell10_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h09) h10
  by_cases h11 : Real.log n ≤ (42225 / 1000 : ℝ)
  · exact
      target028_cell11_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h10) h11
  by_cases h12 : Real.log n ≤ (44225 / 1000 : ℝ)
  · exact
      target028_cell12_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h11) h12
  by_cases h13 : Real.log n ≤ (46225 / 1000 : ℝ)
  · exact
      target028_cell13_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h12) h13
  by_cases h14 : Real.log n ≤ (48225 / 1000 : ℝ)
  · exact
      target028_cell14_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h13) h14
  by_cases h15 : Real.log n ≤ (50225 / 1000 : ℝ)
  · exact
      target028_cell15_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h14) h15
  by_cases h16 : Real.log n ≤ (52225 / 1000 : ℝ)
  · exact
      target028_cell16_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h15) h16
  by_cases h17 : Real.log n ≤ (54225 / 1000 : ℝ)
  · exact
      target028_cell17_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h16) h17
  by_cases h18 : Real.log n ≤ (56225 / 1000 : ℝ)
  · exact
      target028_cell18_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h17) h18
  by_cases h19 : Real.log n ≤ (58225 / 1000 : ℝ)
  · exact
      target028_cell19_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h18) h19
  by_cases h20 : Real.log n ≤ (60225 / 1000 : ℝ)
  · exact
      target028_cell20_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h19) h20
  by_cases h21 : Real.log n ≤ (62225 / 1000 : ℝ)
  · exact
      target028_cell21_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h20) h21
  by_cases h22 : Real.log n ≤ (64225 / 1000 : ℝ)
  · exact
      target028_cell22_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h21) h22
  by_cases h23 : Real.log n ≤ (66225 / 1000 : ℝ)
  · exact
      target028_cell23_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h22) h23
  by_cases h24 : Real.log n ≤ (68225 / 1000 : ℝ)
  · exact
      target028_cell24_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h23) h24
  by_cases h25 : Real.log n ≤ (70225 / 1000 : ℝ)
  · exact
      target028_cell25_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h24) h25
  by_cases h26 : Real.log n ≤ (72225 / 1000 : ℝ)
  · exact
      target028_cell26_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h25) h26
  by_cases h27 : Real.log n ≤ (74225 / 1000 : ℝ)
  · exact
      target028_cell27_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h26) h27
  by_cases h28 : Real.log n ≤ (76225 / 1000 : ℝ)
  · exact
      target028_cell28_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h27) h28
  by_cases h29 : Real.log n ≤ (78225 / 1000 : ℝ)
  · exact
      target028_cell29_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h28) h29
  by_cases h30 : Real.log n ≤ (80225 / 1000 : ℝ)
  · exact
      target028_cell30_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h29) h30
  by_cases h31 : Real.log n ≤ (82225 / 1000 : ℝ)
  · exact
      target028_cell31_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h30) h31
  by_cases h32 : Real.log n ≤ (84225 / 1000 : ℝ)
  · exact
      target028_cell32_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h31) h32
  by_cases h33 : Real.log n ≤ (86225 / 1000 : ℝ)
  · exact
      target028_cell33_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h32) h33
  by_cases h34 : Real.log n ≤ (88225 / 1000 : ℝ)
  · exact
      target028_cell34_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h33) h34
  by_cases h35 : Real.log n ≤ (90225 / 1000 : ℝ)
  · exact
      target028_cell35_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h34) h35
  by_cases h36 : Real.log n ≤ (92225 / 1000 : ℝ)
  · exact
      target028_cell36_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h35) h36
  by_cases h37 : Real.log n ≤ (94225 / 1000 : ℝ)
  · exact
      target028_cell37_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h36) h37
  by_cases h38 : Real.log n ≤ (96225 / 1000 : ℝ)
  · exact
      target028_cell38_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h37) h38
  by_cases h39 : Real.log n ≤ (98225 / 1000 : ℝ)
  · exact
      target028_cell39_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr (le_of_not_ge h38) h39
  exact
    target028_cell40_pair hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK hvq
      hvr (le_of_not_ge h39) hU

end PseudoPrime.PrimeTestBounds.MillerRabin

/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028TwoSupply2781
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Two585Grid
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028TwoSupply2916
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Two597Grid
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028TwoSupply3020
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Two607Grid
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028TwoSupply3088
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Two613Grid
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028TwoSupply3140
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Two618Grid
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Two585Cell
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028EvenEnvelope

/-! # Final two-group semiprime intervals -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The two-group count yields a 0.28 semiprime witness on
`[102062/1000, 103857/1000]` under GRH. -/
theorem target028_two_final_cell1 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (102062 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 103857 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_two2916 hn ho hp hq hpq hprod hGRH 597 5281184889100917312
      target028Two597_count (D := (43110 / 1000 : ℝ))
  · have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 5281184889100917312 63 32 (43110 / 1000) 45 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (48 : ℚ)) (d := (579107 / 100000 : ℚ)) (j := 6)
        (lo := (102062 / 1000 : ℝ)) (hi := (103857 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The two-group count yields a 0.28 semiprime witness on
`[103857/1000, 105018/1000]` under GRH. -/
theorem target028_two_final_cell2 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (103857 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 105018 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_two3020 hn ho hp hq hpq hprod hGRH 607 9123515200361240639
      target028Two607_count (D := (43657 / 1000 : ℝ))
  · have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 9123515200361240639 63 32 (43657 / 1000) 45 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (48 : ℚ)) (d := (579107 / 100000 : ℚ)) (j := 6)
        (lo := (103857 / 1000 : ℝ)) (hi := (105018 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The two-group count yields a 0.28 semiprime witness on
`[105018/1000, 105900/1000]` under GRH. -/
theorem target028_two_final_cell3 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (105018 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 105900 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_two3088 hn ho hp hq hpq hprod hGRH 613 13820018180402697404
      target028Two613_count (D := (44072 / 1000 : ℝ))
  · have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show
            Analysis.rationalLogIntervalCheck 13820018180402697404 64 32 (44072 / 1000) 46 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (48 : ℚ)) (d := (579107 / 100000 : ℚ)) (j := 6)
        (lo := (105018 / 1000 : ℝ)) (hi := (105900 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The two-group count yields a 0.28 semiprime witness on
`[105900/1000, 106000/1000]` under GRH. -/
theorem target028_two_final_cell4 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (105900 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 106000 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_two3140 hn ho hp hq hpq hprod hGRH 618 19242568089568639779
      target028Two618_count (D := (44403 / 1000 : ℝ))
  · have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show
            Analysis.rationalLogIntervalCheck 19242568089568639779 65 32 (44403 / 1000) 46 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (48 : ℚ)) (d := (579107 / 100000 : ℚ)) (j := 6)
        (lo := (105900 / 1000 : ℝ)) (hi := (106000 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The two-group certificates cover distinct semiprimes from logarithmic
scale 99.677 through 106. -/
theorem target028_semiprime_99677_106 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (99677 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 106) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h0 : Real.log n ≤ 102062 / 1000
  · exact target028_two_final_cell0 hn ho hp hq hpq hprod hGRH hL h0
  by_cases h1 : Real.log n ≤ 103857 / 1000
  · exact target028_two_final_cell1 hn ho hp hq hpq hprod hGRH (le_of_not_ge h0) h1
  by_cases h2 : Real.log n ≤ 105018 / 1000
  · exact target028_two_final_cell2 hn ho hp hq hpq hprod hGRH (le_of_not_ge h1) h2
  by_cases h3 : Real.log n ≤ 105900 / 1000
  · exact target028_two_final_cell3 hn ho hp hq hpq hprod hGRH (le_of_not_ge h2) h3
  exact
    target028_two_final_cell4 hn ho hp hq hpq hprod hGRH (le_of_not_ge h3) (by linarith only [hU])

end PseudoPrime.PrimeTestBounds.MillerRabin

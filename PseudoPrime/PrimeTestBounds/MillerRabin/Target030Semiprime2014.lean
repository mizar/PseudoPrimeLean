/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Seed89
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Semiprime1796

/-! # Semiprime coverage through logarithmic scale 20.14 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, the checked supply through 89 transfers any certified budget
through 110 to a rejecting semiprime witness when the local envelope fits. -/
theorem exists_prime_reject_semiprime_seed89 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget : ℕ) (hN : budget ≤ 110)
    {D X : ℝ} (hD : D ≤ Real.log (target030Seed89Row.getD budget 0 : ℝ)) (hB : (89 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_table hn ho hp hq hpq hprod hGRH target030Seed89Primes
      target030Seed89Weights 89 budget 110 target030Seed89Weight 10 (by norm_num only)
      target030Seed89_labels.1 (fun r hr ↦ (target030Seed89_prime_supply r hr).1)
      (fun r hr ↦ (target030Seed89_prime_supply r hr).2) target030Seed89_labels.2.2
      target030Seed89_weight_bounds target030Seed89_labels.2.1 hN target030Seed89Row
      target030Seed89Tail target030Seed89_checked hD hB hlocal

/-- Under GRH, the checked prime supply gives a rejecting prime on
`[17.96, 18.33]` for distinct semiprimes. -/
theorem target030_semiprime89_cell1 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (1796 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 1833 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed89 hn ho hp hq hpq hprod hGRH 98 (by decide) (D :=
      (8501 / 1000 : ℝ))
  · change (8501 / 1000 : ℝ) ≤ Real.log (4923 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 4923 14 32 (8501 / 1000) 11 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_envelope (lo := (1796 / 100 : ℝ)) (hi := (1833 / 100 : ℝ))
        (by norm_num only) hL hU
    all_goals norm_num only

/-- Under GRH, the checked prime supply gives a rejecting prime on
`[18.33, 18.67]` for distinct semiprimes. -/
theorem target030_semiprime89_cell2 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (1833 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 1867 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed89 hn ho hp hq hpq hprod hGRH 100 (by decide) (D :=
      (8634 / 1000 : ℝ))
  · change (8634 / 1000 : ℝ) ≤ Real.log (5624 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 5624 14 32 (8634 / 1000) 11 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_envelope (lo := (1833 / 100 : ℝ)) (hi := (1867 / 100 : ℝ))
        (by norm_num only) hL hU
    all_goals norm_num only

/-- Under GRH, the checked prime supply gives a rejecting prime on
`[18.67, 18.99]` for distinct semiprimes. -/
theorem target030_semiprime89_cell3 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (1867 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 1899 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed89 hn ho hp hq hpq hprod hGRH 102 (by decide) (D :=
      (8767 / 1000 : ℝ))
  · change (8767 / 1000 : ℝ) ≤ Real.log (6420 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 6420 14 32 (8767 / 1000) 11 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_envelope (lo := (1867 / 100 : ℝ)) (hi := (1899 / 100 : ℝ))
        (by norm_num only) hL hU
    all_goals norm_num only

/-- Under GRH, the checked prime supply gives a rejecting prime on
`[18.99, 19.29]` for distinct semiprimes. -/
theorem target030_semiprime89_cell4 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (1899 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 1929 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed89 hn ho hp hq hpq hprod hGRH 104 (by decide) (D :=
      (8899 / 1000 : ℝ))
  · change (8899 / 1000 : ℝ) ≤ Real.log (7326 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 7326 14 32 (8899 / 1000) 11 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_envelope (lo := (1899 / 100 : ℝ)) (hi := (1929 / 100 : ℝ))
        (by norm_num only) hL hU
    all_goals norm_num only

/-- Under GRH, the checked prime supply gives a rejecting prime on
`[19.29, 19.52]` for distinct semiprimes. -/
theorem target030_semiprime89_cell5 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (1929 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 1952 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed89 hn ho hp hq hpq hprod hGRH 105 (by decide) (D :=
      (8964 / 1000 : ℝ))
  · change (8964 / 1000 : ℝ) ≤ Real.log (7819 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 7819 14 32 (8964 / 1000) 11 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_envelope (lo := (1929 / 100 : ℝ)) (hi := (1952 / 100 : ℝ))
        (by norm_num only) hL hU
    all_goals norm_num only

/-- Under GRH, the checked prime supply gives a rejecting prime on
`[19.52, 19.72]` for distinct semiprimes. -/
theorem target030_semiprime89_cell6 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (1952 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 1972 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed89 hn ho hp hq hpq hprod hGRH 106 (by decide) (D :=
      (9029 / 1000 : ℝ))
  · change (9029 / 1000 : ℝ) ≤ Real.log (8344 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 8344 14 32 (9029 / 1000) 11 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_envelope (lo := (1952 / 100 : ℝ)) (hi := (1972 / 100 : ℝ))
        (by norm_num only) hL hU
    all_goals norm_num only

/-- Under GRH, the checked prime supply gives a rejecting prime on
`[19.72, 19.95]` for distinct semiprimes. -/
theorem target030_semiprime89_cell7 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (1972 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 1995 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed89 hn ho hp hq hpq hprod hGRH 108 (by decide) (D :=
      (9159 / 1000 : ℝ))
  · change (9159 / 1000 : ℝ) ≤ Real.log (9507 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 9507 14 32 (9159 / 1000) 11 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_envelope (lo := (1972 / 100 : ℝ)) (hi := (1995 / 100 : ℝ))
        (by norm_num only) hL hU
    all_goals norm_num only

/-- Under GRH, the checked prime supply gives a rejecting prime on
`[19.95, 20.14]` for distinct semiprimes. -/
theorem target030_semiprime89_cell8 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (1995 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 2014 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed89 hn ho hp hq hpq hprod hGRH 109 (by decide) (D :=
      (9222 / 1000 : ℝ))
  · change (9222 / 1000 : ℝ) ≤ Real.log (10126 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 10126 14 32 (9222 / 1000) 11 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_envelope (lo := (1995 / 100 : ℝ)) (hi := (2014 / 100 : ℝ))
        (by norm_num only) hL hU
    all_goals norm_num only

/-- Under GRH, the earlier coverage and eight checked cells give a 0.30
rejecting prime for every distinct semiprime with logarithm in `[8, 20.14]`. -/
theorem exists_prime_reject_03_semiprime_2014 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 2014 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h0 : Real.log n ≤ 449 / 25
  · exact exists_prime_reject_03_semiprime_1796 hn ho hp hq hpq hprod hGRH hL h0
  · by_cases h1 : Real.log n ≤ 1833 / 100
    · exact target030_semiprime89_cell1 hn ho hp hq hpq hprod hGRH (by linarith only [h0]) h1
    · by_cases h2 : Real.log n ≤ 1867 / 100
      · exact target030_semiprime89_cell2 hn ho hp hq hpq hprod hGRH (by linarith only [h1]) h2
      · by_cases h3 : Real.log n ≤ 1899 / 100
        · exact target030_semiprime89_cell3 hn ho hp hq hpq hprod hGRH (by linarith only [h2]) h3
        · by_cases h4 : Real.log n ≤ 1929 / 100
          · exact target030_semiprime89_cell4 hn ho hp hq hpq hprod hGRH (by linarith only [h3]) h4
          · by_cases h5 : Real.log n ≤ 1952 / 100
            · exact
                target030_semiprime89_cell5 hn ho hp hq hpq hprod hGRH (by linarith only [h4]) h5
            · by_cases h6 : Real.log n ≤ 1972 / 100
              · exact
                  target030_semiprime89_cell6 hn ho hp hq hpq hprod hGRH (by linarith only [h5]) h6
              · by_cases h7 : Real.log n ≤ 1995 / 100
                · exact
                    target030_semiprime89_cell7 hn ho hp hq hpq hprod hGRH (by linarith only [h6])
                      h7
                · exact
                    target030_semiprime89_cell8 hn ho hp hq hpq hprod hGRH (by linarith only [h7])
                      hU

end PseudoPrime.PrimeTestBounds.MillerRabin

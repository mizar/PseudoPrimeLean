/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine37Core

/-! # Semiprime cells from the refined twelve-prime supply -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined twelve-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[11900/1000, 12010/1000]`. -/
theorem target028_fine37_cell0 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (11900 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 12010 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine37_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 125 (by decide)
      (5655 / 1000)
  · change (5655 / 1000 : ℝ) ≤ Real.log (286 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 286 9 32 (5655 / 1000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined twelve-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[12010/1000, 12160/1000]`. -/
theorem target028_fine37_cell1 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (12010 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 12160 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine37_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 127 (by decide)
      (5726 / 1000)
  · change (5726 / 1000 : ℝ) ≤ Real.log (307 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 307 9 32 (5726 / 1000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined twelve-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[12160/1000, 12228/1000]`. -/
theorem target028_fine37_cell2 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (12160 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 12228 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine37_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 128 (by decide)
      (5758 / 1000)
  · change (5758 / 1000 : ℝ) ≤ Real.log (317 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 317 9 32 (5758 / 1000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined twelve-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[12228/1000, 12316/1000]`. -/
theorem target028_fine37_cell3 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (12228 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 12316 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine37_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 129 (by decide)
      (5799 / 1000)
  · change (5799 / 1000 : ℝ) ≤ Real.log (330 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 330 9 32 (5799 / 1000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined twelve-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[12316/1000, 12383/1000]`. -/
theorem target028_fine37_cell4 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (12316 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 12383 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine37_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 130 (by decide)
      (5831 / 1000)
  · change (5831 / 1000 : ℝ) ≤ Real.log (341 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 341 9 32 (5831 / 1000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined twelve-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[12383/1000, 12451/1000]`. -/
theorem target028_fine37_cell5 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (12383 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 12451 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine37_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 131 (by decide)
      (5863 / 1000)
  · change (5863 / 1000 : ℝ) ≤ Real.log (352 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 352 9 32 (5863 / 1000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

/-- The six checked cells cover distinct semiprimes from 11.9 to 12.451. -/
theorem target028_semiprime_119_12451 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (119 / 10 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 12451 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h0 : Real.log n ≤ 12010 / 1000
  · exact target028_fine37_cell0 hn ho hp hq hpq hprod hGRH (by linarith only [hL]) h0
  by_cases h1 : Real.log n ≤ 12160 / 1000
  · exact
      target028_fine37_cell1 hn ho hp hq hpq hprod hGRH (by linarith only [(le_of_not_ge h0)]) h1
  by_cases h2 : Real.log n ≤ 12228 / 1000
  · exact
      target028_fine37_cell2 hn ho hp hq hpq hprod hGRH (by linarith only [(le_of_not_ge h1)]) h2
  by_cases h3 : Real.log n ≤ 12316 / 1000
  · exact
      target028_fine37_cell3 hn ho hp hq hpq hprod hGRH (by linarith only [(le_of_not_ge h2)]) h3
  by_cases h4 : Real.log n ≤ 12383 / 1000
  · exact
      target028_fine37_cell4 hn ho hp hq hpq hprod hGRH (by linarith only [(le_of_not_ge h3)]) h4
  exact target028_fine37_cell5 hn ho hp hq hpq hprod hGRH (le_of_not_ge h4) hU

end PseudoPrime.PrimeTestBounds.MillerRabin

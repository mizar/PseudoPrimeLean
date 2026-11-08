/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine31Core

/-! # Semiprime cells from the refined eleven-prime supply -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined eleven-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[11330/1000, 11461/1000]`. -/
theorem target028_fine31_cell0 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (11330 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 11461 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine31_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 119 (by decide)
      (5397 / 1000)
  · change (5397 / 1000 : ℝ) ≤ Real.log (221 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 221 8 32 (5397 / 1000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined eleven-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[11461/1000, 11609/1000]`. -/
theorem target028_fine31_cell1 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (11461 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 11609 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine31_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 121 (by decide)
      (5467 / 1000)
  · change (5467 / 1000 : ℝ) ≤ Real.log (237 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 237 8 32 (5467 / 1000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined eleven-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[11609/1000, 11680/1000]`. -/
theorem target028_fine31_cell2 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (11609 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 11680 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine31_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 122 (by decide)
      (5500 / 1000)
  · change (5500 / 1000 : ℝ) ≤ Real.log (245 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 245 8 32 (5500 / 1000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined eleven-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[11680/1000, 11747/1000]`. -/
theorem target028_fine31_cell3 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (11680 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 11747 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine31_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 123 (by decide)
      (5532 / 1000)
  · change (5532 / 1000 : ℝ) ≤ Real.log (253 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 253 8 32 (5532 / 1000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined eleven-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[11747/1000, 11830/1000]`. -/
theorem target028_fine31_cell4 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (11747 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 11830 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine31_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 124 (by decide)
      (5571 / 1000)
  · change (5571 / 1000 : ℝ) ≤ Real.log (263 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 263 9 32 (5571 / 1000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined eleven-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[11830/1000, 11900/1000]`. -/
theorem target028_fine31_cell5 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (11830 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 11900 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine31_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 125 (by decide)
      (5608 / 1000)
  · change (5608 / 1000 : ℝ) ≤ Real.log (273 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 273 9 32 (5608 / 1000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

/-- Under GRH, a product of two distinct primes has a 0.28
rejecting prime throughout the interval `[11.33, 11.9]`. The refined
eleven-prime count covers each adjacent subinterval. -/
theorem target028_semiprime_1133_1190 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (1133 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 119 / 10) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h0 : Real.log n ≤ (11461 / 1000 : ℝ)
  · exact target028_fine31_cell0 hn ho hp hq hpq hprod hGRH (by linarith only [hL]) h0
  by_cases h1 : Real.log n ≤ (11609 / 1000 : ℝ)
  · exact target028_fine31_cell1 hn ho hp hq hpq hprod hGRH (le_of_not_ge h0) h1
  by_cases h2 : Real.log n ≤ (11680 / 1000 : ℝ)
  · exact target028_fine31_cell2 hn ho hp hq hpq hprod hGRH (le_of_not_ge h1) h2
  by_cases h3 : Real.log n ≤ (11747 / 1000 : ℝ)
  · exact target028_fine31_cell3 hn ho hp hq hpq hprod hGRH (le_of_not_ge h2) h3
  by_cases h4 : Real.log n ≤ (11830 / 1000 : ℝ)
  · exact target028_fine31_cell4 hn ho hp hq hpq hprod hGRH (le_of_not_ge h3) h4
  exact target028_fine31_cell5 hn ho hp hq hpq hprod hGRH (le_of_not_ge h4) (by linarith only [hU])

end PseudoPrime.PrimeTestBounds.MillerRabin

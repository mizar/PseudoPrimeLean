/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine47Core

/-! # Semiprime cells from the refined fifteen-prime supply -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined fifteen-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[13324/1000, 13479/1000]`. -/
theorem target028_fine47_cell0 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (13324 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 13479 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine47_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 141 (by decide)
      (6347 / 1000)
  · change (6347 / 1000 : ℝ) ≤ Real.log (571 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 571 10 32 (6347 / 1000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined fifteen-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[13479/1000, 13556/1000]`. -/
theorem target028_fine47_cell1 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (13479 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 13556 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine47_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 142 (by decide)
      (6383 / 1000)
  · change (6383 / 1000 : ℝ) ≤ Real.log (592 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 592 10 32 (6383 / 1000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined fifteen-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[13556/1000, 13626/1000]`. -/
theorem target028_fine47_cell2 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (13556 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 13626 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine47_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 143 (by decide)
      (6416 / 1000)
  · change (6416 / 1000 : ℝ) ≤ Real.log (612 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 612 10 32 (6416 / 1000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined fifteen-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[13626/1000, 13711/1000]`. -/
theorem target028_fine47_cell3 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (13626 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 13711 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine47_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 144 (by decide)
      (6456 / 1000)
  · change (6456 / 1000 : ℝ) ≤ Real.log (637 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 637 10 32 (6456 / 1000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined fifteen-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[13711/1000, 13777/1000]`. -/
theorem target028_fine47_cell4 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (13711 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 13777 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine47_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 145 (by decide)
      (6487 / 1000)
  · change (6487 / 1000 : ℝ) ≤ Real.log (657 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 657 10 32 (6487 / 1000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

/-- The five checked cells cover distinct semiprimes from 13.324 to 13.777. -/
theorem target028_semiprime_13324_13777 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (13324 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 13777 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h0 : Real.log n ≤ 13479 / 1000
  · exact target028_fine47_cell0 hn ho hp hq hpq hprod hGRH (by linarith only [hL]) h0
  by_cases h1 : Real.log n ≤ 13556 / 1000
  · exact
      target028_fine47_cell1 hn ho hp hq hpq hprod hGRH (by linarith only [(le_of_not_ge h0)]) h1
  by_cases h2 : Real.log n ≤ 13626 / 1000
  · exact
      target028_fine47_cell2 hn ho hp hq hpq hprod hGRH (by linarith only [(le_of_not_ge h1)]) h2
  by_cases h3 : Real.log n ≤ 13711 / 1000
  · exact
      target028_fine47_cell3 hn ho hp hq hpq hprod hGRH (by linarith only [(le_of_not_ge h2)]) h3
  exact target028_fine47_cell4 hn ho hp hq hpq hprod hGRH (le_of_not_ge h3) hU

end PseudoPrime.PrimeTestBounds.MillerRabin

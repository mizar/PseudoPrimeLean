/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine43Core

/-! # Semiprime cells from the refined fourteen-prime supply -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined fourteen-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[12451/1000, 12632/1000]`. -/
theorem target028_fine43_cell0 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (12451 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 12632 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine43_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 131 (by decide)
      (5948 / 1000)
  · change (5948 / 1000 : ℝ) ≤ Real.log (383 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 383 9 32 (5948 / 1000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined fourteen-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[12632/1000, 12791/1000]`. -/
theorem target028_fine43_cell1 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (12632 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 12791 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine43_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 133 (by decide)
      (6023 / 1000)
  · change (6023 / 1000 : ℝ) ≤ Real.log (413 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 413 9 32 (6023 / 1000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined fourteen-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[12791/1000, 12944/1000]`. -/
theorem target028_fine43_cell2 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (12791 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 12944 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine43_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 135 (by decide)
      (6095 / 1000)
  · change (6095 / 1000 : ℝ) ≤ Real.log (444 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 444 9 32 (6095 / 1000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined fourteen-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[12944/1000, 13021/1000]`. -/
theorem target028_fine43_cell3 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (12944 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 13021 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine43_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 136 (by decide)
      (6131 / 1000)
  · change (6131 / 1000 : ℝ) ≤ Real.log (460 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 460 9 32 (6131 / 1000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined fourteen-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[13021/1000, 13093/1000]`. -/
theorem target028_fine43_cell4 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (13021 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 13093 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine43_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 137 (by decide)
      (6165 / 1000)
  · change (6165 / 1000 : ℝ) ≤ Real.log (476 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 476 9 32 (6165 / 1000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined fourteen-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[13093/1000, 13171/1000]`. -/
theorem target028_fine43_cell5 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (13093 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 13171 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine43_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 138 (by decide)
      (6202 / 1000)
  · change (6202 / 1000 : ℝ) ≤ Real.log (494 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 494 9 32 (6202 / 1000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined fourteen-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[13171/1000, 13248/1000]`. -/
theorem target028_fine43_cell6 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (13171 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 13248 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine43_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 139 (by decide)
      (6238 / 1000)
  · change (6238 / 1000 : ℝ) ≤ Real.log (512 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 512 10 32 (6238 / 1000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined fourteen-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[13248/1000, 13324/1000]`. -/
theorem target028_fine43_cell7 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (13248 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 13324 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine43_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 140 (by decide)
      (6274 / 1000)
  · change (6274 / 1000 : ℝ) ≤ Real.log (531 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 531 10 32 (6274 / 1000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

/-- The eight checked cells cover distinct semiprimes from 12.451 to 13.324. -/
theorem target028_semiprime_12451_13324 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (12451 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 13324 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h0 : Real.log n ≤ 12632 / 1000
  · exact target028_fine43_cell0 hn ho hp hq hpq hprod hGRH (by linarith only [hL]) h0
  by_cases h1 : Real.log n ≤ 12791 / 1000
  · exact
      target028_fine43_cell1 hn ho hp hq hpq hprod hGRH (by linarith only [(le_of_not_ge h0)]) h1
  by_cases h2 : Real.log n ≤ 12944 / 1000
  · exact
      target028_fine43_cell2 hn ho hp hq hpq hprod hGRH (by linarith only [(le_of_not_ge h1)]) h2
  by_cases h3 : Real.log n ≤ 13021 / 1000
  · exact
      target028_fine43_cell3 hn ho hp hq hpq hprod hGRH (by linarith only [(le_of_not_ge h2)]) h3
  by_cases h4 : Real.log n ≤ 13093 / 1000
  · exact
      target028_fine43_cell4 hn ho hp hq hpq hprod hGRH (by linarith only [(le_of_not_ge h3)]) h4
  by_cases h5 : Real.log n ≤ 13171 / 1000
  · exact
      target028_fine43_cell5 hn ho hp hq hpq hprod hGRH (by linarith only [(le_of_not_ge h4)]) h5
  by_cases h6 : Real.log n ≤ 13248 / 1000
  · exact
      target028_fine43_cell6 hn ho hp hq hpq hprod hGRH (by linarith only [(le_of_not_ge h5)]) h6
  exact target028_fine43_cell7 hn ho hp hq hpq hprod hGRH (le_of_not_ge h6) hU

end PseudoPrime.PrimeTestBounds.MillerRabin

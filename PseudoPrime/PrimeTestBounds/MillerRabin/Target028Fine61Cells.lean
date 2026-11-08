/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine61Core

/-! # Semiprime cells from the refined eighteen-prime supply -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined eighteen-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[14800/1000, 14928/1000]`. -/
theorem target028_fine61_cell0 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (14800 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 14928 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine61_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 462 1129
      (le_of_eq target028_fine61_count462.symm) (70290 / 10000)
  · change (70290 / 10000 : ℝ) ≤ Real.log (1129 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 1129 11 32 (70290 / 10000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined eighteen-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[14928/1000, 15027/1000]`. -/
theorem target028_fine61_cell1 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (14928 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 15027 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine61_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 466 1183
      (le_of_eq target028_fine61_count466.symm) (70758 / 10000)
  · change (70758 / 10000 : ℝ) ≤ Real.log (1183 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 1183 11 32 (70758 / 10000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined eighteen-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[15027/1000, 15103/1000]`. -/
theorem target028_fine61_cell2 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (15027 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 15103 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine61_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 469 1226
      (le_of_eq target028_fine61_count469.symm) (71115 / 10000)
  · change (71115 / 10000 : ℝ) ≤ Real.log (1226 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 1226 11 32 (71115 / 10000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined eighteen-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[15103/1000, 15153/1000]`. -/
theorem target028_fine61_cell3 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (15103 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 15153 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine61_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 471 1255
      (le_of_eq target028_fine61_count471.symm) (71348 / 10000)
  · change (71348 / 10000 : ℝ) ≤ Real.log (1255 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 1255 11 32 (71348 / 10000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

/-- The four checked cells cover distinct semiprimes from 14.8 to 15.153. -/
theorem target028_semiprime_14800_15153 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (14800 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 15153 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h0 : Real.log n ≤ 14928 / 1000
  · exact target028_fine61_cell0 hn ho hp hq hpq hprod hGRH (by linarith only [hL]) h0
  by_cases h1 : Real.log n ≤ 15027 / 1000
  · exact
      target028_fine61_cell1 hn ho hp hq hpq hprod hGRH (by linarith only [(le_of_not_ge h0)]) h1
  by_cases h2 : Real.log n ≤ 15103 / 1000
  · exact
      target028_fine61_cell2 hn ho hp hq hpq hprod hGRH (by linarith only [(le_of_not_ge h1)]) h2
  exact target028_fine61_cell3 hn ho hp hq hpq hprod hGRH (le_of_not_ge h2) hU

end PseudoPrime.PrimeTestBounds.MillerRabin

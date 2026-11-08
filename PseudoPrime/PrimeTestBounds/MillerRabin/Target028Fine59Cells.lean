/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine59Core

/-! # Semiprime cells from the refined seventeen-prime supply -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined seventeen-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[14518/1000, 14623/1000]`. -/
theorem target028_fine59_cell0 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (14518 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 14623 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine59_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 453 978
      (le_of_eq target028_fine59_count453.symm) (68855 / 10000)
  · change (68855 / 10000 : ℝ) ≤ Real.log (978 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 978 10 32 (68855 / 10000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined seventeen-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[14623/1000, 14700/1000]`. -/
theorem target028_fine59_cell1 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (14623 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 14700 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine59_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 456 1014
      (le_of_eq target028_fine59_count456.symm) (69216 / 10000)
  · change (69216 / 10000 : ℝ) ≤ Real.log (1014 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 1014 10 32 (69216 / 10000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined seventeen-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[14700/1000, 14747/1000]`. -/
theorem target028_fine59_cell2 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (14700 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 14747 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine59_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 458 1037
      (le_of_eq target028_fine59_count458.symm) (69440 / 10000)
  · change (69440 / 10000 : ℝ) ≤ Real.log (1037 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 1037 11 32 (69440 / 10000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined seventeen-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[14747/1000, 14800/1000]`. -/
theorem target028_fine59_cell3 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (14747 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 14800 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine59_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 460 1063
      (le_of_eq target028_fine59_count460.symm) (69688 / 10000)
  · change (69688 / 10000 : ℝ) ≤ Real.log (1063 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 1063 11 32 (69688 / 10000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

/-- The four checked cells cover distinct semiprimes from 14.518 to 14.8. -/
theorem target028_semiprime_14518_14800 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (14518 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 14800 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h0 : Real.log n ≤ 14623 / 1000
  · exact target028_fine59_cell0 hn ho hp hq hpq hprod hGRH (by linarith only [hL]) h0
  by_cases h1 : Real.log n ≤ 14700 / 1000
  · exact
      target028_fine59_cell1 hn ho hp hq hpq hprod hGRH (by linarith only [(le_of_not_ge h0)]) h1
  by_cases h2 : Real.log n ≤ 14747 / 1000
  · exact
      target028_fine59_cell2 hn ho hp hq hpq hprod hGRH (by linarith only [(le_of_not_ge h1)]) h2
  exact target028_fine59_cell3 hn ho hp hq hpq hprod hGRH (le_of_not_ge h2) hU

end PseudoPrime.PrimeTestBounds.MillerRabin

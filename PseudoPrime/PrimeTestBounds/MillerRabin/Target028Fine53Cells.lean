/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine53Core

/-! # Semiprime cells from the refined sixteen-prime supply -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined sixteen-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[13777/1000, 13955/1000]`. -/
theorem target028_fine53_cell0 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (13777 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 13955 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine53_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 430 (by decide)
      (65708 / 10000)
  · change (65708 / 10000 : ℝ) ≤ Real.log (714 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 714 10 32 (65708 / 10000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined sixteen-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[13955/1000, 14087/1000]`. -/
theorem target028_fine53_cell1 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (13955 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 14087 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine53_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 435 (by decide)
      (66333 / 10000)
  · change (66333 / 10000 : ℝ) ≤ Real.log (760 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 760 10 32 (66333 / 10000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined sixteen-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[14087/1000, 14183/1000]`. -/
theorem target028_fine53_cell2 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (14087 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 14183 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine53_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 439 (by decide)
      (66783 / 10000)
  · change (66783 / 10000 : ℝ) ≤ Real.log (795 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 795 10 32 (66783 / 10000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined sixteen-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[14183/1000, 14264/1000]`. -/
theorem target028_fine53_cell3 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (14183 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 14264 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine53_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 442 (by decide)
      (67165 / 10000)
  · change (67165 / 10000 : ℝ) ≤ Real.log (826 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 826 10 32 (67165 / 10000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined sixteen-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[14264/1000, 14342/1000]`. -/
theorem target028_fine53_cell4 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (14264 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 14342 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine53_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 445 (by decide)
      (67534 / 10000)
  · change (67534 / 10000 : ℝ) ≤ Real.log (857 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 857 10 32 (67534 / 10000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined sixteen-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[14342/1000, 14392/1000]`. -/
theorem target028_fine53_cell5 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (14342 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 14392 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine53_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 447 (by decide)
      (67765 / 10000)
  · change (67765 / 10000 : ℝ) ≤ Real.log (877 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 877 10 32 (67765 / 10000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined sixteen-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[14392/1000, 14439/1000]`. -/
theorem target028_fine53_cell6 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (14392 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 14439 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine53_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 449 (by decide)
      (67990 / 10000)
  · change (67990 / 10000 : ℝ) ≤ Real.log (897 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 897 10 32 (67990 / 10000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined sixteen-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[14439/1000, 14465/1000]`. -/
theorem target028_fine53_cell7 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (14439 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 14465 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine53_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 450 (by decide)
      (68112 / 10000)
  · change (68112 / 10000 : ℝ) ≤ Real.log (908 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 908 10 32 (68112 / 10000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined sixteen-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[14465/1000, 14491/1000]`. -/
theorem target028_fine53_cell8 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (14465 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 14491 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine53_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 451 (by decide)
      (68232 / 10000)
  · change (68232 / 10000 : ℝ) ≤ Real.log (919 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 919 10 32 (68232 / 10000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

-- Reducing the finite count row requires additional recursion depth.
set_option maxRecDepth 65536 in
/-- The refined sixteen-prime count gives a 0.28 semiprime witness on
the certified logarithmic interval `[14491/1000, 14518/1000]`. -/
theorem target028_fine53_cell9 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (14491 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 14518 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_fine53_core hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 452 (by decide)
      (68362 / 10000)
  · change (68362 / 10000 : ℝ) ≤ Real.log (931 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 931 10 32 (68362 / 10000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

/-- The ten checked cells cover distinct semiprimes from 13.777 to 14.518. -/
theorem target028_semiprime_13777_14518 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (13777 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 14518 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h0 : Real.log n ≤ 13955 / 1000
  · exact target028_fine53_cell0 hn ho hp hq hpq hprod hGRH (by linarith only [hL]) h0
  by_cases h1 : Real.log n ≤ 14087 / 1000
  · exact
      target028_fine53_cell1 hn ho hp hq hpq hprod hGRH (by linarith only [(le_of_not_ge h0)]) h1
  by_cases h2 : Real.log n ≤ 14183 / 1000
  · exact
      target028_fine53_cell2 hn ho hp hq hpq hprod hGRH (by linarith only [(le_of_not_ge h1)]) h2
  by_cases h3 : Real.log n ≤ 14264 / 1000
  · exact
      target028_fine53_cell3 hn ho hp hq hpq hprod hGRH (by linarith only [(le_of_not_ge h2)]) h3
  by_cases h4 : Real.log n ≤ 14342 / 1000
  · exact
      target028_fine53_cell4 hn ho hp hq hpq hprod hGRH (by linarith only [(le_of_not_ge h3)]) h4
  by_cases h5 : Real.log n ≤ 14392 / 1000
  · exact
      target028_fine53_cell5 hn ho hp hq hpq hprod hGRH (by linarith only [(le_of_not_ge h4)]) h5
  by_cases h6 : Real.log n ≤ 14439 / 1000
  · exact
      target028_fine53_cell6 hn ho hp hq hpq hprod hGRH (by linarith only [(le_of_not_ge h5)]) h6
  by_cases h7 : Real.log n ≤ 14465 / 1000
  · exact
      target028_fine53_cell7 hn ho hp hq hpq hprod hGRH (by linarith only [(le_of_not_ge h6)]) h7
  by_cases h8 : Real.log n ≤ 14491 / 1000
  · exact
      target028_fine53_cell8 hn ho hp hq hpq hprod hGRH (by linarith only [(le_of_not_ge h7)]) h8
  exact target028_fine53_cell9 hn ho hp hq hpq hprod hGRH (le_of_not_ge h8) hU

end PseudoPrime.PrimeTestBounds.MillerRabin

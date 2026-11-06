/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030SemiprimeSeed43

/-! # Semiprime coverage through logarithmic scale 14.8 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, the weighted table through 43 gives a 0.30 semiprime
witness on `[12.17, 13.13]`, using the certified count and local envelope. -/
theorem target030_semiprime43_cell1 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (1217 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 1313 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed43 hn ho hp hq hpq hprod hGRH 66 (by decide) (D :=
      (5940 / 1000 : ℝ))
  · change (5940 / 1000 : ℝ) ≤ Real.log (380 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 380 9 32 (5940 / 1000) 7 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only at ⊢
    exact h
  · nlinarith only [hL]
  · apply
      target030_semiprime_envelope (lo := (1217 / 100 : ℝ)) (hi := (1313 / 100 : ℝ))
        (by norm_num only) hL hU
    all_goals norm_num only

/-- Under GRH, the weighted table through 43 gives a 0.30 semiprime
witness on `[13.13, 13.89]`, using the certified count and local envelope. -/
theorem target030_semiprime43_cell2 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (1313 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 1389 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed43 hn ho hp hq hpq hprod hGRH 71 (by decide) (D :=
      (6285 / 1000 : ℝ))
  · change (6285 / 1000 : ℝ) ≤ Real.log (537 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 537 10 32 (6285 / 1000) 7 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only at ⊢
    exact h
  · nlinarith only [hL]
  · apply
      target030_semiprime_envelope (lo := (1313 / 100 : ℝ)) (hi := (1389 / 100 : ℝ))
        (by norm_num only) hL hU
    all_goals norm_num only

/-- Under GRH, the weighted table through 43 gives a 0.30 semiprime
witness on `[13.89, 14.66]`, using the certified count and local envelope. -/
theorem target030_semiprime43_cell3 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (1389 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 1466 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed43 hn ho hp hq hpq hprod hGRH 76 (by decide) (D :=
      (6632 / 1000 : ℝ))
  · change (6632 / 1000 : ℝ) ≤ Real.log (759 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 759 10 32 (6632 / 1000) 7 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only at ⊢
    exact h
  · nlinarith only [hL]
  · apply
      target030_semiprime_envelope (lo := (1389 / 100 : ℝ)) (hi := (1466 / 100 : ℝ))
        (by norm_num only) hL hU
    all_goals norm_num only

/-- Under GRH, the weighted table through 43 gives a 0.30 semiprime
witness on `[14.66, 14.8]`, using the certified count and local envelope. -/
theorem target030_semiprime43_cell4 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (1466 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 1480 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed43 hn ho hp hq hpq hprod hGRH 77 (by decide) (D :=
      (6695 / 1000 : ℝ))
  · change (6695 / 1000 : ℝ) ≤ Real.log (809 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 809 10 32 (6695 / 1000) 7 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only at ⊢
    exact h
  · nlinarith only [hL]
  · apply
      target030_semiprime_envelope (lo := (1466 / 100 : ℝ)) (hi := (1480 / 100 : ℝ))
        (by norm_num only) hL hU
    all_goals norm_num only

/-- Under GRH, every distinct odd semiprime with logarithm in `[8, 14.8]`
has a 0.30 rejecting prime. Four weighted-count intervals extend the earlier
coverage through 12.17. -/
theorem exists_prime_reject_03_semiprime_148 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 74 / 5) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h1 : Real.log n ≤ 1217 / 100
  · exact exists_prime_reject_03_semiprime_1217 hn ho hp hq hpq hprod hGRH hL h1
  · by_cases h2 : Real.log n ≤ 1313 / 100
    · exact target030_semiprime43_cell1 hn ho hp hq hpq hprod hGRH (le_of_not_ge h1) h2
    · by_cases h3 : Real.log n ≤ 1389 / 100
      · exact target030_semiprime43_cell2 hn ho hp hq hpq hprod hGRH (le_of_not_ge h2) h3
      · by_cases h4 : Real.log n ≤ 1466 / 100
        · exact target030_semiprime43_cell3 hn ho hp hq hpq hprod hGRH (le_of_not_ge h3) h4
        · exact
            target030_semiprime43_cell4 hn ho hp hq hpq hprod hGRH (le_of_not_ge h4)
              (by linarith only [hU])

end PseudoPrime.PrimeTestBounds.MillerRabin

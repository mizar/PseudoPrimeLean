/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030FurtherCells

/-! # Extending the low semiprime range with one weighted count -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- On `[10.614, 11.19]`, the local envelope for the budget-58 count is at
most the 0.30 target. Both terms of the maximum are bounded by `5477/10000`
times the logarithmic scale, whose square is below 0.30. -/
theorem target030_semiprime_envelope_1119 {n : ℕ} (hL : (10614 / 1000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 1119 / 100) :
    localFullEnvelope (max ((58 : ℝ) / 10) (Real.log n - 5062 / 1000)) ≤
      (3 / 10 : ℝ) * Real.log n ^ 2 := by
  have hmax : max ((58 : ℝ) / 10) (Real.log n - 5062 / 1000) ≤ (5477 / 10000 : ℝ) * Real.log n := by
    apply max_le
    · linarith only [hL]
    · linarith only [hU]
  have hnonneg : (0 : ℝ) ≤ max ((58 : ℝ) / 10) (Real.log n - 5062 / 1000) :=
    (by norm_num only : (0 : ℝ) ≤ 58 / 10).trans (le_max_left _ _)
  have hsq := mul_self_le_mul_self hnonneg hmax
  have hLsq := sq_nonneg (Real.log n)
  exact (min_le_left _ _).trans ((min_le_left _ _).trans (by nlinarith only [hsq, hLsq]))

/-- Under GRH, a distinct odd semiprime with logarithm in `[10.614, 11.19]`
has a 0.30 rejecting prime. The budget-58 table has 158 products, and a
rational logarithm certificate and the local envelope discharge its bounds. -/
theorem exists_prime_reject_03_semiprime_1119_cell {n p q : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (10614 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 1119 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_supply58 hn ho hp hq hpq hprod hGRH 58 (by decide) (D := (5062 / 1000 : ℝ))
  · change (5062 / 1000 : ℝ) ≤ Real.log (158 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 158 8 32 (5062 / 1000) 6 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only at ⊢
    exact h
  · nlinarith only [hL]
  · exact target030_semiprime_envelope_1119 hL hU

/-- Under GRH, every distinct odd semiprime with logarithm in `[8, 11.19]`
has a 0.30 rejecting prime. The new continuous interval meets the earlier
eight checked cells at 10.614. -/
theorem exists_prime_reject_03_semiprime_1119 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 1119 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h : Real.log n ≤ 10614 / 1000
  · exact exists_prime_reject_03_semiprime_10614 hn ho hp hq hpq hprod hGRH hL h
  · exact exists_prime_reject_03_semiprime_1119_cell hn ho hp hq hpq hprod hGRH (le_of_not_ge h) hU

end PseudoPrime.PrimeTestBounds.MillerRabin

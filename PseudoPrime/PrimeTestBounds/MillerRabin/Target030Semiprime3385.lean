/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Seed89Count197
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030EvenEnvelope
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Semiprime2014

/-! # Semiprime coverage through logarithmic scale 33.85 -/

@[expose] public section

set_option maxRecDepth 16384

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The checked supply through 89 yields semiprime witnesses for budgets
through 197 whenever the count and local-envelope conditions hold. -/
theorem exists_prime_reject_semiprime_seed89_197 {n p q : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget : ℕ) (hN : budget ≤ 197)
    {D X : ℝ} (hD : D ≤ Real.log (target030Seed89Row197.getD budget 0 : ℝ)) (hB : (89 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_table hn ho hp hq hpq hprod hGRH target030Seed89Primes
      target030Seed89Weights 89 budget 197 target030Seed89Weight 10 (by norm_num only)
      target030Seed89_labels.1 (fun r hr ↦ (target030Seed89_prime_supply r hr).1)
      (fun r hr ↦ (target030Seed89_prime_supply r hr).2) target030Seed89_labels.2.2
      target030Seed89_weight_bounds target030Seed89_labels.2.1 hN target030Seed89Row197
      target030Seed89Tail197 target030Seed89_checked197 hD hB hlocal

/-- The checked count and first even correction give a 0.30 semiprime
witness on this closed logarithmic interval. -/
theorem target030_semiprime89_even_cell1 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (2014 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 2550 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed89_197 hn ho hp hq hpq hprod hGRH 142 (by decide) (D :=
      (11225 / 1000 : ℝ))
  · change (11225 / 1000 : ℝ) ≤ Real.log (75034 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 75034 17 32 (11225 / 1000) 16 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply target030_semiprime_even_envelope (lo := (2014 / 100 : ℝ)) (hi := (2550 / 100 : ℝ)) hL hU
    all_goals norm_num only

/-- The checked count and first even correction give a 0.30 semiprime
witness on this closed logarithmic interval. -/
theorem target030_semiprime89_even_cell2 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (2550 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 3008 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed89_197 hn ho hp hq hpq hprod hGRH 172 (by decide) (D :=
      (12867 / 1000 : ℝ))
  · change (12867 / 1000 : ℝ) ≤ Real.log (387518 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 387518 19 32 (12867 / 1000) 16 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply target030_semiprime_even_envelope (lo := (2550 / 100 : ℝ)) (hi := (3008 / 100 : ℝ)) hL hU
    all_goals norm_num only

/-- The checked count and first even correction give a 0.30 semiprime
witness on this closed logarithmic interval. -/
theorem target030_semiprime89_even_cell3 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (3008 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 3385 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed89_197 hn ho hp hq hpq hprod hGRH 197 (by decide) (D :=
      (14132 / 1000 : ℝ))
  · change (14132 / 1000 : ℝ) ≤ Real.log (1372508 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 1372508 21 32 (14132 / 1000) 16 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply target030_semiprime_even_envelope (lo := (3008 / 100 : ℝ)) (hi := (3385 / 100 : ℝ)) hL hU
    all_goals norm_num only

/-- Under GRH, every distinct semiprime with logarithm in `[8, 33.85]`
has a 0.30 rejecting prime. Three corrected cells extend the earlier range. -/
theorem exists_prime_reject_03_semiprime_3385 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 3385 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h0 : Real.log n ≤ 2014 / 100
  · exact exists_prime_reject_03_semiprime_2014 hn ho hp hq hpq hprod hGRH hL h0
  · by_cases h1 : Real.log n ≤ 2550 / 100
    · exact target030_semiprime89_even_cell1 hn ho hp hq hpq hprod hGRH (le_of_not_ge h0) h1
    · by_cases h2 : Real.log n ≤ 3008 / 100
      · exact target030_semiprime89_even_cell2 hn ho hp hq hpq hprod hGRH (le_of_not_ge h1) h2
      · exact target030_semiprime89_even_cell3 hn ho hp hq hpq hprod hGRH (le_of_not_ge h2) hU

end PseudoPrime.PrimeTestBounds.MillerRabin

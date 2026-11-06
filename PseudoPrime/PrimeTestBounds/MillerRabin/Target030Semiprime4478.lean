/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Seed89Count282
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030EvenEnvelope
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Semiprime3385

/-! # Semiprime coverage through logarithmic scale 44.78 -/

@[expose] public section

set_option maxRecDepth 32768

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The checked supply through 89 yields semiprime witnesses for budgets
through 282 whenever the count and local-envelope conditions hold. -/
theorem exists_prime_reject_semiprime_seed89_282 {n p q : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget : ℕ) (hN : budget ≤ 282)
    {D X : ℝ} (hD : D ≤ Real.log (target030Seed89Row282.getD budget 0 : ℝ)) (hB : (89 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_table hn ho hp hq hpq hprod hGRH target030Seed89Primes
      target030Seed89Weights 89 budget 282 target030Seed89Weight 10 (by norm_num only)
      target030Seed89_labels.1 (fun r hr ↦ (target030Seed89_prime_supply r hr).1)
      (fun r hr ↦ (target030Seed89_prime_supply r hr).2) target030Seed89_labels.2.2
      target030Seed89_weight_bounds target030Seed89_labels.2.1 hN target030Seed89Row282
      target030Seed89Tail282 target030Seed89_checked282 hD hB hlocal

/-- The checked count and even anchor give a 0.30 semiprime witness on
this closed logarithmic interval. -/
theorem target030_semiprime89_anchor_cell1 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (3385 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 3841 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed89_282 hn ho hp hq hpq hprod hGRH 228 (by decide) (D :=
      (15593 / 1000 : ℝ))
  · change (15593 / 1000 : ℝ) ≤ Real.log (5915194 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 5915194 23 32 (15593 / 1000) 19 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (16 : ℚ)) (d := (85669 / 20000 : ℚ)) (j := 4) (lo :=
        (3385 / 100 : ℝ)) (hi := (3841 / 100 : ℝ))
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked count and even anchor give a 0.30 semiprime witness on
this closed logarithmic interval. -/
theorem target030_semiprime89_anchor_cell2 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (3841 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 4201 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed89_282 hn ho hp hq hpq hprod hGRH 253 (by decide) (D :=
      (16697 / 1000 : ℝ))
  · change (16697 / 1000 : ℝ) ≤ Real.log (17843263 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 17843263 25 32 (16697 / 1000) 19 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (16 : ℚ)) (d := (85669 / 20000 : ℚ)) (j := 4) (lo :=
        (3841 / 100 : ℝ)) (hi := (4201 / 100 : ℝ))
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked count and even anchor give a 0.30 semiprime witness on
this closed logarithmic interval. -/
theorem target030_semiprime89_anchor_cell3 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (4201 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 4478 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed89_282 hn ho hp hq hpq hprod hGRH 272 (by decide) (D :=
      (17497 / 1000 : ℝ))
  · change (17497 / 1000 : ℝ) ≤ Real.log (39721656 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 39721656 26 32 (17497 / 1000) 19 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (16 : ℚ)) (d := (85669 / 20000 : ℚ)) (j := 4) (lo :=
        (4201 / 100 : ℝ)) (hi := (4478 / 100 : ℝ))
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- Under GRH, every distinct semiprime with logarithm in `[8, 44.78]`
has a 0.30 rejecting prime. Three anchored cells extend the earlier range. -/
theorem exists_prime_reject_03_semiprime_4478 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 4478 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h0 : Real.log n ≤ 3385 / 100
  · exact exists_prime_reject_03_semiprime_3385 hn ho hp hq hpq hprod hGRH hL h0
  · by_cases h1 : Real.log n ≤ 3841 / 100
    · exact target030_semiprime89_anchor_cell1 hn ho hp hq hpq hprod hGRH (le_of_not_ge h0) h1
    · by_cases h2 : Real.log n ≤ 4201 / 100
      · exact target030_semiprime89_anchor_cell2 hn ho hp hq hpq hprod hGRH (le_of_not_ge h1) h2
      · exact target030_semiprime89_anchor_cell3 hn ho hp hq hpq hprod hGRH (le_of_not_ge h2) hU

end PseudoPrime.PrimeTestBounds.MillerRabin

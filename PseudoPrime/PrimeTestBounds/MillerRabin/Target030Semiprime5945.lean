/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Seed113Table
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Semiprime5551

/-! # Semiprime coverage through logarithmic scale 59.45 -/

@[expose] public section

set_option maxRecDepth 32768

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The checked supply through 113 yields semiprime witnesses for budgets
through 358 whenever the count and local-envelope conditions hold. -/
theorem exists_prime_reject_semiprime_seed113 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget : ℕ) (hN : budget ≤ 358)
    {D X : ℝ} (hD : D ≤ Real.log (target030Seed113Row6.getD budget 0 : ℝ)) (hB : (113 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_table hn ho hp hq hpq hprod hGRH target030Seed113Primes
      target030Seed113Weights 113 budget 358 target030Seed113Weight 10 (by norm_num only)
      target030Seed113_labels.1 (fun r hr ↦ (target030Seed113_prime_supply r hr).1)
      (fun r hr ↦ (target030Seed113_prime_supply r hr).2) target030Seed113_labels.2.2
      target030Seed113_weight_bounds target030Seed113_labels.2.1 hN target030Seed113Row6
      ([target030Seed113Row5, target030Seed113Row4, target030Seed113Row3, target030Seed113Row2,
          target030Seed113Row1, target030Seed89Row358] ++
        target030Seed89Tail358)
      target030Seed113_checked hD hB hlocal

/-- The checked count and even anchor give a 0.30 semiprime witness on
this closed logarithmic interval. -/
theorem target030_semiprime113_cell1 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (5551 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 5683 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed113 hn ho hp hq hpq hprod hGRH 352 (by decide) (D :=
      (21597 / 1000 : ℝ))
  · change (21597 / 1000 : ℝ) ≤ Real.log (2395889156 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 2395889156 32 32 (21597 / 1000) 23 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (24 : ℚ)) (d := (241969 / 50000 : ℚ)) (j := 5)
        (lo := (5551 / 100 : ℝ)) (hi := (5683 / 100 : ℝ))
    · exact
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked count and even anchor give a 0.30 semiprime witness on
this closed logarithmic interval. -/
theorem target030_semiprime113_cell2 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (5683 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 5779 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed113 hn ho hp hq hpq hprod hGRH 358 (by decide) (D :=
      (21830 / 1000 : ℝ))
  · change (21830 / 1000 : ℝ) ≤ Real.log (3027065790 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 3027065790 32 32 (21830 / 1000) 23 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (24 : ℚ)) (d := (241969 / 50000 : ℚ)) (j := 5)
        (lo := (5683 / 100 : ℝ)) (hi := (5779 / 100 : ℝ))
    · exact
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked count and even anchor give a 0.30 semiprime witness on
this closed logarithmic interval. -/
theorem target030_semiprime113_cell3 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (5779 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 5832 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed113 hn ho hp hq hpq hprod hGRH 358 (by decide) (D :=
      (21830 / 1000 : ℝ))
  · change (21830 / 1000 : ℝ) ≤ Real.log (3027065790 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 3027065790 32 32 (21830 / 1000) 23 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (24 : ℚ)) (d := (241969 / 50000 : ℚ)) (j := 5)
        (lo := (5779 / 100 : ℝ)) (hi := (5832 / 100 : ℝ))
    · exact
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked count and even anchor give a 0.30 semiprime witness on
this closed logarithmic interval. -/
theorem target030_semiprime113_cell4 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (5832 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 5860 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed113 hn ho hp hq hpq hprod hGRH 358 (by decide) (D :=
      (21830 / 1000 : ℝ))
  · change (21830 / 1000 : ℝ) ≤ Real.log (3027065790 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 3027065790 32 32 (21830 / 1000) 23 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (24 : ℚ)) (d := (241969 / 50000 : ℚ)) (j := 5)
        (lo := (5832 / 100 : ℝ)) (hi := (5860 / 100 : ℝ))
    · exact
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked count and even anchor give a 0.30 semiprime witness on
this closed logarithmic interval. -/
theorem target030_semiprime113_cell5 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (5860 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 5915 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed113 hn ho hp hq hpq hprod hGRH 358 (by decide) (D :=
      (21830 / 1000 : ℝ))
  · change (21830 / 1000 : ℝ) ≤ Real.log (3027065790 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 3027065790 32 32 (21830 / 1000) 23 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (5860 / 100 : ℝ)) (hi := (5915 / 100 : ℝ))
    · exact
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked count and even anchor give a 0.30 semiprime witness on
this closed logarithmic interval. -/
theorem target030_semiprime113_cell6 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (5915 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 5945 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed113 hn ho hp hq hpq hprod hGRH 358 (by decide) (D :=
      (21830 / 1000 : ℝ))
  · change (21830 / 1000 : ℝ) ≤ Real.log (3027065790 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 3027065790 32 32 (21830 / 1000) 23 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (5915 / 100 : ℝ)) (hi := (5945 / 100 : ℝ))
    · exact
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- Under GRH, every distinct semiprime with logarithm in `[8, 59.45]`
has a 0.30 rejecting prime. Six anchored cells extend the earlier range. -/
theorem exists_prime_reject_03_semiprime_5945 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 5945 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h0 : Real.log n ≤ 5551 / 100
  · exact exists_prime_reject_03_semiprime_5551 hn ho hp hq hpq hprod hGRH hL h0
  · by_cases h1 : Real.log n ≤ 5683 / 100
    · exact target030_semiprime113_cell1 hn ho hp hq hpq hprod hGRH (le_of_not_ge h0) h1
    · by_cases h2 : Real.log n ≤ 5779 / 100
      · exact target030_semiprime113_cell2 hn ho hp hq hpq hprod hGRH (le_of_not_ge h1) h2
      · by_cases h3 : Real.log n ≤ 5832 / 100
        · exact target030_semiprime113_cell3 hn ho hp hq hpq hprod hGRH (le_of_not_ge h2) h3
        · by_cases h4 : Real.log n ≤ 5860 / 100
          · exact target030_semiprime113_cell4 hn ho hp hq hpq hprod hGRH (le_of_not_ge h3) h4
          · by_cases h5 : Real.log n ≤ 5915 / 100
            · exact target030_semiprime113_cell5 hn ho hp hq hpq hprod hGRH (le_of_not_ge h4) h5
            · exact target030_semiprime113_cell6 hn ho hp hq hpq hprod hGRH (le_of_not_ge h5) hU

end PseudoPrime.PrimeTestBounds.MillerRabin

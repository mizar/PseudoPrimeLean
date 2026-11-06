/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Seed281Count
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedSemiprimeLower
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Semiprime6878

/-! # Semiprime coverage through logarithmic scale 75.76 -/

@[expose] public section

set_option maxRecDepth 32768

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A checked weighted-count lower bound through 281 yields semiprime
witnesses when its logarithmic count and local envelope meet the target. -/
theorem exists_prime_reject_semiprime_seed281 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget : ℕ) (hN : budget ≤ 550)
    {D X : ℝ} (hD : D ≤ Real.log (target030Seed281Row14.getD budget 0 : ℝ)) (hB : (281 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_lower hn ho hp hq hpq hprod hGRH target030Seed281Primes
      target030Seed281Weights 281 budget target030Seed281Weight 10 (by norm_num only)
      target030Seed281_labels.1 (fun r hr ↦ (target030Seed281_prime_supply r hr).1)
      (fun r hr ↦ (target030Seed281_prime_supply r hr).2) target030Seed281_labels.2.2
      target030Seed281_weight_bounds target030Seed281_labels.2.1 target030Seed281Row14
      (target030Seed281_count_lower budget hN) hD hB hlocal

/-- The lower count and even anchor give a 0.30 semiprime witness on this
closed logarithmic interval. -/
theorem target030_semiprime281_cell1 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (6878 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 7069 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed281 hn ho hp hq hpq hprod hGRH 429 (by decide) (D :=
      (27789 / 1000 : ℝ))
  · change (27789 / 1000 : ℝ) ≤ Real.log (1171351818335 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 1171351818335 41 32 (27789 / 1000) 31 = true from
            by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (6878 / 100 : ℝ)) (hi := (7069 / 100 : ℝ))
    · exact
        List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The lower count and even anchor give a 0.30 semiprime witness on this
closed logarithmic interval. -/
theorem target030_semiprime281_cell2 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (7069 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 7216 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed281 hn ho hp hq hpq hprod hGRH 439 (by decide) (D :=
      (28221 / 1000 : ℝ))
  · change (28221 / 1000 : ℝ) ≤ Real.log (1804354289099 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 1804354289099 41 32 (28221 / 1000) 31 = true from
            by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (7069 / 100 : ℝ)) (hi := (7216 / 100 : ℝ))
    · exact
        List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The lower count and even anchor give a 0.30 semiprime witness on this
closed logarithmic interval. -/
theorem target030_semiprime281_cell3 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (7216 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 7332 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed281 hn ho hp hq hpq hprod hGRH 447 (by decide) (D :=
      (28570 / 1000 : ℝ))
  · change (28570 / 1000 : ℝ) ≤ Real.log (2559184634643 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 2559184634643 42 32 (28570 / 1000) 31 = true from
            by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (7216 / 100 : ℝ)) (hi := (7332 / 100 : ℝ))
    · exact
        List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The lower count and even anchor give a 0.30 semiprime witness on this
closed logarithmic interval. -/
theorem target030_semiprime281_cell4 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (7332 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 7419 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed281 hn ho hp hq hpq hprod hGRH 453 (by decide) (D :=
      (28809 / 1000 : ℝ))
  · change (28809 / 1000 : ℝ) ≤ Real.log (3247907303942 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 3247907303942 42 32 (28809 / 1000) 31 = true from
            by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (7332 / 100 : ℝ)) (hi := (7419 / 100 : ℝ))
    · exact
        List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The lower count and even anchor give a 0.30 semiprime witness on this
closed logarithmic interval. -/
theorem target030_semiprime281_cell5 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (7419 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 7485 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed281 hn ho hp hq hpq hprod hGRH 458 (by decide) (D :=
      (28993 / 1000 : ℝ))
  · change (28993 / 1000 : ℝ) ≤ Real.log (3904407956876 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 3904407956876 42 32 (28993 / 1000) 31 = true from
            by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (7419 / 100 : ℝ)) (hi := (7485 / 100 : ℝ))
    · exact
        List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The lower count and even anchor give a 0.30 semiprime witness on this
closed logarithmic interval. -/
theorem target030_semiprime281_cell6 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (7485 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 7537 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed281 hn ho hp hq hpq hprod hGRH 462 (by decide) (D :=
      (29145 / 1000 : ℝ))
  · change (29145 / 1000 : ℝ) ≤ Real.log (4544900249555 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 4544900249555 43 32 (29145 / 1000) 31 = true from
            by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (7485 / 100 : ℝ)) (hi := (7537 / 100 : ℝ))
    · exact
        List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The lower count and even anchor give a 0.30 semiprime witness on this
closed logarithmic interval. -/
theorem target030_semiprime281_cell7 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (7537 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 7576 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed281 hn ho hp hq hpq hprod hGRH 465 (by decide) (D :=
      (29258 / 1000 : ℝ))
  · change (29258 / 1000 : ℝ) ≤ Real.log (5088547860824 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 5088547860824 43 32 (29258 / 1000) 31 = true from
            by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (7537 / 100 : ℝ)) (hi := (7576 / 100 : ℝ))
    · exact
        List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- Under GRH, every distinct semiprime with logarithm in `[8, 75.76]`
has a 0.30 rejecting prime. Seven anchored cells extend the earlier range. -/
theorem exists_prime_reject_03_semiprime_7576 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 7576 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h0 : Real.log n ≤ 6878 / 100
  · exact exists_prime_reject_03_semiprime_6878 hn ho hp hq hpq hprod hGRH hL h0
  · by_cases h1 : Real.log n ≤ 7069 / 100
    · exact target030_semiprime281_cell1 hn ho hp hq hpq hprod hGRH (le_of_not_ge h0) h1
    · by_cases h2 : Real.log n ≤ 7216 / 100
      · exact target030_semiprime281_cell2 hn ho hp hq hpq hprod hGRH (le_of_not_ge h1) h2
      · by_cases h3 : Real.log n ≤ 7332 / 100
        · exact target030_semiprime281_cell3 hn ho hp hq hpq hprod hGRH (le_of_not_ge h2) h3
        · by_cases h4 : Real.log n ≤ 7419 / 100
          · exact target030_semiprime281_cell4 hn ho hp hq hpq hprod hGRH (le_of_not_ge h3) h4
          · by_cases h5 : Real.log n ≤ 7485 / 100
            · exact target030_semiprime281_cell5 hn ho hp hq hpq hprod hGRH (le_of_not_ge h4) h5
            · by_cases h6 : Real.log n ≤ 7537 / 100
              · exact target030_semiprime281_cell6 hn ho hp hq hpq hprod hGRH (le_of_not_ge h5) h6
              · exact target030_semiprime281_cell7 hn ho hp hq hpq hprod hGRH (le_of_not_ge h6) hU

end PseudoPrime.PrimeTestBounds.MillerRabin

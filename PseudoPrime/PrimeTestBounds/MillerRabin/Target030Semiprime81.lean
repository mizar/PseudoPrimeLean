/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Seed373Count
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedSemiprimeLower
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Semiprime7576

/-! # Semiprime coverage through logarithmic scale 81 -/

@[expose] public section

set_option maxRecDepth 32768

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A checked weighted-count lower bound through 373 yields semiprime
witnesses when its logarithmic count and local envelope meet the target. -/
theorem exists_prime_reject_semiprime_seed373 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget : ℕ) (hN : budget ≤ 500)
    {D X : ℝ} (hD : D ≤ Real.log (target030Seed373Row14.getD budget 0 : ℝ)) (hB : (373 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_lower hn ho hp hq hpq hprod hGRH target030Seed373Primes
      target030Seed373Weights 373 budget target030Seed373Weight 10 (by norm_num only)
      target030Seed373_labels.1 (fun r hr ↦ (target030Seed373_prime_supply r hr).1)
      (fun r hr ↦ (target030Seed373_prime_supply r hr).2) target030Seed373_labels.2.2
      target030Seed373_weight_bounds target030Seed373_labels.2.1 target030Seed373Row14
      (target030Seed373_count_lower budget hN) hD hB hlocal

/-- The lower count and even anchor give a 0.30 semiprime witness on this
closed logarithmic interval. -/
theorem target030_semiprime373_cell1 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (7576 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 7717 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed373 hn ho hp hq hpq hprod hGRH 467 (by decide) (D :=
      (30449 / 1000 : ℝ))
  · change (30449 / 1000 : ℝ) ≤ Real.log (16754032452099 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 16754032452099 44 32 (30449 / 1000) 33 = true from
            by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (7576 / 100 : ℝ)) (hi := (7717 / 100 : ℝ))
    · exact
        List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The lower count and even anchor give a 0.30 semiprime witness on this
closed logarithmic interval. -/
theorem target030_semiprime373_cell2 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (7717 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 7824 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed373 hn ho hp hq hpq hprod hGRH 474 (by decide) (D :=
      (30744 / 1000 : ℝ))
  · change (30744 / 1000 : ℝ) ≤ Real.log (22489175417409 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 22489175417409 45 32 (30744 / 1000) 33 = true from
            by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (7717 / 100 : ℝ)) (hi := (7824 / 100 : ℝ))
    · exact
        List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The lower count and even anchor give a 0.30 semiprime witness on this
closed logarithmic interval. -/
theorem target030_semiprime373_cell3 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (7824 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 7907 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed373 hn ho hp hq hpq hprod hGRH 480 (by decide) (D :=
      (30994 / 1000 : ℝ))
  · change (30994 / 1000 : ℝ) ≤ Real.log (28882247953414 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 28882247953414 45 32 (30994 / 1000) 33 = true from
            by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (7824 / 100 : ℝ)) (hi := (7907 / 100 : ℝ))
    · exact
        List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The lower count and even anchor give a 0.30 semiprime witness on this
closed logarithmic interval. -/
theorem target030_semiprime373_cell4 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (7907 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 7974 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed373 hn ho hp hq hpq hprod hGRH 485 (by decide) (D :=
      (31207 / 1000 : ℝ))
  · change (31207 / 1000 : ℝ) ≤ Real.log (35735411542090 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 35735411542090 46 32 (31207 / 1000) 33 = true from
            by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (7907 / 100 : ℝ)) (hi := (7974 / 100 : ℝ))
    · exact
        List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The lower count and even anchor give a 0.30 semiprime witness on this
closed logarithmic interval. -/
theorem target030_semiprime373_cell5 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (7974 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 8028 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed373 hn ho hp hq hpq hprod hGRH 489 (by decide) (D :=
      (31380 / 1000 : ℝ))
  · change (31380 / 1000 : ℝ) ≤ Real.log (42477750843568 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 42477750843568 46 32 (31380 / 1000) 33 = true from
            by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (7974 / 100 : ℝ)) (hi := (8028 / 100 : ℝ))
    · exact
        List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The lower count and even anchor give a 0.30 semiprime witness on this
closed logarithmic interval. -/
theorem target030_semiprime373_cell6 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (8028 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 8066 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed373 hn ho hp hq hpq hprod hGRH 491 (by decide) (D :=
      (31467 / 1000 : ℝ))
  · change (31467 / 1000 : ℝ) ≤ Real.log (46343069390465 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 46343069390465 46 32 (31467 / 1000) 33 = true from
            by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (8028 / 100 : ℝ)) (hi := (8066 / 100 : ℝ))
    · exact
        List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The lower count and even anchor give a 0.30 semiprime witness on this
closed logarithmic interval. -/
theorem target030_semiprime373_cell7 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (8066 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 8100 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed373 hn ho hp hq hpq hprod hGRH 494 (by decide) (D :=
      (31598 / 1000 : ℝ))
  · change (31598 / 1000 : ℝ) ≤ Real.log (52847055916016 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 52847055916016 46 32 (31598 / 1000) 33 = true from
            by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (8066 / 100 : ℝ)) (hi := (8100 / 100 : ℝ))
    · exact
        List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- Under GRH, every distinct semiprime with logarithm in `[8, 81]`
has a 0.30 rejecting prime. Seven anchored cells extend the earlier range. -/
theorem exists_prime_reject_03_semiprime_81 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 81) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h0 : Real.log n ≤ 7576 / 100
  · exact exists_prime_reject_03_semiprime_7576 hn ho hp hq hpq hprod hGRH hL h0
  · by_cases h1 : Real.log n ≤ 7717 / 100
    · exact target030_semiprime373_cell1 hn ho hp hq hpq hprod hGRH (le_of_not_ge h0) h1
    · by_cases h2 : Real.log n ≤ 7824 / 100
      · exact target030_semiprime373_cell2 hn ho hp hq hpq hprod hGRH (le_of_not_ge h1) h2
      · by_cases h3 : Real.log n ≤ 7907 / 100
        · exact target030_semiprime373_cell3 hn ho hp hq hpq hprod hGRH (le_of_not_ge h2) h3
        · by_cases h4 : Real.log n ≤ 7974 / 100
          · exact target030_semiprime373_cell4 hn ho hp hq hpq hprod hGRH (le_of_not_ge h3) h4
          · by_cases h5 : Real.log n ≤ 8028 / 100
            · exact target030_semiprime373_cell5 hn ho hp hq hpq hprod hGRH (le_of_not_ge h4) h5
            · by_cases h6 : Real.log n ≤ 8066 / 100
              · exact target030_semiprime373_cell6 hn ho hp hq hpq hprod hGRH (le_of_not_ge h5) h6
              · exact
                  target030_semiprime373_cell7 hn ho hp hq hpq hprod hGRH (le_of_not_ge h6)
                    (by linarith only [hU])

end PseudoPrime.PrimeTestBounds.MillerRabin

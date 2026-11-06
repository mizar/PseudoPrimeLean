/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Seed89Count358
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Semiprime4478

/-! # Semiprime coverage through logarithmic scale 55.51 -/

@[expose] public section

set_option maxRecDepth 32768

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The checked supply through 89 yields semiprime witnesses for budgets
through 358 whenever the count and local-envelope conditions hold. -/
theorem exists_prime_reject_semiprime_seed89_358 {n p q : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget : ℕ) (hN : budget ≤ 358)
    {D X : ℝ} (hD : D ≤ Real.log (target030Seed89Row358.getD budget 0 : ℝ)) (hB : (89 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_table hn ho hp hq hpq hprod hGRH target030Seed89Primes
      target030Seed89Weights 89 budget 358 target030Seed89Weight 10 (by norm_num only)
      target030Seed89_labels.1 (fun r hr ↦ (target030Seed89_prime_supply r hr).1)
      (fun r hr ↦ (target030Seed89_prime_supply r hr).2) target030Seed89_labels.2.2
      target030Seed89_weight_bounds target030Seed89_labels.2.1 hN target030Seed89Row358
      target030Seed89Tail358 target030Seed89_checked358 hD hB hlocal

/-- The checked count and even anchor give a 0.30 semiprime witness on
this closed logarithmic interval. -/
theorem target030_semiprime89_anchor2_cell1 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (4478 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 4771 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed89_358 hn ho hp hq hpq hprod hGRH 293 (by decide) (D :=
      (18346 / 1000 : ℝ))
  · change (18346 / 1000 : ℝ) ≤ Real.log (92890746 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 92890746 27 32 (18346 / 1000) 22 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (24 : ℚ)) (d := (241969 / 50000 : ℚ)) (j := 5)
        (lo := (4478 / 100 : ℝ)) (hi := (4771 / 100 : ℝ))
    · exact
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked count and even anchor give a 0.30 semiprime witness on
this closed logarithmic interval. -/
theorem target030_semiprime89_anchor2_cell2 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (4771 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 4994 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed89_358 hn ho hp hq hpq hprod hGRH 309 (by decide) (D :=
      (18971 / 1000 : ℝ))
  · change (18971 / 1000 : ℝ) ≤ Real.log (173462448 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 173462448 28 32 (18971 / 1000) 22 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (24 : ℚ)) (d := (241969 / 50000 : ℚ)) (j := 5)
        (lo := (4771 / 100 : ℝ)) (hi := (4994 / 100 : ℝ))
    · exact
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked count and even anchor give a 0.30 semiprime witness on
this closed logarithmic interval. -/
theorem target030_semiprime89_anchor2_cell3 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (4994 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 5161 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed89_358 hn ho hp hq hpq hprod hGRH 321 (by decide) (D :=
      (19427 / 1000 : ℝ))
  · change (19427 / 1000 : ℝ) ≤ Real.log (273797437 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 273797437 29 32 (19427 / 1000) 22 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (24 : ℚ)) (d := (241969 / 50000 : ℚ)) (j := 5)
        (lo := (4994 / 100 : ℝ)) (hi := (5161 / 100 : ℝ))
    · exact
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked count and even anchor give a 0.30 semiprime witness on
this closed logarithmic interval. -/
theorem target030_semiprime89_anchor2_cell4 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (5161 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 5290 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed89_358 hn ho hp hq hpq hprod hGRH 331 (by decide) (D :=
      (19800 / 1000 : ℝ))
  · change (19800 / 1000 : ℝ) ≤ Real.log (397536706 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 397536706 29 32 (19800 / 1000) 22 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (24 : ℚ)) (d := (241969 / 50000 : ℚ)) (j := 5)
        (lo := (5161 / 100 : ℝ)) (hi := (5290 / 100 : ℝ))
    · exact
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked count and even anchor give a 0.30 semiprime witness on
this closed logarithmic interval. -/
theorem target030_semiprime89_anchor2_cell5 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (5290 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 5386 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed89_358 hn ho hp hq hpq hprod hGRH 338 (by decide) (D :=
      (20057 / 1000 : ℝ))
  · change (20057 / 1000 : ℝ) ≤ Real.log (514108663 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 514108663 29 32 (20057 / 1000) 22 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (24 : ℚ)) (d := (241969 / 50000 : ℚ)) (j := 5)
        (lo := (5290 / 100 : ℝ)) (hi := (5386 / 100 : ℝ))
    · exact
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked count and even anchor give a 0.30 semiprime witness on
this closed logarithmic interval. -/
theorem target030_semiprime89_anchor2_cell6 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (5386 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 5457 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed89_358 hn ho hp hq hpq hprod hGRH 343 (by decide) (D :=
      (20239 / 1000 : ℝ))
  · change (20239 / 1000 : ℝ) ≤ Real.log (616594637 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 616594637 30 32 (20239 / 1000) 22 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (24 : ℚ)) (d := (241969 / 50000 : ℚ)) (j := 5)
        (lo := (5386 / 100 : ℝ)) (hi := (5457 / 100 : ℝ))
    · exact
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked count and even anchor give a 0.30 semiprime witness on
this closed logarithmic interval. -/
theorem target030_semiprime89_anchor2_cell7 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (5457 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 5511 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed89_358 hn ho hp hq hpq hprod hGRH 347 (by decide) (D :=
      (20384 / 1000 : ℝ))
  · change (20384 / 1000 : ℝ) ≤ Real.log (712313808 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 712313808 30 32 (20384 / 1000) 22 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (24 : ℚ)) (d := (241969 / 50000 : ℚ)) (j := 5)
        (lo := (5457 / 100 : ℝ)) (hi := (5511 / 100 : ℝ))
    · exact
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked count and even anchor give a 0.30 semiprime witness on
this closed logarithmic interval. -/
theorem target030_semiprime89_anchor2_cell8 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (5511 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 5551 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed89_358 hn ho hp hq hpq hprod hGRH 350 (by decide) (D :=
      (20491 / 1000 : ℝ))
  · change (20491 / 1000 : ℝ) ≤ Real.log (793226168 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 793226168 30 32 (20491 / 1000) 22 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (24 : ℚ)) (d := (241969 / 50000 : ℚ)) (j := 5)
        (lo := (5511 / 100 : ℝ)) (hi := (5551 / 100 : ℝ))
    · exact
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- Under GRH, every distinct semiprime with logarithm in `[8, 55.51]`
has a 0.30 rejecting prime. Eight anchored cells extend the earlier range. -/
theorem exists_prime_reject_03_semiprime_5551 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 5551 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h0 : Real.log n ≤ 4478 / 100
  · exact exists_prime_reject_03_semiprime_4478 hn ho hp hq hpq hprod hGRH hL h0
  · by_cases h1 : Real.log n ≤ 4771 / 100
    · exact target030_semiprime89_anchor2_cell1 hn ho hp hq hpq hprod hGRH (le_of_not_ge h0) h1
    · by_cases h2 : Real.log n ≤ 4994 / 100
      · exact target030_semiprime89_anchor2_cell2 hn ho hp hq hpq hprod hGRH (le_of_not_ge h1) h2
      · by_cases h3 : Real.log n ≤ 5161 / 100
        · exact target030_semiprime89_anchor2_cell3 hn ho hp hq hpq hprod hGRH (le_of_not_ge h2) h3
        · by_cases h4 : Real.log n ≤ 5290 / 100
          · exact
              target030_semiprime89_anchor2_cell4 hn ho hp hq hpq hprod hGRH (le_of_not_ge h3) h4
          · by_cases h5 : Real.log n ≤ 5386 / 100
            · exact
                target030_semiprime89_anchor2_cell5 hn ho hp hq hpq hprod hGRH (le_of_not_ge h4) h5
            · by_cases h6 : Real.log n ≤ 5457 / 100
              · exact
                  target030_semiprime89_anchor2_cell6 hn ho hp hq hpq hprod hGRH (le_of_not_ge h5)
                    h6
              · by_cases h7 : Real.log n ≤ 5511 / 100
                · exact
                    target030_semiprime89_anchor2_cell7 hn ho hp hq hpq hprod hGRH (le_of_not_ge h6)
                      h7
                · exact
                    target030_semiprime89_anchor2_cell8 hn ho hp hq hpq hprod hGRH (le_of_not_ge h7)
                      hU

end PseudoPrime.PrimeTestBounds.MillerRabin

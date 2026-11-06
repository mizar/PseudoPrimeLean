/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Seed1849
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Seed1849Count
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedSemiprimeCount
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Semiprime81

/-! # Semiprime coverage through logarithmic scale 100 -/

@[expose] public section

set_option maxRecDepth 32768

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The grouped count through 1849 gives a semiprime witness when its
logarithmic lower count and local envelope fit the requested bound. -/
theorem exists_prime_reject_semiprime_seed1849 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (A k : ℕ) (hA : A ≤ 500)
    {D X : ℝ}
    (hD : D ≤ Real.log ((Nat.choose (209 + k) k * target030Seed373Row14.getD A 0 : ℕ) : ℝ))
    (hB : (1849 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max (((A + k * 76 : ℕ) : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_count_lower hn ho hp hq hpq hprod hGRH target030Seed1849Primes
      target030Seed1849Weights 1849 (A + k * 76) target030Seed1849Weight 10 (by norm_num only)
      target030Seed1849_labels.1 (fun r hr ↦ (target030Seed1849_prime_supply r hr).1)
      (fun r hr ↦ (target030Seed1849_prime_supply r hr).2) target030Seed1849_labels.2.2
      target030Seed1849_weight_bounds target030Seed1849_labels.2.1
      (Nat.choose (209 + k) k * target030Seed373Row14.getD A 0)
      (target030Seed1849_group_lower A k hA) hD hB hlocal

/-- The grouped count and even anchor give a 0.30 semiprime witness on
this closed logarithmic interval. -/
theorem target030_semiprime1849_cell1 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (8100 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 8419 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed1849 hn ho hp hq hpq hprod hGRH 267 3 (by decide) (D :=
      (34603 / 1000 : ℝ))
  · change (34603 / 1000 : ℝ) ≤ Real.log (1066632964538960 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 1066632964538960 50 32 (34603 / 1000) 42 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (8100 / 100 : ℝ)) (hi := (8419 / 100 : ℝ))
    · exact
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The grouped count and even anchor give a 0.30 semiprime witness on
this closed logarithmic interval. -/
theorem target030_semiprime1849_cell2 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (8419 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 8696 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed1849 hn ho hp hq hpq hprod hGRH 285 3 (by decide) (D :=
      (35622 / 1000 : ℝ))
  · change (35622 / 1000 : ℝ) ≤ Real.log (2955258447187480 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 2955258447187480 52 32 (35622 / 1000) 42 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (8419 / 100 : ℝ)) (hi := (8696 / 100 : ℝ))
    · exact
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The grouped count and even anchor give a 0.30 semiprime witness on
this closed logarithmic interval. -/
theorem target030_semiprime1849_cell3 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (8696 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 8931 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed1849 hn ho hp hq hpq hprod hGRH 300 3 (by decide) (D :=
      (36453 / 1000 : ℝ))
  · change (36453 / 1000 : ℝ) ≤ Real.log (6785103294538240 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 6785103294538240 53 32 (36453 / 1000) 42 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (8696 / 100 : ℝ)) (hi := (8931 / 100 : ℝ))
    · exact
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The grouped count and even anchor give a 0.30 semiprime witness on
this closed logarithmic interval. -/
theorem target030_semiprime1849_cell4 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (8931 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 9219 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed1849 hn ho hp hq hpq hprod hGRH 319 3 (by decide) (D :=
      (37484 / 1000 : ℝ))
  · change (37484 / 1000 : ℝ) ≤ Real.log (19017637395267560 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 19017637395267560 55 32 (37484 / 1000) 42 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (48 : ℚ)) (d := (579107 / 100000 : ℚ)) (j := 6)
        (lo := (8931 / 100 : ℝ)) (hi := (9219 / 100 : ℝ))
    · exact
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The grouped count and even anchor give a 0.30 semiprime witness on
this closed logarithmic interval. -/
theorem target030_semiprime1849_cell5 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (9219 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 9456 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed1849 hn ho hp hq hpq hprod hGRH 334 3 (by decide) (D :=
      (38281 / 1000 : ℝ))
  · change (38281 / 1000 : ℝ) ≤ Real.log (42195838872346460 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 42195838872346460 56 32 (38281 / 1000) 42 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (48 : ℚ)) (d := (579107 / 100000 : ℚ)) (j := 6)
        (lo := (9219 / 100 : ℝ)) (hi := (9456 / 100 : ℝ))
    · exact
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The grouped count and even anchor give a 0.30 semiprime witness on
this closed logarithmic interval. -/
theorem target030_semiprime1849_cell6 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (9456 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 9654 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed1849 hn ho hp hq hpq hprod hGRH 347 3 (by decide) (D :=
      (38960 / 1000 : ℝ))
  · change (38960 / 1000 : ℝ) ≤ Real.log (83249435296194020 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 83249435296194020 57 32 (38960 / 1000) 42 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (48 : ℚ)) (d := (579107 / 100000 : ℚ)) (j := 6)
        (lo := (9456 / 100 : ℝ)) (hi := (9654 / 100 : ℝ))
    · exact
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The grouped count and even anchor give a 0.30 semiprime witness on
this closed logarithmic interval. -/
theorem target030_semiprime1849_cell7 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (9654 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 9819 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed1849 hn ho hp hq hpq hprod hGRH 358 3 (by decide) (D :=
      (39527 / 1000 : ℝ))
  · change (39527 / 1000 : ℝ) ≤ Real.log (146802818092119420 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 146802818092119420 58 32 (39527 / 1000) 42 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (48 : ℚ)) (d := (579107 / 100000 : ℚ)) (j := 6)
        (lo := (9654 / 100 : ℝ)) (hi := (9819 / 100 : ℝ))
    · exact
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The grouped count and even anchor give a 0.30 semiprime witness on
this closed logarithmic interval. -/
theorem target030_semiprime1849_cell8 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (9819 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 9954 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed1849 hn ho hp hq hpq hprod hGRH 367 3 (by decide) (D :=
      (39978 / 1000 : ℝ))
  · change (39978 / 1000 : ℝ) ≤ Real.log (230347218251972500 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 230347218251972500 58 32 (39978 / 1000) 42 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (48 : ℚ)) (d := (579107 / 100000 : ℚ)) (j := 6)
        (lo := (9819 / 100 : ℝ)) (hi := (9954 / 100 : ℝ))
    · exact
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The grouped count and even anchor give a 0.30 semiprime witness on
this closed logarithmic interval. -/
theorem target030_semiprime1849_cell9 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (9954 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 10000 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed1849 hn ho hp hq hpq hprod hGRH 375 3 (by decide) (D :=
      (40378 / 1000 : ℝ))
  · change (40378 / 1000 : ℝ) ≤ Real.log (343683350416550200 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 343683350416550200 59 32 (40378 / 1000) 42 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (48 : ℚ)) (d := (579107 / 100000 : ℚ)) (j := 6)
        (lo := (9954 / 100 : ℝ)) (hi := (10000 / 100 : ℝ))
    · exact
        (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- Under GRH, every distinct semiprime with logarithm in `[8, 100]`
has a 0.30 rejecting prime. Nine grouped-count cells extend the earlier range. -/
theorem exists_prime_reject_03_semiprime_100 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h0 : Real.log n ≤ 81
  · exact exists_prime_reject_03_semiprime_81 hn ho hp hq hpq hprod hGRH hL h0
  · by_cases h1 : Real.log n ≤ 8419 / 100
    · exact target030_semiprime1849_cell1 hn ho hp hq hpq hprod hGRH (by linarith only [h0]) h1
    · by_cases h2 : Real.log n ≤ 8696 / 100
      · exact target030_semiprime1849_cell2 hn ho hp hq hpq hprod hGRH (le_of_not_ge h1) h2
      · by_cases h3 : Real.log n ≤ 8931 / 100
        · exact target030_semiprime1849_cell3 hn ho hp hq hpq hprod hGRH (le_of_not_ge h2) h3
        · by_cases h4 : Real.log n ≤ 9219 / 100
          · exact target030_semiprime1849_cell4 hn ho hp hq hpq hprod hGRH (le_of_not_ge h3) h4
          · by_cases h5 : Real.log n ≤ 9456 / 100
            · exact target030_semiprime1849_cell5 hn ho hp hq hpq hprod hGRH (le_of_not_ge h4) h5
            · by_cases h6 : Real.log n ≤ 9654 / 100
              · exact target030_semiprime1849_cell6 hn ho hp hq hpq hprod hGRH (le_of_not_ge h5) h6
              · by_cases h7 : Real.log n ≤ 9819 / 100
                · exact
                    target030_semiprime1849_cell7 hn ho hp hq hpq hprod hGRH (le_of_not_ge h6) h7
                · by_cases h8 : Real.log n ≤ 9954 / 100
                  · exact
                      target030_semiprime1849_cell8 hn ho hp hq hpq hprod hGRH (le_of_not_ge h7) h8
                  · exact
                      target030_semiprime1849_cell9 hn ho hp hq hpq hprod hGRH (le_of_not_ge h8)
                        (by linarith only [hU])

end PseudoPrime.PrimeTestBounds.MillerRabin

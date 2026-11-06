/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Seed199Count
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedSemiprimeLower
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Semiprime5945

/-! # Semiprime coverage through logarithmic scale 68.78 -/

@[expose] public section

set_option maxRecDepth 32768

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A checked weighted-count lower bound through 199 yields semiprime
witnesses when its logarithmic count and local envelope meet the target. -/
theorem exists_prime_reject_semiprime_seed199 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget : ℕ) (hN : budget ≤ 450)
    {D X : ℝ} (hD : D ≤ Real.log (target030Seed199Row16.getD budget 0 : ℝ)) (hB : (199 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_lower hn ho hp hq hpq hprod hGRH target030Seed199Primes
      target030Seed199Weights 199 budget target030Seed199Weight 10 (by norm_num only)
      target030Seed199_labels.1 (fun r hr ↦ (target030Seed199_prime_supply r hr).1)
      (fun r hr ↦ (target030Seed199_prime_supply r hr).2) target030Seed199_labels.2.2
      target030Seed199_weight_bounds target030Seed199_labels.2.1 target030Seed199Row16
      (target030Seed199_count_lower budget hN) hD hB hlocal

/-- The lower count and even anchor give a 0.30 semiprime witness on this
closed logarithmic interval. -/
theorem target030_semiprime199_cell1 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (5945 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 6216 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed199 hn ho hp hq hpq hprod hGRH 377 (by decide) (D :=
      (24377 / 1000 : ℝ))
  · change (24377 / 1000 : ℝ) ≤ Real.log (38640227796 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 38640227796 36 32 (24377 / 1000) 28 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (5945 / 100 : ℝ)) (hi := (6216 / 100 : ℝ))
    · exact
        List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The lower count and even anchor give a 0.30 semiprime witness on this
closed logarithmic interval. -/
theorem target030_semiprime199_cell2 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (6216 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 6428 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed199 hn ho hp hq hpq hprod hGRH 392 (by decide) (D :=
      (25007 / 1000 : ℝ))
  · change (25007 / 1000 : ℝ) ≤ Real.log (72575549824 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 72575549824 37 32 (25007 / 1000) 28 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (6216 / 100 : ℝ)) (hi := (6428 / 100 : ℝ))
    · exact
        List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The lower count and even anchor give a 0.30 semiprime witness on this
closed logarithmic interval. -/
theorem target030_semiprime199_cell3 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (6428 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 6595 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed199 hn ho hp hq hpq hprod hGRH 404 (by decide) (D :=
      (25516 / 1000 : ℝ))
  · change (25516 / 1000 : ℝ) ≤ Real.log (120675405438 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 120675405438 37 32 (25516 / 1000) 28 = true from
            by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (6428 / 100 : ℝ)) (hi := (6595 / 100 : ℝ))
    · exact
        List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The lower count and even anchor give a 0.30 semiprime witness on this
closed logarithmic interval. -/
theorem target030_semiprime199_cell4 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (6595 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 6720 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed199 hn ho hp hq hpq hprod hGRH 413 (by decide) (D :=
      (25854 / 1000 : ℝ))
  · change (25854 / 1000 : ℝ) ≤ Real.log (169223101277 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 169223101277 38 32 (25854 / 1000) 28 = true from
            by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (6595 / 100 : ℝ)) (hi := (6720 / 100 : ℝ))
    · exact
        List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The lower count and even anchor give a 0.30 semiprime witness on this
closed logarithmic interval. -/
theorem target030_semiprime199_cell5 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (6720 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 6811 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed199 hn ho hp hq hpq hprod hGRH 420 (by decide) (D :=
      (26082 / 1000 : ℝ))
  · change (26082 / 1000 : ℝ) ≤ Real.log (212581300873 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 212581300873 38 32 (26082 / 1000) 28 = true from
            by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (6720 / 100 : ℝ)) (hi := (6811 / 100 : ℝ))
    · exact
        List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The lower count and even anchor give a 0.30 semiprime witness on this
closed logarithmic interval. -/
theorem target030_semiprime199_cell6 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (6811 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 6878 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed199 hn ho hp hq hpq hprod hGRH 425 (by decide) (D :=
      (26255 / 1000 : ℝ))
  · change (26255 / 1000 : ℝ) ≤ Real.log (252617840055 : ℝ)
    have hl :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 252617840055 38 32 (26255 / 1000) 28 = true from
            by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    norm_num only at ⊢
    exact hl
  · nlinarith only [hL]
  · apply
      target030_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (6811 / 100 : ℝ)) (hi := (6878 / 100 : ℝ))
    · exact
        List.mem_cons_of_mem _
          (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- Under GRH, every distinct semiprime with logarithm in `[8, 68.78]`
has a 0.30 rejecting prime. Six anchored cells extend the earlier range. -/
theorem exists_prime_reject_03_semiprime_6878 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 6878 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h0 : Real.log n ≤ 5945 / 100
  · exact exists_prime_reject_03_semiprime_5945 hn ho hp hq hpq hprod hGRH hL h0
  · by_cases h1 : Real.log n ≤ 6216 / 100
    · exact target030_semiprime199_cell1 hn ho hp hq hpq hprod hGRH (le_of_not_ge h0) h1
    · by_cases h2 : Real.log n ≤ 6428 / 100
      · exact target030_semiprime199_cell2 hn ho hp hq hpq hprod hGRH (le_of_not_ge h1) h2
      · by_cases h3 : Real.log n ≤ 6595 / 100
        · exact target030_semiprime199_cell3 hn ho hp hq hpq hprod hGRH (le_of_not_ge h2) h3
        · by_cases h4 : Real.log n ≤ 6720 / 100
          · exact target030_semiprime199_cell4 hn ho hp hq hpq hprod hGRH (le_of_not_ge h3) h4
          · by_cases h5 : Real.log n ≤ 6811 / 100
            · exact target030_semiprime199_cell5 hn ho hp hq hpq hprod hGRH (le_of_not_ge h4) h5
            · exact target030_semiprime199_cell6 hn ho hp hq hpq hprod hGRH (le_of_not_ge h5) hU

end PseudoPrime.PrimeTestBounds.MillerRabin

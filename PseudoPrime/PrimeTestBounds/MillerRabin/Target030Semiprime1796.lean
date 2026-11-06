/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Seed61
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedSemiprimeTable
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Semiprime148

/-! # Semiprime coverage through logarithmic scale 17.96 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, the checked prime supply through 61 yields a semiprime witness
at every budget through 96 when the count and local-envelope conditions hold. -/
theorem exists_prime_reject_semiprime_seed61 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget : ℕ) (hN : budget ≤ 96)
    {D X : ℝ} (hD : D ≤ Real.log (target030Seed61Row.getD budget 0 : ℝ)) (hB : (61 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_table hn ho hp hq hpq hprod hGRH target030Seed61Primes
      target030Seed61Weights 61 budget 96 target030Seed61Weight 10 (by norm_num only)
      target030Seed61_labels.1 (fun r hr ↦ (target030Seed61_prime_supply r hr).1)
      (fun r hr ↦ (target030Seed61_prime_supply r hr).2) target030Seed61_labels.2.2
      target030Seed61_weight_bounds target030Seed61_labels.2.1 hN target030Seed61Row
      target030Seed61Tail target030Seed61_checked hD hB hlocal

/-- Under GRH, the weighted supply through 61 gives a 0.30 semiprime
witness on `[14.8, 15.78]` using the certified count and local envelope. -/
theorem target030_semiprime61_cell1 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (1480 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 1578 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed61 hn ho hp hq hpq hprod hGRH 81 (by decide) (D :=
      (7141 / 1000 : ℝ))
  · change (7141 / 1000 : ℝ) ≤ Real.log (1263 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 1263 11 32 (7141 / 1000) 9 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only at ⊢
    exact h
  · nlinarith only [hL]
  · apply
      target030_semiprime_envelope (lo := (1480 / 100 : ℝ)) (hi := (1578 / 100 : ℝ))
        (by norm_num only) hL hU
    all_goals norm_num only

/-- Under GRH, the weighted supply through 61 gives a 0.30 semiprime
witness on `[15.78, 16.52]` using the certified count and local envelope. -/
theorem target030_semiprime61_cell2 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (1578 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 1652 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed61 hn ho hp hq hpq hprod hGRH 86 (by decide) (D :=
      (7475 / 1000 : ℝ))
  · change (7475 / 1000 : ℝ) ≤ Real.log (1765 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 1765 11 32 (7475 / 1000) 9 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only at ⊢
    exact h
  · nlinarith only [hL]
  · apply
      target030_semiprime_envelope (lo := (1578 / 100 : ℝ)) (hi := (1652 / 100 : ℝ))
        (by norm_num only) hL hU
    all_goals norm_num only

/-- Under GRH, the weighted supply through 61 gives a 0.30 semiprime
witness on `[16.52, 17.11]` using the certified count and local envelope. -/
theorem target030_semiprime61_cell3 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (1652 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 1711 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed61 hn ho hp hq hpq hprod hGRH 90 (by decide) (D :=
      (7742 / 1000 : ℝ))
  · change (7742 / 1000 : ℝ) ≤ Real.log (2304 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 2304 12 32 (7742 / 1000) 9 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only at ⊢
    exact h
  · nlinarith only [hL]
  · apply
      target030_semiprime_envelope (lo := (1652 / 100 : ℝ)) (hi := (1711 / 100 : ℝ))
        (by norm_num only) hL hU
    all_goals norm_num only

/-- Under GRH, the weighted supply through 61 gives a 0.30 semiprime
witness on `[17.11, 17.53]` using the certified count and local envelope. -/
theorem target030_semiprime61_cell4 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (1711 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 1753 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed61 hn ho hp hq hpq hprod hGRH 93 (by decide) (D :=
      (7933 / 1000 : ℝ))
  · change (7933 / 1000 : ℝ) ≤ Real.log (2790 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 2790 12 32 (7933 / 1000) 9 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only at ⊢
    exact h
  · nlinarith only [hL]
  · apply
      target030_semiprime_envelope (lo := (1711 / 100 : ℝ)) (hi := (1753 / 100 : ℝ))
        (by norm_num only) hL hU
    all_goals norm_num only

/-- Under GRH, the weighted supply through 61 gives a 0.30 semiprime
witness on `[17.53, 17.96]` using the certified count and local envelope. -/
theorem target030_semiprime61_cell5 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (1753 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 1796 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed61 hn ho hp hq hpq hprod hGRH 96 (by decide) (D :=
      (8124 / 1000 : ℝ))
  · change (8124 / 1000 : ℝ) ≤ Real.log (3376 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 3376 12 32 (8124 / 1000) 9 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only at ⊢
    exact h
  · nlinarith only [hL]
  · apply
      target030_semiprime_envelope (lo := (1753 / 100 : ℝ)) (hi := (1796 / 100 : ℝ))
        (by norm_num only) hL hU
    all_goals norm_num only

/-- Under GRH, every distinct odd semiprime with logarithm in `[8, 17.96]`
has a 0.30 rejecting prime. Five weighted-count intervals extend the earlier
coverage through 14.8. -/
theorem exists_prime_reject_03_semiprime_1796 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 449 / 25) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h1 : Real.log n ≤ 74 / 5
  · exact exists_prime_reject_03_semiprime_148 hn ho hp hq hpq hprod hGRH hL h1
  · by_cases h2 : Real.log n ≤ 1578 / 100
    · exact target030_semiprime61_cell1 hn ho hp hq hpq hprod hGRH (by linarith only [h1]) h2
    · by_cases h3 : Real.log n ≤ 1652 / 100
      · exact target030_semiprime61_cell2 hn ho hp hq hpq hprod hGRH (le_of_not_ge h2) h3
      · by_cases h4 : Real.log n ≤ 1711 / 100
        · exact target030_semiprime61_cell3 hn ho hp hq hpq hprod hGRH (le_of_not_ge h3) h4
        · by_cases h5 : Real.log n ≤ 1753 / 100
          · exact target030_semiprime61_cell4 hn ho hp hq hpq hprod hGRH (le_of_not_ge h4) h5
          · exact
              target030_semiprime61_cell5 hn ho hp hq hpq hprod hGRH (le_of_not_ge h5)
                (by linarith only [hU])

end PseudoPrime.PrimeTestBounds.MillerRabin

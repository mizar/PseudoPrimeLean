/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Seed1409
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028EvenEnvelope

/-! # Grouped-count semiprime intervals -/

@[expose] public section

-- Reduction accesses the certified 501-entry base count row.
set_option maxRecDepth 65536

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The checked grouped count gives a semiprime witness on
`[71609/1000, 75578/1000]` at coefficient 0.28. -/
theorem target028_group_cell0 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (71609 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 75578 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed1409 hn ho hp hq hpq hprod hGRH 279 2 (by decide) (D :=
      (30356 / 1000 : ℝ))
  · change (30356 / 1000 : ℝ) ≤ Real.log (15261977586750 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 15261977586750 44 32 (30356 / 1000) 32 = true from
            by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (71609 / 1000 : ℝ)) (hi := (75578 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked grouped count gives a semiprime witness on
`[75578/1000, 78059/1000]` at coefficient 0.28. -/
theorem target028_group_cell1 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (75578 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 78059 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed1409 hn ho hp hq hpq hprod hGRH 300 2 (by decide) (D :=
      (31524 / 1000 : ℝ))
  · change (31524 / 1000 : ℝ) ≤ Real.log (49080424886400 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 49080424886400 46 32 (31524 / 1000) 33 = true from
            by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (75578 / 1000 : ℝ)) (hi := (78059 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked grouped count gives a semiprime witness on
`[78059/1000, 79563/1000]` at coefficient 0.28. -/
theorem target028_group_cell2 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (78059 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 79563 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed1409 hn ho hp hq hpq hprod hGRH 313 2 (by decide) (D :=
      (32232 / 1000 : ℝ))
  · change (32232 / 1000 : ℝ) ≤ Real.log (99608872766550 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 99608872766550 47 32 (32232 / 1000) 34 = true from
            by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (78059 / 1000 : ℝ)) (hi := (79563 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked grouped count gives a semiprime witness on
`[79563/1000, 80476/1000]` at coefficient 0.28. -/
theorem target028_group_cell3 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (79563 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 80476 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed1409 hn ho hp hq hpq hprod hGRH 321 2 (by decide) (D :=
      (32662 / 1000 : ℝ))
  · change (32662 / 1000 : ℝ) ≤ Real.log (153114733112550 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 153114733112550 48 32 (32662 / 1000) 34 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (79563 / 1000 : ℝ)) (hi := (80476 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked grouped count gives a semiprime witness on
`[80476/1000, 81041/1000]` at coefficient 0.28. -/
theorem target028_group_cell4 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (80476 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 81041 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed1409 hn ho hp hq hpq hprod hGRH 326 2 (by decide) (D :=
      (32928 / 1000 : ℝ))
  · change (32928 / 1000 : ℝ) ≤ Real.log (199893058488075 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 199893058488075 48 32 (32928 / 1000) 34 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (80476 / 1000 : ℝ)) (hi := (81041 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked grouped count gives a semiprime witness on
`[81041/1000, 81379/1000]` at coefficient 0.28. -/
theorem target028_group_cell5 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (81041 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 81379 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed1409 hn ho hp hq hpq hprod hGRH 329 2 (by decide) (D :=
      (33087 / 1000 : ℝ))
  · change (33087 / 1000 : ℝ) ≤ Real.log (234387631481325 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 234387631481325 48 32 (33087 / 1000) 35 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (81041 / 1000 : ℝ)) (hi := (81379 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked grouped count gives a semiprime witness on
`[81379/1000, 83001/1000]` at coefficient 0.28. -/
theorem target028_group_cell6 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (81379 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 83001 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed1849 hn ho hp hq hpq hprod hGRH 254 3 (by decide) (D :=
      (33851 / 1000 : ℝ))
  · change (33851 / 1000 : ℝ) ≤ Real.log (502786594801680 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 502786594801680 49 32 (33851 / 1000) 35 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (81379 / 1000 : ℝ)) (hi := (83001 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked grouped count gives a semiprime witness on
`[83001/1000, 84110/1000]` at coefficient 0.28. -/
theorem target028_group_cell7 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (83001 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 84110 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed1849 hn ho hp hq hpq hprod hGRH 263 3 (by decide) (D :=
      (34373 / 1000 : ℝ))
  · change (34373 / 1000 : ℝ) ≤ Real.log (847537332157180 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 847537332157180 50 32 (34373 / 1000) 36 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (83001 / 1000 : ℝ)) (hi := (84110 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked grouped count gives a semiprime witness on
`[84110/1000, 84840/1000]` at coefficient 0.28. -/
theorem target028_group_cell8 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (84110 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 84840 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed1849 hn ho hp hq hpq hprod hGRH 269 3 (by decide) (D :=
      (34717 / 1000 : ℝ))
  · change (34717 / 1000 : ℝ) ≤ Real.log (1196001009361200 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 1196001009361200 51 32 (34717 / 1000) 36 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (84110 / 1000 : ℝ)) (hi := (84840 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked grouped count gives a semiprime witness on
`[84840/1000, 85325/1000]` at coefficient 0.28. -/
theorem target028_group_cell9 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (84840 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 85325 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed1849 hn ho hp hq hpq hprod hGRH 273 3 (by decide) (D :=
      (34945 / 1000 : ℝ))
  · change (34945 / 1000 : ℝ) ≤ Real.log (1502270991156600 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 1502270991156600 51 32 (34945 / 1000) 36 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (84840 / 1000 : ℝ)) (hi := (85325 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked grouped count gives a semiprime witness on
`[85325/1000, 85567/1000]` at coefficient 0.28. -/
theorem target028_group_cell10 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (85325 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 85567 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed1849 hn ho hp hq hpq hprod hGRH 275 3 (by decide) (D :=
      (35059 / 1000 : ℝ))
  · change (35059 / 1000 : ℝ) ≤ Real.log (1682874990050520 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 1682874990050520 51 32 (35059 / 1000) 37 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (85325 / 1000 : ℝ)) (hi := (85567 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked grouped count gives a semiprime witness on
`[85567/1000, 85807/1000]` at coefficient 0.28. -/
theorem target028_group_cell11 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (85567 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 85807 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed1849 hn ho hp hq hpq hprod hGRH 277 3 (by decide) (D :=
      (35172 / 1000 : ℝ))
  · change (35172 / 1000 : ℝ) ≤ Real.log (1884611054487840 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 1884611054487840 51 32 (35172 / 1000) 37 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (85567 / 1000 : ℝ)) (hi := (85807 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked grouped count gives a semiprime witness on
`[85807/1000, 85926/1000]` at coefficient 0.28. -/
theorem target028_group_cell12 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (85807 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 85926 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed1849 hn ho hp hq hpq hprod hGRH 278 3 (by decide) (D :=
      (35228 / 1000 : ℝ))
  · change (35228 / 1000 : ℝ) ≤ Real.log (1994145530813520 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 1994145530813520 51 32 (35228 / 1000) 37 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (85807 / 1000 : ℝ)) (hi := (85926 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The grouped cells cover all distinct semiprimes from logarithmic scale
71.609 through 85.926 under GRH. -/
theorem target028_semiprime_71609_85926 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (71609 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 85926 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h0 : Real.log n ≤ 75578 / 1000
  · exact target028_group_cell0 hn ho hp hq hpq hprod hGRH hL h0
  by_cases h1 : Real.log n ≤ 78059 / 1000
  · exact target028_group_cell1 hn ho hp hq hpq hprod hGRH (le_of_not_ge h0) h1
  by_cases h2 : Real.log n ≤ 79563 / 1000
  · exact target028_group_cell2 hn ho hp hq hpq hprod hGRH (le_of_not_ge h1) h2
  by_cases h3 : Real.log n ≤ 80476 / 1000
  · exact target028_group_cell3 hn ho hp hq hpq hprod hGRH (le_of_not_ge h2) h3
  by_cases h4 : Real.log n ≤ 81041 / 1000
  · exact target028_group_cell4 hn ho hp hq hpq hprod hGRH (le_of_not_ge h3) h4
  by_cases h5 : Real.log n ≤ 81379 / 1000
  · exact target028_group_cell5 hn ho hp hq hpq hprod hGRH (le_of_not_ge h4) h5
  by_cases h6 : Real.log n ≤ 83001 / 1000
  · exact target028_group_cell6 hn ho hp hq hpq hprod hGRH (le_of_not_ge h5) h6
  by_cases h7 : Real.log n ≤ 84110 / 1000
  · exact target028_group_cell7 hn ho hp hq hpq hprod hGRH (le_of_not_ge h6) h7
  by_cases h8 : Real.log n ≤ 84840 / 1000
  · exact target028_group_cell8 hn ho hp hq hpq hprod hGRH (le_of_not_ge h7) h8
  by_cases h9 : Real.log n ≤ 85325 / 1000
  · exact target028_group_cell9 hn ho hp hq hpq hprod hGRH (le_of_not_ge h8) h9
  by_cases h10 : Real.log n ≤ 85567 / 1000
  · exact target028_group_cell10 hn ho hp hq hpq hprod hGRH (le_of_not_ge h9) h10
  by_cases h11 : Real.log n ≤ 85807 / 1000
  · exact target028_group_cell11 hn ho hp hq hpq hprod hGRH (le_of_not_ge h10) h11
  exact target028_group_cell12 hn ho hp hq hpq hprod hGRH (le_of_not_ge h11) hU

end PseudoPrime.PrimeTestBounds.MillerRabin

/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Group518
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Group526
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Group531
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Group540
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Group551
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Group558
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Group562
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Group565
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Group567
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Group568
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Group569
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GroupWitness
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028EvenEnvelope

/-! # Further semiprime intervals from summed grouped counts -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The checked summed count gives a semiprime witness on
`[88181/1000, 89591/1000]` at coefficient 0.28. -/
theorem target028_sum_cell0 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (88181 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 89591 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_group hn ho hp hq hpq hprod hGRH 518 11199153120272822
      target028_group518_count (D := (36954 / 1000 : ℝ))
  · have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 11199153120272822 54 32 (36954 / 1000) 38 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (88181 / 1000 : ℝ)) (hi := (89591 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked summed count gives a semiprime witness on
`[89591/1000, 90530/1000]` at coefficient 0.28. -/
theorem target028_sum_cell1 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (89591 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 90530 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_group hn ho hp hq hpq hprod hGRH 526 17429940986795261
      target028_group526_count (D := (37396 / 1000 : ℝ))
  · have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 17429940986795261 54 32 (37396 / 1000) 39 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (89591 / 1000 : ℝ)) (hi := (90530 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked summed count gives a semiprime witness on
`[90530/1000, 91114/1000]` at coefficient 0.28. -/
theorem target028_sum_cell2 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (90530 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 91114 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_group hn ho hp hq hpq hprod hGRH 531 22945080585764228
      target028_group531_count (D := (37671 / 1000 : ℝ))
  · have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 22945080585764228 55 32 (37671 / 1000) 39 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (90530 / 1000 : ℝ)) (hi := (91114 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked summed count gives a semiprime witness on
`[91114/1000, 93356/1000]` at coefficient 0.28. -/
theorem target028_sum_cell3 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (91114 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 93356 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_group hn ho hp hq hpq hprod hGRH 540 37643740262939801
      target028_group540_count (D := (38166 / 1000 : ℝ))
  · have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 37643740262939801 56 32 (38166 / 1000) 40 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (48 : ℚ)) (d := (579107 / 100000 : ℚ)) (j := 6)
        (lo := (91114 / 1000 : ℝ)) (hi := (93356 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked summed count gives a semiprime witness on
`[93356/1000, 94635/1000]` at coefficient 0.28. -/
theorem target028_sum_cell4 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (93356 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 94635 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_group hn ho hp hq hpq hprod hGRH 551 68690955093042921
      target028_group551_count (D := (38768 / 1000 : ℝ))
  · have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 68690955093042921 56 32 (38768 / 1000) 40 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (48 : ℚ)) (d := (579107 / 100000 : ℚ)) (j := 6)
        (lo := (93356 / 1000 : ℝ)) (hi := (94635 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked summed count gives a semiprime witness on
`[94635/1000, 95444/1000]` at coefficient 0.28. -/
theorem target028_sum_cell5 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (94635 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 95444 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_group hn ho hp hq hpq hprod hGRH 558 100583183838083486
      target028_group558_count (D := (39149 / 1000 : ℝ))
  · have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 100583183838083486 57 32 (39149 / 1000) 41 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (48 : ℚ)) (d := (579107 / 100000 : ℚ)) (j := 6)
        (lo := (94635 / 1000 : ℝ)) (hi := (95444 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked summed count gives a semiprime witness on
`[95444/1000, 95907/1000]` at coefficient 0.28. -/
theorem target028_sum_cell6 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (95444 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 95907 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_group hn ho hp hq hpq hprod hGRH 562 125005480271333608
      target028_group562_count (D := (39367 / 1000 : ℝ))
  · have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 125005480271333608 57 32 (39367 / 1000) 41 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (48 : ℚ)) (d := (579107 / 100000 : ℚ)) (j := 6)
        (lo := (95444 / 1000 : ℝ)) (hi := (95907 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked summed count gives a semiprime witness on
`[95907/1000, 96251/1000]` at coefficient 0.28. -/
theorem target028_sum_cell7 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (95907 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 96251 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_group hn ho hp hq hpq hprod hGRH 565 147036403418229909
      target028_group565_count (D := (39529 / 1000 : ℝ))
  · have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 147036403418229909 58 32 (39529 / 1000) 41 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (48 : ℚ)) (d := (579107 / 100000 : ℚ)) (j := 6)
        (lo := (95907 / 1000 : ℝ)) (hi := (96251 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked summed count gives a semiprime witness on
`[96251/1000, 96480/1000]` at coefficient 0.28. -/
theorem target028_sum_cell8 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (96251 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 96480 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_group hn ho hp hq hpq hprod hGRH 567 163795039191054404
      target028_group567_count (D := (39637 / 1000 : ℝ))
  · have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 163795039191054404 58 32 (39637 / 1000) 41 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (48 : ℚ)) (d := (579107 / 100000 : ℚ)) (j := 6)
        (lo := (96251 / 1000 : ℝ)) (hi := (96480 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked summed count gives a semiprime witness on
`[96480/1000, 96595/1000]` at coefficient 0.28. -/
theorem target028_sum_cell9 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (96480 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 96595 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_group hn ho hp hq hpq hprod hGRH 568 172846466401364471
      target028_group568_count (D := (39691 / 1000 : ℝ))
  · have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 172846466401364471 58 32 (39691 / 1000) 41 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (48 : ℚ)) (d := (579107 / 100000 : ℚ)) (j := 6)
        (lo := (96480 / 1000 : ℝ)) (hi := (96595 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked summed count gives a semiprime witness on
`[96595/1000, 96708/1000]` at coefficient 0.28. -/
theorem target028_sum_cell10 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (96595 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 96708 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_group hn ho hp hq hpq hprod hGRH 569 182399201633205217
      target028_group569_count (D := (39744 / 1000 : ℝ))
  · have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 182399201633205217 58 32 (39744 / 1000) 41 = true
            from by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (48 : ℚ)) (d := (579107 / 100000 : ℚ)) (j := 6)
        (lo := (96595 / 1000 : ℝ)) (hi := (96708 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The summed group certificates cover distinct semiprimes between scales
88.181 and 96.708 under GRH. -/
theorem target028_semiprime_88181_96708 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (88181 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 96708 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h0 : Real.log n ≤ 89591 / 1000
  · exact target028_sum_cell0 hn ho hp hq hpq hprod hGRH hL h0
  by_cases h1 : Real.log n ≤ 90530 / 1000
  · exact target028_sum_cell1 hn ho hp hq hpq hprod hGRH (le_of_not_ge h0) h1
  by_cases h2 : Real.log n ≤ 91114 / 1000
  · exact target028_sum_cell2 hn ho hp hq hpq hprod hGRH (le_of_not_ge h1) h2
  by_cases h3 : Real.log n ≤ 93356 / 1000
  · exact target028_sum_cell3 hn ho hp hq hpq hprod hGRH (le_of_not_ge h2) h3
  by_cases h4 : Real.log n ≤ 94635 / 1000
  · exact target028_sum_cell4 hn ho hp hq hpq hprod hGRH (le_of_not_ge h3) h4
  by_cases h5 : Real.log n ≤ 95444 / 1000
  · exact target028_sum_cell5 hn ho hp hq hpq hprod hGRH (le_of_not_ge h4) h5
  by_cases h6 : Real.log n ≤ 95907 / 1000
  · exact target028_sum_cell6 hn ho hp hq hpq hprod hGRH (le_of_not_ge h5) h6
  by_cases h7 : Real.log n ≤ 96251 / 1000
  · exact target028_sum_cell7 hn ho hp hq hpq hprod hGRH (le_of_not_ge h6) h7
  by_cases h8 : Real.log n ≤ 96480 / 1000
  · exact target028_sum_cell8 hn ho hp hq hpq hprod hGRH (le_of_not_ge h7) h8
  by_cases h9 : Real.log n ≤ 96595 / 1000
  · exact target028_sum_cell9 hn ho hp hq hpq hprod hGRH (le_of_not_ge h8) h9
  exact target028_sum_cell10 hn ho hp hq hpq hprod hGRH (le_of_not_ge h9) hU

end PseudoPrime.PrimeTestBounds.MillerRabin

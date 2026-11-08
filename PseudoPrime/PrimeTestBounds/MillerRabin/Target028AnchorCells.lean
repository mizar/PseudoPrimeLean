/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028AnchorSupply

/-! # Semiprime intervals from even-character anchors -/

@[expose] public section

-- The previously certified count rows require deeper reduction.
set_option maxRecDepth 65536

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The checked count and even anchor give a semiprime witness on
`[15153/1000, 25567/1000]` at coefficient 0.28. -/
theorem target028_anchor_cell0 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (15153 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 25567 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed43_197 hn ho hp hq hpq hprod hGRH 112 (by decide) (D :=
      (8789 / 1000 : ℝ))
  · change (8789 / 1000 : ℝ) ≤ Real.log (6562 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 6562 13 32 (8789 / 1000) 10 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (8 : ℚ)) (d := (324969 / 100000 : ℚ)) (j := 3)
        (lo := (15153 / 1000 : ℝ)) (hi := (25567 / 1000 : ℝ))
    · exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked count and even anchor give a semiprime witness on
`[25567/1000, 36645/1000]` at coefficient 0.28. -/
theorem target028_anchor_cell1 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (25567 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 36645 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed113 hn ho hp hq hpq hprod hGRH 174 (by decide) (D :=
      (13381 / 1000 : ℝ))
  · change (13381 / 1000 : ℝ) ≤ Real.log (647875 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 647875 20 32 (13381 / 1000) 15 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (12 : ℚ)) (d := (193673 / 50000 : ℚ)) (j := 4)
        (lo := (25567 / 1000 : ℝ)) (hi := (36645 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked count and even anchor give a semiprime witness on
`[36645/1000, 48434/1000]` at coefficient 0.28. -/
theorem target028_anchor_cell2 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (36645 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 48434 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed373 hn ho hp hq hpq hprod hGRH 236 (by decide) (D :=
      (18522 / 1000 : ℝ))
  · change (18522 / 1000 : ℝ) ≤ Real.log (110739047 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 110739047 27 32 (18522 / 1000) 20 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (16 : ℚ)) (d := (85669 / 20000 : ℚ)) (j := 4) (lo :=
        (36645 / 1000 : ℝ)) (hi := (48434 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked count and even anchor give a semiprime witness on
`[48434/1000, 57868/1000]` at coefficient 0.28. -/
theorem target028_anchor_cell3 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (48434 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 57868 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed373 hn ho hp hq hpq hprod hGRH 304 (by decide) (D :=
      (22408 / 1000 : ℝ))
  · change (22408 / 1000 : ℝ) ≤ Real.log (5394895357 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 5394895357 33 32 (22408 / 1000) 24 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (24 : ℚ)) (d := (241969 / 50000 : ℚ)) (j := 5)
        (lo := (48434 / 1000 : ℝ)) (hi := (57868 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked count and even anchor give a semiprime witness on
`[57868/1000, 63496/1000]` at coefficient 0.28. -/
theorem target028_anchor_cell4 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (57868 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 63496 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed373 hn ho hp hq hpq hprod hGRH 354 (by decide) (D :=
      (25058 / 1000 : ℝ))
  · change (25058 / 1000 : ℝ) ≤ Real.log (76351017317 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 76351017317 37 32 (25058 / 1000) 27 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (24 : ℚ)) (d := (241969 / 50000 : ℚ)) (j := 5)
        (lo := (57868 / 1000 : ℝ)) (hi := (63496 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked count and even anchor give a semiprime witness on
`[63496/1000, 67943/1000]` at coefficient 0.28. -/
theorem target028_anchor_cell5 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (63496 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 67943 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed373 hn ho hp hq hpq hprod hGRH 388 (by decide) (D :=
      (26761 / 1000 : ℝ))
  · change (26761 / 1000 : ℝ) ≤ Real.log (419194129747 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 419194129747 39 32 (26761 / 1000) 28 = true from
            by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (63496 / 1000 : ℝ)) (hi := (67943 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked count and even anchor give a semiprime witness on
`[67943/1000, 70335/1000]` at coefficient 0.28. -/
theorem target028_anchor_cell6 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (67943 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 70335 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed373 hn ho hp hq hpq hprod hGRH 411 (by decide) (D :=
      (27887 / 1000 : ℝ))
  · change (27887 / 1000 : ℝ) ≤ Real.log (1292798056937 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 1292798056937 41 32 (27887 / 1000) 29 = true from
            by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (67943 / 1000 : ℝ)) (hi := (70335 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The checked count and even anchor give a semiprime witness on
`[70335/1000, 71609/1000]` at coefficient 0.28. -/
theorem target028_anchor_cell7 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (70335 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 71609 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_semiprime_seed373 hn ho hp hq hpq hprod hGRH 424 (by decide) (D :=
      (28487 / 1000 : ℝ))
  · change (28487 / 1000 : ℝ) ≤ Real.log (2355963632521 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 2355963632521 42 32 (28487 / 1000) 30 = true from
            by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · nlinarith only [hL]
  · apply
      target028_semiprime_anchor_envelope (b := (32 : ℚ)) (d := (65379 / 12500 : ℚ)) (j := 5) (lo :=
        (70335 / 1000 : ℝ)) (hi := (71609 / 1000 : ℝ))
    · apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      apply List.mem_cons_of_mem
      exact List.mem_cons_self
    all_goals norm_num only [Rat.cast_ofNat, Rat.cast_div] at *
    all_goals linarith only [hL, hU]

/-- The eight certified cells cover all distinct semiprimes between logarithmic
scales 15.153 and 71.609 using finite weighted counts and even anchors. -/
theorem target028_semiprime_15153_71609 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (15153 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 71609 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h0 : Real.log n ≤ 25567 / 1000
  · exact target028_anchor_cell0 hn ho hp hq hpq hprod hGRH hL h0
  by_cases h1 : Real.log n ≤ 36645 / 1000
  · exact target028_anchor_cell1 hn ho hp hq hpq hprod hGRH (le_of_not_ge h0) h1
  by_cases h2 : Real.log n ≤ 48434 / 1000
  · exact target028_anchor_cell2 hn ho hp hq hpq hprod hGRH (le_of_not_ge h1) h2
  by_cases h3 : Real.log n ≤ 57868 / 1000
  · exact target028_anchor_cell3 hn ho hp hq hpq hprod hGRH (le_of_not_ge h2) h3
  by_cases h4 : Real.log n ≤ 63496 / 1000
  · exact target028_anchor_cell4 hn ho hp hq hpq hprod hGRH (le_of_not_ge h3) h4
  by_cases h5 : Real.log n ≤ 67943 / 1000
  · exact target028_anchor_cell5 hn ho hp hq hpq hprod hGRH (le_of_not_ge h4) h5
  by_cases h6 : Real.log n ≤ 70335 / 1000
  · exact target028_anchor_cell6 hn ho hp hq hpq hprod hGRH (le_of_not_ge h5) h6
  exact target028_anchor_cell7 hn ho hp hq hpq hprod hGRH (le_of_not_ge h6) hU

end PseudoPrime.PrimeTestBounds.MillerRabin

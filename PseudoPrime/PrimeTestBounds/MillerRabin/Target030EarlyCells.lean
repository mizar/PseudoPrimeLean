/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030ExtendedCell
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030FirstCell

/-! # Further low-scale semiprime cells using the first supply -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, the explicit eight-prime weighted count proves the 0.30
semiprime bound on this closed logarithmic interval. The rational logarithm
and local radius certificates cover both branches of the candidate theorem. -/
theorem target030_semiprime_cell_2 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (837 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 8743 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_first_supply hn ho hp hq hpq hprod hGRH 45 (by decide) (D :=
      (4158883 / 1000000 : ℝ))
  · change (4158883 / 1000000 : ℝ) ≤ Real.log (64 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 64 6 32 (4158883 / 1000000) 5 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only at ⊢
    exact h
  · nlinarith only [hL]
  · apply
      local_envelope_le_03_interval (lo := (837 / 100 : ℝ)) (hi := (8743 / 1000 : ℝ)) (R :=
        (4584437 / 1000000 : ℝ)) (by norm_num only) hL hU
    all_goals norm_num only

/-- Under GRH, the explicit eight-prime weighted count proves the 0.30
semiprime bound on this closed logarithmic interval. The rational logarithm
and local radius certificates cover both branches of the candidate theorem. -/
theorem target030_semiprime_cell_3 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (8743 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 9079 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_first_supply hn ho hp hq hpq hprod hGRH 47 (by decide) (D :=
      (4290459 / 1000000 : ℝ))
  · change (4290459 / 1000000 : ℝ) ≤ Real.log (73 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 73 7 32 (4290459 / 1000000) 5 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only at ⊢
    exact h
  · nlinarith only [hL]
  · apply
      local_envelope_le_03_interval (lo := (8743 / 1000 : ℝ)) (hi := (9079 / 1000 : ℝ)) (R :=
        (4788738 / 1000000 : ℝ)) (by norm_num only) hL hU
    all_goals norm_num only

/-- Under GRH, the explicit eight-prime weighted count proves the 0.30
semiprime bound on this closed logarithmic interval. The rational logarithm
and local radius certificates cover both branches of the candidate theorem. -/
theorem target030_semiprime_cell_4 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (9079 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 1883 / 200) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_first_supply hn ho hp hq hpq hprod hGRH 49 (by decide) (D :=
      (4442651 / 1000000 : ℝ))
  · change (4442651 / 1000000 : ℝ) ≤ Real.log (85 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 85 7 32 (4442651 / 1000000) 5 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only at ⊢
    exact h
  · nlinarith only [hL]
  · apply
      local_envelope_le_03_interval (lo := (9079 / 1000 : ℝ)) (hi := (1883 / 200 : ℝ)) (R :=
        (4972773 / 1000000 : ℝ)) (by norm_num only) hL hU
    all_goals norm_num only

/-- Under GRH, the explicit eight-prime weighted count proves the 0.30
semiprime bound on this closed logarithmic interval. The rational logarithm
and local radius certificates cover both branches of the candidate theorem. -/
theorem target030_semiprime_cell_5 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (1883 / 200 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 9751 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_first_supply hn ho hp hq hpq hprod hGRH 51 (by decide) (D :=
      (4595119 / 1000000 : ℝ))
  · change (4595119 / 1000000 : ℝ) ≤ Real.log (99 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 99 7 32 (4595119 / 1000000) 5 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only at ⊢
    exact h
  · nlinarith only [hL]
  · apply
      local_envelope_le_03_interval (lo := (1883 / 200 : ℝ)) (hi := (9751 / 1000 : ℝ)) (R :=
        (5156807 / 1000000 : ℝ)) (by norm_num only) hL hU
    all_goals norm_num only

/-- Under GRH, the explicit eight-prime weighted count proves the 0.30
semiprime bound on this closed logarithmic interval. The rational logarithm
and local radius certificates cover both branches of the candidate theorem. -/
theorem target030_semiprime_cell_6 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (9751 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 10059 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_reject_first_supply hn ho hp hq hpq hprod hGRH 53 (by decide) (D :=
      (4718498 / 1000000 : ℝ))
  · change (4718498 / 1000000 : ℝ) ≤ Real.log (112 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 112 7 32 (4718498 / 1000000) 5 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only at ⊢
    exact h
  · nlinarith only [hL]
  · apply
      local_envelope_le_03_interval (lo := (9751 / 1000 : ℝ)) (hi := (10059 / 1000 : ℝ)) (R :=
        (5340842 / 1000000 : ℝ)) (by norm_num only) hL hU
    all_goals norm_num only

/-- Under GRH, every distinct odd semiprime with logarithm from 8 through
10.059 has a rejecting prime within the 0.30 target. The six certified closed
cells meet at their shared rational endpoints. -/
theorem exists_prime_reject_03_semiprime_log10 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 10059 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h1 : Real.log n ≤ 837 / 100
  · exact exists_prime_reject_03_first_semiprime hn ho hp hq hpq hprod hGRH hL h1
  · by_cases h2 : Real.log n ≤ 8743 / 1000
    · exact target030_semiprime_cell_2 hn ho hp hq hpq hprod hGRH (le_of_not_ge h1) h2
    · by_cases h3 : Real.log n ≤ 9079 / 1000
      · exact target030_semiprime_cell_3 hn ho hp hq hpq hprod hGRH (le_of_not_ge h2) h3
      · by_cases h4 : Real.log n ≤ 1883 / 200
        · exact target030_semiprime_cell_4 hn ho hp hq hpq hprod hGRH (le_of_not_ge h3) h4
        · by_cases h5 : Real.log n ≤ 9751 / 1000
          · exact target030_semiprime_cell_5 hn ho hp hq hpq hprod hGRH (le_of_not_ge h4) h5
          · exact target030_semiprime_cell_6 hn ho hp hq hpq hprod hGRH (le_of_not_ge h5) hU

end PseudoPrime.PrimeTestBounds.MillerRabin

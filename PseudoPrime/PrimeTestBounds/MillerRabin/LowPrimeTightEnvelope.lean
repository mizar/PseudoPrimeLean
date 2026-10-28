/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.LowPrimeTightComparison

/-! # Extended low-prime envelope and exact interval selection -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The current envelope intersected with nine extended low-prime certificates.
Each guarded constant uses its proved cap and otherwise returns the current envelope. -/
noncomputable def lowPrimeTightEnvelope (n : ℕ) : ℝ :=
  let L := Real.log n
  let B := nextWitnessEnvelope n
  min B <|
    min (if L ≤ 8032 / 1000 then 23 else B) <|
    min (if L ≤ 8271 / 1000 then 29 else B) <|
    min (if L ≤ 8934 / 1000 then 31 else B) <|
    min (if L ≤ 9339 / 1000 then 37 else B) <|
    min (if L ≤ 9532 / 1000 then 41 else B) <|
    min (if L ≤ 9902 / 1000 then 43 else B) <|
    min (if L ≤ 10422 / 1000 then 47 else B) <|
    min (if L ≤ 10907 / 1000 then 53 else B) (if L ≤ 11062 / 1000 then 59 else B)

/-- Ascending low-prime interval selection with the current envelope as fallback.
Inputs below 3000 keep the existing small-interval value, including the exception at 2047. -/
noncomputable def lowPrimeTightSelected (n : ℕ) : ℝ :=
  if n < 3000 then smallIntervalBound n
  else
    if Real.log n ≤ 8032 / 1000 then 23
    else
      if Real.log n ≤ 8271 / 1000 then 29
      else
        if Real.log n ≤ 8934 / 1000 then 31
        else
          if Real.log n ≤ 9339 / 1000 then 37
          else
            if Real.log n ≤ 9532 / 1000 then 41
            else
              if Real.log n ≤ 9902 / 1000 then 43
              else
                if Real.log n ≤ 10422 / 1000 then 47
                else
                  if Real.log n ≤ 10907 / 1000 then 53
                  else if Real.log n ≤ 11062 / 1000 then 59 else nextSelectedEnvelope n

/-- For every natural input, the extended envelope is no larger than the current one.
This is the first projection from its defining minimum and requires no mathematical hypotheses. -/
theorem lowPrimeTightEnvelope_le_next (n : ℕ) :
    lowPrimeTightEnvelope n ≤ nextWitnessEnvelope n := by exact min_le_left _ _

/-- A common lower bound for the current envelope and every valid profile bounds
the guarded minimum. Resolve each guard and combine the nine inequalities by min. -/
theorem lowPrimeTight_lower {n : ℕ} {C : ℝ} (hB : C ≤ nextWitnessEnvelope n)
    (hF : ∀ f : LLS.PaperStatements.LowPrimeProfile, Real.log n ≤ f.tightLogCap → C ≤ f.bound) :
    C ≤ lowPrimeTightEnvelope n := by
  classical
  have guard (f : LLS.PaperStatements.LowPrimeProfile) :
    C ≤ (if Real.log n ≤ f.tightLogCap then (f.bound : ℝ) else nextWitnessEnvelope n) := by
    by_cases h : Real.log n ≤ f.tightLogCap
    · rw [ite_eq_left h]
      exact hF f h
    · rw [ite_eq_right h]
      exact hB
  simpa only [lowPrimeTightEnvelope, LLS.PaperStatements.LowPrimeProfile.tightLogCap,
    LLS.PaperStatements.LowPrimeProfile.bound, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using
    le_min hB
      (le_min (guard .p23)
        (le_min (guard .p29)
          (le_min (guard .p31)
            (le_min (guard .p37)
              (le_min (guard .p41)
                (le_min (guard .p43) (le_min (guard .p47) (le_min (guard .p53) (guard .p59)))))))))

/-- Every profile bounds the new envelope on its certified logarithmic domain.
Project to the selected guarded candidate and eliminate its true guard. -/
theorem lowPrimeTight_le_profile (f : LLS.PaperStatements.LowPrimeProfile) {n : ℕ}
    (hL : Real.log n ≤ f.tightLogCap) : lowPrimeTightEnvelope n ≤ f.bound := by
  cases f
  · norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
      Rat.cast_ofNat] at hL
    norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
    have h :
      lowPrimeTightEnvelope n ≤
        (if Real.log n ≤ 8032 / 1000 then 23 else nextWitnessEnvelope n) := by
      exact (min_le_right _ _).trans ((min_le_left _ _))
    have hcap : Real.log n ≤ 8032 / 1000 := by linarith only [hL]
    simpa only [ite_eq_left hcap] using h
  · norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
      Rat.cast_ofNat] at hL
    norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
    have h :
      lowPrimeTightEnvelope n ≤
        (if Real.log n ≤ 8271 / 1000 then 29 else nextWitnessEnvelope n) := by
      exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_left _ _)))
    have hcap : Real.log n ≤ 8271 / 1000 := by linarith only [hL]
    simpa only [ite_eq_left hcap] using h
  · norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
      Rat.cast_ofNat] at hL
    norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
    have h :
      lowPrimeTightEnvelope n ≤
        (if Real.log n ≤ 8934 / 1000 then 31 else nextWitnessEnvelope n) := by
      exact
        (min_le_right _ _).trans
          ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_left _ _))))
    have hcap : Real.log n ≤ 8934 / 1000 := by linarith only [hL]
    simpa only [ite_eq_left hcap] using h
  · norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
      Rat.cast_ofNat] at hL
    norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
    have h :
      lowPrimeTightEnvelope n ≤
        (if Real.log n ≤ 9339 / 1000 then 37 else nextWitnessEnvelope n) := by
      exact
        (min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_left _ _)))))
    have hcap : Real.log n ≤ 9339 / 1000 := by linarith only [hL]
    simpa only [ite_eq_left hcap] using h
  · norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
      Rat.cast_ofNat] at hL
    norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
    have h :
      lowPrimeTightEnvelope n ≤
        (if Real.log n ≤ 9532 / 1000 then 41 else nextWitnessEnvelope n) := by
      exact
        (min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans
              ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_left _ _))))))
    have hcap : Real.log n ≤ 9532 / 1000 := by linarith only [hL]
    simpa only [ite_eq_left hcap] using h
  · norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
      Rat.cast_ofNat] at hL
    norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
    have h :
      lowPrimeTightEnvelope n ≤
        (if Real.log n ≤ 9902 / 1000 then 43 else nextWitnessEnvelope n) := by
      exact
        (min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans
              ((min_le_right _ _).trans
                ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_left _ _)))))))
    have hcap : Real.log n ≤ 9902 / 1000 := by linarith only [hL]
    simpa only [ite_eq_left hcap] using h
  · norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
      Rat.cast_ofNat] at hL
    norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
    have h :
      lowPrimeTightEnvelope n ≤
        (if Real.log n ≤ 10422 / 1000 then 47 else nextWitnessEnvelope n) := by
      exact
        (min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans
              ((min_le_right _ _).trans
                ((min_le_right _ _).trans
                  ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_left _ _))))))))
    have hcap : Real.log n ≤ 10422 / 1000 := by linarith only [hL]
    simpa only [ite_eq_left hcap] using h
  · norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
      Rat.cast_ofNat] at hL
    norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
    have h :
      lowPrimeTightEnvelope n ≤
        (if Real.log n ≤ 10907 / 1000 then 53 else nextWitnessEnvelope n) := by
      exact
        (min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans
              ((min_le_right _ _).trans
                ((min_le_right _ _).trans
                  ((min_le_right _ _).trans
                    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_left _ _)))))))))
    have hcap : Real.log n ≤ 10907 / 1000 := by linarith only [hL]
    simpa only [ite_eq_left hcap] using h
  · norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
      Rat.cast_ofNat] at hL
    norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
    have h :
      lowPrimeTightEnvelope n ≤
        (if Real.log n ≤ 11062 / 1000 then 59 else nextWitnessEnvelope n) := by
      exact
        (min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans
              ((min_le_right _ _).trans
                ((min_le_right _ _).trans
                  ((min_le_right _ _).trans
                    ((min_le_right _ _).trans
                      ((min_le_right _ _).trans ((min_le_right _ _).trans ((le_refl _))))))))))
    have hcap : Real.log n ≤ 11062 / 1000 := by linarith only [hL]
    simpa only [ite_eq_left hcap] using h

/-- Under GRH, every odd composite above one has a least rejecting prime bounded
by the extended envelope. Transfer all valid profile witnesses to the same least prime,
then combine the bounds using the minimum interface. -/
theorem exists_least_lowPrimeTightEnvelope {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ lowPrimeTightEnvelope n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_nextEnvelope hn ho hc hGRH
  have transfer (f : LLS.PaperStatements.LowPrimeProfile) (hL : Real.log n ≤ f.tightLogCap) :
    (p : ℝ) ≤ f.bound := by
    obtain ⟨q, hq, hqb, hqr⟩ := exists_prime_endpointLowTight f hn ho hc hGRH hL
    exact (Nat.cast_le.mpr (hm q hq hqr)).trans hqb
  exact ⟨p, hp, hr, lowPrimeTight_lower hb transfer, hm⟩

/-- Under GRH, every odd composite above one has an actual rejecting prime below
the extended low-prime envelope. Forget the leastness of the common witness. -/
theorem exists_prime_lowPrimeTightEnvelope {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ lowPrimeTightEnvelope n ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hr, hb, _⟩ := exists_least_lowPrimeTightEnvelope hn ho hc hGRH
  exact ⟨p, hp, hb, hr⟩

/-- The preceding tight cap, or zero for the first profile. This finite datum
identifies which constant is selected after all preceding caps have been excluded. -/
noncomputable def tightLowPreviousCap : LLS.PaperStatements.LowPrimeProfile → ℝ
  | .p23 => 0
  | .p29 => 8032 / 1000
  | .p31 => 8271 / 1000
  | .p37 => 8934 / 1000
  | .p41 => 9339 / 1000
  | .p43 => 9532 / 1000
  | .p47 => 9902 / 1000
  | .p53 => 10422 / 1000
  | .p59 => 10907 / 1000

/-- Above a profile's preceding tight cap and below its own cap, its bound is
no larger than the current envelope for inputs at least 3000. Resolve the current
low-prime selection or its subsequent fixed-61 branch. -/
theorem lowPrimeTight_base_lower (f : LLS.PaperStatements.LowPrimeProfile) {n : ℕ} (hn : 1 < n)
    (hN : 3000 ≤ n) (hL : tightLowPreviousCap f < Real.log n) (hU : Real.log n ≤ f.tightLogCap) :
    (f.bound : ℝ) ≤ nextWitnessEnvelope n := by
  have hsmall : ¬n < 3000 := not_lt.mpr hN
  cases f
  · norm_num only [tightLowPreviousCap, LLS.PaperStatements.LowPrimeProfile.tightLogCap,
      Rat.cast_div, Rat.cast_ofNat] at hL hU
    by_cases ht : Real.log n ≤ 553 / 50
    · rw [next_eq_low ht, lowPrime_eq_selected hn]
      simp only [lowPrimeSelected, ite_eq_right hsmall, ite_eq_left ht]
      try split_ifs
      all_goals norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
    · rw [next_eq_fixed61 hn hN (lt_of_not_ge ht) (by linarith only [hU])]
      norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
  · norm_num only [tightLowPreviousCap, LLS.PaperStatements.LowPrimeProfile.tightLogCap,
      Rat.cast_div, Rat.cast_ofNat] at hL hU
    by_cases ht : Real.log n ≤ 553 / 50
    · rw [next_eq_low ht, lowPrime_eq_selected hn]
      simp only [lowPrimeSelected, ite_eq_right hsmall,
        ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 401 / 50), ite_eq_left ht]
      try split_ifs
      all_goals norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
    · rw [next_eq_fixed61 hn hN (lt_of_not_ge ht) (by linarith only [hU])]
      norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
  · norm_num only [tightLowPreviousCap, LLS.PaperStatements.LowPrimeProfile.tightLogCap,
      Rat.cast_div, Rat.cast_ofNat] at hL hU
    by_cases ht : Real.log n ≤ 553 / 50
    · rw [next_eq_low ht, lowPrime_eq_selected hn]
      simp only [lowPrimeSelected, ite_eq_right hsmall,
        ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 401 / 50),
        ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 413 / 50), ite_eq_left ht]
      try split_ifs
      all_goals norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
    · rw [next_eq_fixed61 hn hN (lt_of_not_ge ht) (by linarith only [hU])]
      norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
  · norm_num only [tightLowPreviousCap, LLS.PaperStatements.LowPrimeProfile.tightLogCap,
      Rat.cast_div, Rat.cast_ofNat] at hL hU
    by_cases ht : Real.log n ≤ 553 / 50
    · rw [next_eq_low ht, lowPrime_eq_selected hn]
      simp only [lowPrimeSelected, ite_eq_right hsmall,
        ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 401 / 50),
        ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 413 / 50),
        ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 893 / 100), ite_eq_left ht]
      try split_ifs
      all_goals norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
    · rw [next_eq_fixed61 hn hN (lt_of_not_ge ht) (by linarith only [hU])]
      norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
  · norm_num only [tightLowPreviousCap, LLS.PaperStatements.LowPrimeProfile.tightLogCap,
      Rat.cast_div, Rat.cast_ofNat] at hL hU
    by_cases ht : Real.log n ≤ 553 / 50
    · rw [next_eq_low ht, lowPrime_eq_selected hn]
      simp only [lowPrimeSelected, ite_eq_right hsmall,
        ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 401 / 50),
        ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 413 / 50),
        ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 893 / 100),
        ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 933 / 100), ite_eq_left ht]
      try split_ifs
      all_goals norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
    · rw [next_eq_fixed61 hn hN (lt_of_not_ge ht) (by linarith only [hU])]
      norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
  · norm_num only [tightLowPreviousCap, LLS.PaperStatements.LowPrimeProfile.tightLogCap,
      Rat.cast_div, Rat.cast_ofNat] at hL hU
    by_cases ht : Real.log n ≤ 553 / 50
    · rw [next_eq_low ht, lowPrime_eq_selected hn]
      simp only [lowPrimeSelected, ite_eq_right hsmall,
        ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 401 / 50),
        ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 413 / 50),
        ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 893 / 100),
        ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 933 / 100),
        ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 238 / 25), ite_eq_left ht]
      try split_ifs
      all_goals norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
    · rw [next_eq_fixed61 hn hN (lt_of_not_ge ht) (by linarith only [hU])]
      norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
  · norm_num only [tightLowPreviousCap, LLS.PaperStatements.LowPrimeProfile.tightLogCap,
      Rat.cast_div, Rat.cast_ofNat] at hL hU
    by_cases ht : Real.log n ≤ 553 / 50
    · rw [next_eq_low ht, lowPrime_eq_selected hn]
      simp only [lowPrimeSelected, ite_eq_right hsmall,
        ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 401 / 50),
        ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 413 / 50),
        ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 893 / 100),
        ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 933 / 100),
        ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 238 / 25),
        ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 989 / 100), ite_eq_left ht]
      try split_ifs
      all_goals norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
    · rw [next_eq_fixed61 hn hN (lt_of_not_ge ht) (by linarith only [hU])]
      norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
  · norm_num only [tightLowPreviousCap, LLS.PaperStatements.LowPrimeProfile.tightLogCap,
      Rat.cast_div, Rat.cast_ofNat] at hL hU
    by_cases ht : Real.log n ≤ 553 / 50
    · rw [next_eq_low ht, lowPrime_eq_selected hn]
      simp only [lowPrimeSelected, ite_eq_right hsmall,
        ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 401 / 50),
        ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 413 / 50),
        ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 893 / 100),
        ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 933 / 100),
        ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 238 / 25),
        ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 989 / 100),
        ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 521 / 50), ite_eq_left ht]
      try split_ifs
      all_goals norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
    · rw [next_eq_fixed61 hn hN (lt_of_not_ge ht) (by linarith only [hU])]
      norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
  · norm_num only [tightLowPreviousCap, LLS.PaperStatements.LowPrimeProfile.tightLogCap,
      Rat.cast_div, Rat.cast_ofNat] at hL hU
    by_cases ht : Real.log n ≤ 553 / 50
    · rw [next_eq_low ht, lowPrime_eq_selected hn]
      simp only [lowPrimeSelected, ite_eq_right hsmall,
        ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 401 / 50),
        ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 413 / 50),
        ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 893 / 100),
        ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 933 / 100),
        ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 238 / 25),
        ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 989 / 100),
        ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 521 / 50),
        ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 109 / 10), ite_eq_left ht]
      all_goals norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
    · rw [next_eq_fixed61 hn hN (lt_of_not_ge ht) (by linarith only [hU])]
      norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]

/-- A profile selected after its preceding tight cap is no larger than any other
currently valid tight profile. Check the finite cap ordering by rational arithmetic. -/
theorem lowPrimeTight_bounds_order (f g : LLS.PaperStatements.LowPrimeProfile) {n : ℕ}
    (hL : tightLowPreviousCap f < Real.log n) (hG : Real.log n ≤ g.tightLogCap) :
    (f.bound : ℝ) ≤ g.bound := by
  cases f <;> cases g <;>
    norm_num only [tightLowPreviousCap, LLS.PaperStatements.LowPrimeProfile.tightLogCap,
      LLS.PaperStatements.LowPrimeProfile.bound, Rat.cast_div, Rat.cast_ofNat,
      Nat.cast_ofNat] at hL hG ⊢ <;>
    linarith only [hL, hG]

/-- Within a profile's tight selection interval, the guarded envelope equals its
constant. Combine its upper projection with the common lower-bound interface. -/
theorem lowPrimeTight_eq_profile (f : LLS.PaperStatements.LowPrimeProfile) {n : ℕ} (hn : 1 < n)
    (hN : 3000 ≤ n) (hL : tightLowPreviousCap f < Real.log n) (hU : Real.log n ≤ f.tightLogCap) :
    lowPrimeTightEnvelope n = f.bound := by
  apply le_antisymm (lowPrimeTight_le_profile f hU)
  exact
    lowPrimeTight_lower (lowPrimeTight_base_lower f hn hN hL hU)
      (fun g hG => lowPrimeTight_bounds_order f g hL hG)

/-- If the current envelope is at most 23, all nine new constants preserve it.
Use their finite lower bounds to show equality of the guarded minimum. -/
theorem lowPrimeTight_eq_base {n : ℕ} (hB : nextWitnessEnvelope n ≤ 23) :
    lowPrimeTightEnvelope n = nextWitnessEnvelope n := by
  apply le_antisymm (lowPrimeTightEnvelope_le_next n)
  apply lowPrimeTight_lower le_rfl
  intro f _
  apply hB.trans
  cases f <;> norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]

/-- For every natural input above one, the guarded minimum equals the ascending
nine-cap selection. Small inputs retain their existing bound; larger inputs use the
profile ordering, and beyond the final cap all guards return the current envelope. -/
theorem lowPrimeTight_eq_selected {n : ℕ} (hn : 1 < n) :
    lowPrimeTightEnvelope n = lowPrimeTightSelected n := by
  by_cases hN : n < 3000
  · have hb : nextWitnessEnvelope n ≤ 23 := by
      rw [next_eq_selected hn]
      simp only [nextSelectedEnvelope, ite_eq_left hN]
      dsimp only [smallIntervalBound]
      split_ifs <;> norm_num only
    rw [lowPrimeTight_eq_base hb, next_eq_selected hn]
    simp only [nextSelectedEnvelope, lowPrimeTightSelected, ite_eq_left hN]
  · have hlarge : 3000 ≤ n := le_of_not_gt hN
    by_cases h23 : Real.log n ≤ 8032 / 1000
    · have hprev : tightLowPreviousCap .p23 < Real.log n := by
        exact Real.log_pos (by exact_mod_cast hn)
      have he :=
        lowPrimeTight_eq_profile .p23 hn hlarge hprev
          (by
            norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
              Rat.cast_ofNat]
            linarith only [h23])
      simpa only [lowPrimeTightSelected, ite_eq_right hN, ite_eq_left h23,
        LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using he
    · by_cases h29 : Real.log n ≤ 8271 / 1000
      · have hprev : tightLowPreviousCap .p29 < Real.log n := by exact lt_of_not_ge h23
        have he :=
          lowPrimeTight_eq_profile .p29 hn hlarge hprev
            (by
              norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
                Rat.cast_ofNat]
              linarith only [h29])
        simpa only [lowPrimeTightSelected, ite_eq_right hN, ite_eq_right h23, ite_eq_left h29,
          LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using he
      · by_cases h31 : Real.log n ≤ 8934 / 1000
        · have hprev : tightLowPreviousCap .p31 < Real.log n := by exact lt_of_not_ge h29
          have he :=
            lowPrimeTight_eq_profile .p31 hn hlarge hprev
              (by
                norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
                  Rat.cast_ofNat]
                linarith only [h31])
          simpa only [lowPrimeTightSelected, ite_eq_right hN, ite_eq_right h23, ite_eq_right h29,
            ite_eq_left h31, LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using he
        · by_cases h37 : Real.log n ≤ 9339 / 1000
          · have hprev : tightLowPreviousCap .p37 < Real.log n := by exact lt_of_not_ge h31
            have he :=
              lowPrimeTight_eq_profile .p37 hn hlarge hprev
                (by
                  norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
                    Rat.cast_ofNat]
                  linarith only [h37])
            simpa only [lowPrimeTightSelected, ite_eq_right hN, ite_eq_right h23, ite_eq_right h29,
              ite_eq_right h31, ite_eq_left h37, LLS.PaperStatements.LowPrimeProfile.bound,
              Nat.cast_ofNat] using he
          · by_cases h41 : Real.log n ≤ 9532 / 1000
            · have hprev : tightLowPreviousCap .p41 < Real.log n := by exact lt_of_not_ge h37
              have he :=
                lowPrimeTight_eq_profile .p41 hn hlarge hprev
                  (by
                    norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
                      Rat.cast_ofNat]
                    linarith only [h41])
              simpa only [lowPrimeTightSelected, ite_eq_right hN, ite_eq_right h23,
                ite_eq_right h29, ite_eq_right h31, ite_eq_right h37, ite_eq_left h41,
                LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using he
            · by_cases h43 : Real.log n ≤ 9902 / 1000
              · have hprev : tightLowPreviousCap .p43 < Real.log n := by exact lt_of_not_ge h41
                have he :=
                  lowPrimeTight_eq_profile .p43 hn hlarge hprev
                    (by
                      norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
                        Rat.cast_ofNat]
                      linarith only [h43])
                simpa only [lowPrimeTightSelected, ite_eq_right hN, ite_eq_right h23,
                  ite_eq_right h29, ite_eq_right h31, ite_eq_right h37, ite_eq_right h41,
                  ite_eq_left h43, LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
                  he
              · by_cases h47 : Real.log n ≤ 10422 / 1000
                · have hprev : tightLowPreviousCap .p47 < Real.log n := by exact lt_of_not_ge h43
                  have he :=
                    lowPrimeTight_eq_profile .p47 hn hlarge hprev
                      (by
                        norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap,
                          Rat.cast_div, Rat.cast_ofNat]
                        linarith only [h47])
                  simpa only [lowPrimeTightSelected, ite_eq_right hN, ite_eq_right h23,
                    ite_eq_right h29, ite_eq_right h31, ite_eq_right h37, ite_eq_right h41,
                    ite_eq_right h43, ite_eq_left h47, LLS.PaperStatements.LowPrimeProfile.bound,
                    Nat.cast_ofNat] using he
                · by_cases h53 : Real.log n ≤ 10907 / 1000
                  · have hprev : tightLowPreviousCap .p53 < Real.log n := by exact lt_of_not_ge h47
                    have he :=
                      lowPrimeTight_eq_profile .p53 hn hlarge hprev
                        (by
                          norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap,
                            Rat.cast_div, Rat.cast_ofNat]
                          linarith only [h53])
                    simpa only [lowPrimeTightSelected, ite_eq_right hN, ite_eq_right h23,
                      ite_eq_right h29, ite_eq_right h31, ite_eq_right h37, ite_eq_right h41,
                      ite_eq_right h43, ite_eq_right h47, ite_eq_left h53,
                      LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using he
                  · by_cases h59 : Real.log n ≤ 11062 / 1000
                    · have hprev : tightLowPreviousCap .p59 < Real.log n := by
                        exact lt_of_not_ge h53
                      have he :=
                        lowPrimeTight_eq_profile .p59 hn hlarge hprev
                          (by
                            norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap,
                              Rat.cast_div, Rat.cast_ofNat]
                            linarith only [h59])
                      simpa only [lowPrimeTightSelected, ite_eq_right hN, ite_eq_right h23,
                        ite_eq_right h29, ite_eq_right h31, ite_eq_right h37, ite_eq_right h41,
                        ite_eq_right h43, ite_eq_right h47, ite_eq_right h53, ite_eq_left h59,
                        LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using he
                    · have hg (f : LLS.PaperStatements.LowPrimeProfile) :
                        ¬Real.log n ≤ f.tightLogCap := by
                        intro h
                        cases f <;>
                          norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap,
                            Rat.cast_div, Rat.cast_ofNat] at h <;>
                          linarith only [h, lt_of_not_ge h59]
                      have he : lowPrimeTightEnvelope n = nextWitnessEnvelope n := by
                        apply le_antisymm (lowPrimeTightEnvelope_le_next n)
                        exact lowPrimeTight_lower le_rfl (fun f h => False.elim (hg f h))
                      rw [he, next_eq_selected hn]
                      simp only [lowPrimeTightSelected, ite_eq_right hN, ite_eq_right h23,
                        ite_eq_right h29, ite_eq_right h31, ite_eq_right h37, ite_eq_right h41,
                        ite_eq_right h43, ite_eq_right h47, ite_eq_right h53, ite_eq_right h59]

/-- Inputs between one and 3000 retain the existing small-interval bound.
Specialize the exact selection formula without substituting the separate pointwise bound. -/
theorem lowPrimeTight_eq_small {n : ℕ} (hn : 1 < n) (hN : n < 3000) :
    lowPrimeTightEnvelope n = smallIntervalBound n := by
  rw [lowPrimeTight_eq_selected hn]
  exact ite_eq_left hN

/-- Beyond the last tight cap, every new guard is false and the current envelope
is unchanged. The common lower-bound interface proves equality for all natural inputs. -/
theorem lowPrimeTight_eq_next_of_log {n : ℕ} (hL : 11062 / 1000 < Real.log n) :
    lowPrimeTightEnvelope n = nextWitnessEnvelope n := by
  apply le_antisymm (lowPrimeTightEnvelope_le_next n)
  apply lowPrimeTight_lower le_rfl
  intro f h
  exfalso
  cases f <;>
    norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
      Rat.cast_ofNat] at h <;>
    linarith only [h, hL]

/-- On each old-open to new-closed cap interval, the extended envelope strictly
improves the current selected envelope for inputs at least 3000. Compose its profile
projection with the continuous low-prime comparison. -/
theorem lowPrimeTight_strict (f : LLS.PaperStatements.LowPrimeProfile) {n : ℕ} (hn : 1 < n)
    (hN : 3000 ≤ n) (hL : (f.logCap : ℝ) < Real.log n) (hU : Real.log n ≤ f.tightLogCap) :
    lowPrimeTightEnvelope n < nextSelectedEnvelope n := by
  exact (lowPrimeTight_le_profile f hU).trans_lt (lowPrimeTight_lt_next f hn hN hL hU)

end PseudoPrime.PrimeTestBounds.MillerRabin

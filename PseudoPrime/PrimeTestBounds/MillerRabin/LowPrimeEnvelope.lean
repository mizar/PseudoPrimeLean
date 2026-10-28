/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointLowPrime
public import PseudoPrime.PrimeTestBounds.MillerRabin.ImprovedIntervalSelection

/-! # The nine low-prime candidates and their exact public selection -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The guarded low-prime candidates combined with the existing all-input envelope.
Each constant is available only below its proved logarithmic cap. -/
noncomputable def lowPrimeEnvelope (n : ℕ) : ℝ :=
  let L := Real.log n
  let B := improvedWitnessEnvelope n
  min B <|
    min (if L ≤ 401 / 50 then 23 else B) <|
    min (if L ≤ 413 / 50 then 29 else B) <|
    min (if L ≤ 893 / 100 then 31 else B) <|
    min (if L ≤ 933 / 100 then 37 else B) <|
    min (if L ≤ 238 / 25 then 41 else B) <|
    min (if L ≤ 989 / 100 then 43 else B) <|
    min (if L ≤ 521 / 50 then 47 else B) <|
    min (if L ≤ 109 / 10 then 53 else B) (if L ≤ 553 / 50 then 59 else B)

/-- The ascending low-prime interval selection; small inputs keep the two/three split. -/
noncomputable def lowPrimeSelected (n : ℕ) : ℝ :=
  let L := Real.log n
  if n < 3000 then smallIntervalBound n
  else
    if L ≤ 401 / 50 then 23
    else
      if L ≤ 413 / 50 then 29
      else
        if L ≤ 893 / 100 then 31
        else
          if L ≤ 933 / 100 then 37
          else
            if L ≤ 238 / 25 then 41
            else
              if L ≤ 989 / 100 then 43
              else
                if L ≤ 521 / 50 then 47
                else
                  if L ≤ 109 / 10 then 53
                  else if L ≤ 553 / 50 then 59 else improvedSelectedEnvelope n

/-- For every natural input, the guarded minimum is no larger than its base. -/
theorem lowPrimeEnvelope_le_improved (n : ℕ) : lowPrimeEnvelope n ≤ improvedWitnessEnvelope n := by
  exact min_le_left _ _

/-- All nine effective candidates share a single projection theorem. -/
theorem lowPrime_le_profile (f : LLS.PaperStatements.LowPrimeProfile) {n : ℕ}
    (hL : Real.log n ≤ f.logCap) : lowPrimeEnvelope n ≤ f.bound := by
  cases f
  · norm_num only [LLS.PaperStatements.LowPrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] at hL
    norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
    have h :
      lowPrimeEnvelope n ≤ (if Real.log n ≤ 401 / 50 then 23 else improvedWitnessEnvelope n) := by
      exact (min_le_right _ _).trans (min_le_left _ _)
    simpa only [ite_eq_left hL] using h
  · norm_num only [LLS.PaperStatements.LowPrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] at hL
    norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
    have h :
      lowPrimeEnvelope n ≤ (if Real.log n ≤ 413 / 50 then 29 else improvedWitnessEnvelope n) := by
      exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    simpa only [ite_eq_left hL] using h
  · norm_num only [LLS.PaperStatements.LowPrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] at hL
    norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
    have h :
      lowPrimeEnvelope n ≤ (if Real.log n ≤ 893 / 100 then 31 else improvedWitnessEnvelope n) := by
      exact
        (min_le_right _ _).trans
          ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    simpa only [ite_eq_left hL] using h
  · norm_num only [LLS.PaperStatements.LowPrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] at hL
    norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
    have h :
      lowPrimeEnvelope n ≤ (if Real.log n ≤ 933 / 100 then 37 else improvedWitnessEnvelope n) := by
      exact
        (min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    simpa only [ite_eq_left hL] using h
  · norm_num only [LLS.PaperStatements.LowPrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] at hL
    norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
    have h :
      lowPrimeEnvelope n ≤ (if Real.log n ≤ 238 / 25 then 41 else improvedWitnessEnvelope n) := by
      exact
        (min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans
              ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
    simpa only [ite_eq_left hL] using h
  · norm_num only [LLS.PaperStatements.LowPrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] at hL
    norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
    have h :
      lowPrimeEnvelope n ≤ (if Real.log n ≤ 989 / 100 then 43 else improvedWitnessEnvelope n) := by
      exact
        (min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans
              ((min_le_right _ _).trans
                ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))))
    simpa only [ite_eq_left hL] using h
  · norm_num only [LLS.PaperStatements.LowPrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] at hL
    norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
    have h :
      lowPrimeEnvelope n ≤ (if Real.log n ≤ 521 / 50 then 47 else improvedWitnessEnvelope n) := by
      exact
        (min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans
              ((min_le_right _ _).trans
                ((min_le_right _ _).trans
                  ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))))
    simpa only [ite_eq_left hL] using h
  · norm_num only [LLS.PaperStatements.LowPrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] at hL
    norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
    have h :
      lowPrimeEnvelope n ≤ (if Real.log n ≤ 109 / 10 then 53 else improvedWitnessEnvelope n) := by
      exact
        (min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans
              ((min_le_right _ _).trans
                ((min_le_right _ _).trans
                  ((min_le_right _ _).trans
                    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))))))
    simpa only [ite_eq_left hL] using h
  · norm_num only [LLS.PaperStatements.LowPrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] at hL
    norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
    have h :
      lowPrimeEnvelope n ≤ (if Real.log n ≤ 553 / 50 then 59 else improvedWitnessEnvelope n) := by
      exact
        (min_le_right _ _).trans
          ((min_le_right _ _).trans
            ((min_le_right _ _).trans
              ((min_le_right _ _).trans
                ((min_le_right _ _).trans
                  ((min_le_right _ _).trans
                    ((min_le_right _ _).trans
                      ((min_le_right _ _).trans ((min_le_right _ _).trans (le_refl _)))))))))
    simpa only [ite_eq_left hL] using h

/-- Under GRH, every odd composite n>1 has a least rejecting prime within the low envelope.
Transfer each valid candidate to one fixed least prime before taking their minimum. -/
theorem exists_least_lowPrimeEnvelope {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ lowPrimeEnvelope n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_improvedWitness hn ho hc hGRH
  have transfer {C : ℝ}
    (h : ∃ q : ℕ, q.Prime ∧ (q : ℝ) ≤ C ∧ ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n)) :
    (p : ℝ) ≤ C := by
    obtain ⟨q, hq, hqb, hqr⟩ := h
    exact (Nat.cast_le.mpr (hm q hq hqr)).trans hqb
  have h23 : (p : ℝ) ≤ (if Real.log n ≤ 401 / 50 then 23 else improvedWitnessEnvelope n) := by
    by_cases h : Real.log n ≤ 401 / 50
    · rw [ite_eq_left h]
      exact transfer (exists_prime_endpoint23 hn ho hc hGRH h)
    · rw [ite_eq_right h]
      exact hb
  have h29 : (p : ℝ) ≤ (if Real.log n ≤ 413 / 50 then 29 else improvedWitnessEnvelope n) := by
    by_cases h : Real.log n ≤ 413 / 50
    · rw [ite_eq_left h]
      exact transfer (exists_prime_endpoint29 hn ho hc hGRH h)
    · rw [ite_eq_right h]
      exact hb
  have h31 : (p : ℝ) ≤ (if Real.log n ≤ 893 / 100 then 31 else improvedWitnessEnvelope n) := by
    by_cases h : Real.log n ≤ 893 / 100
    · rw [ite_eq_left h]
      exact transfer (exists_prime_endpoint31 hn ho hc hGRH h)
    · rw [ite_eq_right h]
      exact hb
  have h37 : (p : ℝ) ≤ (if Real.log n ≤ 933 / 100 then 37 else improvedWitnessEnvelope n) := by
    by_cases h : Real.log n ≤ 933 / 100
    · rw [ite_eq_left h]
      exact transfer (exists_prime_endpoint37 hn ho hc hGRH h)
    · rw [ite_eq_right h]
      exact hb
  have h41 : (p : ℝ) ≤ (if Real.log n ≤ 238 / 25 then 41 else improvedWitnessEnvelope n) := by
    by_cases h : Real.log n ≤ 238 / 25
    · rw [ite_eq_left h]
      exact transfer (exists_prime_endpoint41 hn ho hc hGRH h)
    · rw [ite_eq_right h]
      exact hb
  have h43 : (p : ℝ) ≤ (if Real.log n ≤ 989 / 100 then 43 else improvedWitnessEnvelope n) := by
    by_cases h : Real.log n ≤ 989 / 100
    · rw [ite_eq_left h]
      exact transfer (exists_prime_endpoint43 hn ho hc hGRH h)
    · rw [ite_eq_right h]
      exact hb
  have h47 : (p : ℝ) ≤ (if Real.log n ≤ 521 / 50 then 47 else improvedWitnessEnvelope n) := by
    by_cases h : Real.log n ≤ 521 / 50
    · rw [ite_eq_left h]
      exact transfer (exists_prime_endpoint47 hn ho hc hGRH h)
    · rw [ite_eq_right h]
      exact hb
  have h53 : (p : ℝ) ≤ (if Real.log n ≤ 109 / 10 then 53 else improvedWitnessEnvelope n) := by
    by_cases h : Real.log n ≤ 109 / 10
    · rw [ite_eq_left h]
      exact transfer (exists_prime_endpoint53 hn ho hc hGRH h)
    · rw [ite_eq_right h]
      exact hb
  have h59 : (p : ℝ) ≤ (if Real.log n ≤ 553 / 50 then 59 else improvedWitnessEnvelope n) := by
    by_cases h : Real.log n ≤ 553 / 50
    · rw [ite_eq_left h]
      exact transfer (exists_prime_endpoint59 hn ho hc hGRH h)
    · rw [ite_eq_right h]
      exact hb
  exact
    ⟨p, hp, hr,
      le_min hb
        (le_min h23
          (le_min h29
            (le_min h31 (le_min h37 (le_min h41 (le_min h43 (le_min h47 (le_min h53 h59)))))))),
      hm⟩

/-- If the base already lies below 23, all guarded low candidates preserve it. -/
theorem lowPrime_eq_base {n : ℕ} (hB : improvedWitnessEnvelope n ≤ 23) :
    lowPrimeEnvelope n = improvedWitnessEnvelope n := by
  classical
  apply le_antisymm (lowPrimeEnvelope_le_improved n)
  have hf (b : ℝ) (hb : 23 ≤ b) (P : Prop) :
    improvedWitnessEnvelope n ≤ (if P then b else improvedWitnessEnvelope n) := by
    by_cases h : P
    · rw [ite_eq_left h]
      exact hB.trans hb
    · rw [ite_eq_right h]
  exact
    le_min (le_refl _)
      (le_min (hf 23 (by norm_num only) _)
        (le_min (hf 29 (by norm_num only) _)
          (le_min (hf 31 (by norm_num only) _)
            (le_min (hf 37 (by norm_num only) _)
              (le_min (hf 41 (by norm_num only) _)
                (le_min (hf 43 (by norm_num only) _)
                  (le_min (hf 47 (by norm_num only) _)
                    (le_min (hf 53 (by norm_num only) _) (hf 59 (by norm_num only) _)))))))))

/-- The selected piecewise value equals the guarded minimum for every input n>1. -/
theorem lowPrime_eq_selected {n : ℕ} (hn : 1 < n) : lowPrimeEnvelope n = lowPrimeSelected n := by
  by_cases hN : n < 3000
  · have hb : improvedWitnessEnvelope n ≤ 23 := by
      rw [improved_eq_small hn hN]
      dsimp only [smallIntervalBound]
      split_ifs <;> norm_num only
    rw [lowPrime_eq_base hb, improved_eq_small hn hN]
    exact (ite_eq_left hN).symm
  · by_cases htop : Real.log n ≤ 553 / 50
    · have hbase :=
        improved_eq_fixed61 (le_of_not_gt hN) (by linarith only [htop] : Real.log n ≤ 2877 / 250)
      by_cases h23 : Real.log n ≤ 401 / 50
      · have h29t : Real.log n ≤ 413 / 50 := by linarith only [h23]
        have h31t : Real.log n ≤ 893 / 100 := by linarith only [h23]
        have h37t : Real.log n ≤ 933 / 100 := by linarith only [h23]
        have h41t : Real.log n ≤ 238 / 25 := by linarith only [h23]
        have h43t : Real.log n ≤ 989 / 100 := by linarith only [h23]
        have h47t : Real.log n ≤ 521 / 50 := by linarith only [h23]
        have h53t : Real.log n ≤ 109 / 10 := by linarith only [h23]
        have h59t : Real.log n ≤ 553 / 50 := by linarith only [h23]
        simp only [lowPrimeEnvelope, lowPrimeSelected, ite_eq_right hN, hbase, ite_eq_left h23,
          ite_eq_left h29t, ite_eq_left h31t, ite_eq_left h37t, ite_eq_left h41t, ite_eq_left h43t,
          ite_eq_left h47t, ite_eq_left h53t, ite_eq_left h59t]
        norm_num only [min_def, ite_true, ite_false]
      · by_cases h29 : Real.log n ≤ 413 / 50
        · have h31t : Real.log n ≤ 893 / 100 := by linarith only [h29]
          have h37t : Real.log n ≤ 933 / 100 := by linarith only [h29]
          have h41t : Real.log n ≤ 238 / 25 := by linarith only [h29]
          have h43t : Real.log n ≤ 989 / 100 := by linarith only [h29]
          have h47t : Real.log n ≤ 521 / 50 := by linarith only [h29]
          have h53t : Real.log n ≤ 109 / 10 := by linarith only [h29]
          have h59t : Real.log n ≤ 553 / 50 := by linarith only [h29]
          simp only [lowPrimeEnvelope, lowPrimeSelected, ite_eq_right hN, hbase, ite_eq_right h23,
            ite_eq_left h29, ite_eq_left h31t, ite_eq_left h37t, ite_eq_left h41t, ite_eq_left h43t,
            ite_eq_left h47t, ite_eq_left h53t, ite_eq_left h59t]
          norm_num only [min_def, ite_true, ite_false]
        · by_cases h31 : Real.log n ≤ 893 / 100
          · have h37t : Real.log n ≤ 933 / 100 := by linarith only [h31]
            have h41t : Real.log n ≤ 238 / 25 := by linarith only [h31]
            have h43t : Real.log n ≤ 989 / 100 := by linarith only [h31]
            have h47t : Real.log n ≤ 521 / 50 := by linarith only [h31]
            have h53t : Real.log n ≤ 109 / 10 := by linarith only [h31]
            have h59t : Real.log n ≤ 553 / 50 := by linarith only [h31]
            simp only [lowPrimeEnvelope, lowPrimeSelected, ite_eq_right hN, hbase, ite_eq_right h23,
              ite_eq_right h29, ite_eq_left h31, ite_eq_left h37t, ite_eq_left h41t,
              ite_eq_left h43t, ite_eq_left h47t, ite_eq_left h53t, ite_eq_left h59t]
            norm_num only [min_def, ite_true, ite_false]
          · by_cases h37 : Real.log n ≤ 933 / 100
            · have h41t : Real.log n ≤ 238 / 25 := by linarith only [h37]
              have h43t : Real.log n ≤ 989 / 100 := by linarith only [h37]
              have h47t : Real.log n ≤ 521 / 50 := by linarith only [h37]
              have h53t : Real.log n ≤ 109 / 10 := by linarith only [h37]
              have h59t : Real.log n ≤ 553 / 50 := by linarith only [h37]
              simp only [lowPrimeEnvelope, lowPrimeSelected, ite_eq_right hN, hbase,
                ite_eq_right h23, ite_eq_right h29, ite_eq_right h31, ite_eq_left h37,
                ite_eq_left h41t, ite_eq_left h43t, ite_eq_left h47t, ite_eq_left h53t,
                ite_eq_left h59t]
              norm_num only [min_def, ite_true, ite_false]
            · by_cases h41 : Real.log n ≤ 238 / 25
              · have h43t : Real.log n ≤ 989 / 100 := by linarith only [h41]
                have h47t : Real.log n ≤ 521 / 50 := by linarith only [h41]
                have h53t : Real.log n ≤ 109 / 10 := by linarith only [h41]
                have h59t : Real.log n ≤ 553 / 50 := by linarith only [h41]
                simp only [lowPrimeEnvelope, lowPrimeSelected, ite_eq_right hN, hbase,
                  ite_eq_right h23, ite_eq_right h29, ite_eq_right h31, ite_eq_right h37,
                  ite_eq_left h41, ite_eq_left h43t, ite_eq_left h47t, ite_eq_left h53t,
                  ite_eq_left h59t]
                norm_num only [min_def, ite_true, ite_false]
              · by_cases h43 : Real.log n ≤ 989 / 100
                · have h47t : Real.log n ≤ 521 / 50 := by linarith only [h43]
                  have h53t : Real.log n ≤ 109 / 10 := by linarith only [h43]
                  have h59t : Real.log n ≤ 553 / 50 := by linarith only [h43]
                  simp only [lowPrimeEnvelope, lowPrimeSelected, ite_eq_right hN, hbase,
                    ite_eq_right h23, ite_eq_right h29, ite_eq_right h31, ite_eq_right h37,
                    ite_eq_right h41, ite_eq_left h43, ite_eq_left h47t, ite_eq_left h53t,
                    ite_eq_left h59t]
                  norm_num only [min_def, ite_true, ite_false]
                · by_cases h47 : Real.log n ≤ 521 / 50
                  · have h53t : Real.log n ≤ 109 / 10 := by linarith only [h47]
                    have h59t : Real.log n ≤ 553 / 50 := by linarith only [h47]
                    simp only [lowPrimeEnvelope, lowPrimeSelected, ite_eq_right hN, hbase,
                      ite_eq_right h23, ite_eq_right h29, ite_eq_right h31, ite_eq_right h37,
                      ite_eq_right h41, ite_eq_right h43, ite_eq_left h47, ite_eq_left h53t,
                      ite_eq_left h59t]
                    norm_num only [min_def, ite_true, ite_false]
                  · by_cases h53 : Real.log n ≤ 109 / 10
                    · have h59t : Real.log n ≤ 553 / 50 := by linarith only [h53]
                      simp only [lowPrimeEnvelope, lowPrimeSelected, ite_eq_right hN, hbase,
                        ite_eq_right h23, ite_eq_right h29, ite_eq_right h31, ite_eq_right h37,
                        ite_eq_right h41, ite_eq_right h43, ite_eq_right h47, ite_eq_left h53,
                        ite_eq_left h59t]
                      norm_num only [min_def, ite_true, ite_false]
                    · have h59 := htop
                      simp only [lowPrimeEnvelope, lowPrimeSelected, ite_eq_right hN, hbase,
                        ite_eq_right h23, ite_eq_right h29, ite_eq_right h31, ite_eq_right h37,
                        ite_eq_right h41, ite_eq_right h43, ite_eq_right h47, ite_eq_right h53,
                        ite_eq_left h59]
                      norm_num only [min_def, ite_true, ite_false]
    · have h23 : ¬Real.log n ≤ 401 / 50 := by
        intro h
        exact htop (by linarith only [h])
      have h29 : ¬Real.log n ≤ 413 / 50 := by
        intro h
        exact htop (by linarith only [h])
      have h31 : ¬Real.log n ≤ 893 / 100 := by
        intro h
        exact htop (by linarith only [h])
      have h37 : ¬Real.log n ≤ 933 / 100 := by
        intro h
        exact htop (by linarith only [h])
      have h41 : ¬Real.log n ≤ 238 / 25 := by
        intro h
        exact htop (by linarith only [h])
      have h43 : ¬Real.log n ≤ 989 / 100 := by
        intro h
        exact htop (by linarith only [h])
      have h47 : ¬Real.log n ≤ 521 / 50 := by
        intro h
        exact htop (by linarith only [h])
      have h53 : ¬Real.log n ≤ 109 / 10 := by
        intro h
        exact htop (by linarith only [h])
      simp only [lowPrimeEnvelope, lowPrimeSelected, ite_eq_right hN, ite_eq_right h23,
        ite_eq_right h29, ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_right h43,
        ite_eq_right h47, ite_eq_right h53, ite_eq_right htop, min_self]
      exact improved_eq_selected hn

/-- Below its logarithmic cap, the low envelope is at most 23. -/
theorem lowPrime_le_fixed23 {n : ℕ} (hL : Real.log n ≤ 401 / 50) : lowPrimeEnvelope n ≤ 23 := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    lowPrime_le_profile .p23
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] using
          hL)

/-- Below its logarithmic cap, the low envelope is at most 29. -/
theorem lowPrime_le_fixed29 {n : ℕ} (hL : Real.log n ≤ 413 / 50) : lowPrimeEnvelope n ≤ 29 := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    lowPrime_le_profile .p29
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] using
          hL)

/-- Below its logarithmic cap, the low envelope is at most 31. -/
theorem lowPrime_le_fixed31 {n : ℕ} (hL : Real.log n ≤ 893 / 100) : lowPrimeEnvelope n ≤ 31 := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    lowPrime_le_profile .p31
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] using
          hL)

/-- Below its logarithmic cap, the low envelope is at most 37. -/
theorem lowPrime_le_fixed37 {n : ℕ} (hL : Real.log n ≤ 933 / 100) : lowPrimeEnvelope n ≤ 37 := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    lowPrime_le_profile .p37
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] using
          hL)

/-- Below its logarithmic cap, the low envelope is at most 41. -/
theorem lowPrime_le_fixed41 {n : ℕ} (hL : Real.log n ≤ 238 / 25) : lowPrimeEnvelope n ≤ 41 := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    lowPrime_le_profile .p41
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] using
          hL)

/-- Below its logarithmic cap, the low envelope is at most 43. -/
theorem lowPrime_le_fixed43 {n : ℕ} (hL : Real.log n ≤ 989 / 100) : lowPrimeEnvelope n ≤ 43 := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    lowPrime_le_profile .p43
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] using
          hL)

/-- Below its logarithmic cap, the low envelope is at most 47. -/
theorem lowPrime_le_fixed47 {n : ℕ} (hL : Real.log n ≤ 521 / 50) : lowPrimeEnvelope n ≤ 47 := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    lowPrime_le_profile .p47
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] using
          hL)

/-- Below its logarithmic cap, the low envelope is at most 53. -/
theorem lowPrime_le_fixed53 {n : ℕ} (hL : Real.log n ≤ 109 / 10) : lowPrimeEnvelope n ≤ 53 := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    lowPrime_le_profile .p53
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] using
          hL)

/-- Below its logarithmic cap, the low envelope is at most 59. -/
theorem lowPrime_le_fixed59 {n : ℕ} (hL : Real.log n ≤ 553 / 50) : lowPrimeEnvelope n ≤ 59 := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    lowPrime_le_profile .p59
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] using
          hL)

/-- Every odd composite n>1 under GRH has an actual witness within the low envelope. -/
theorem exists_prime_lowPrimeEnvelope {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧ (p : ℝ) ≤ lowPrimeEnvelope n ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hr, hb, _⟩ := exists_least_lowPrimeEnvelope hn ho hc hGRH
  exact ⟨p, hp, hb, hr⟩

/-- From n>=3000 through log n=11.06 the nine-step envelope strictly improves its base.
The new value is at most 59 while the existing selected value is 61. -/
theorem lowPrimeEnvelope_lt_improved {n : ℕ} (hN : 3000 ≤ n) (hL : Real.log n ≤ 553 / 50) :
    lowPrimeEnvelope n < improvedWitnessEnvelope n := by
  rw [improved_eq_fixed61 hN (by linarith only [hL])]
  exact (lowPrime_le_fixed59 hL).trans_lt (by norm_num only)

/-- The selected low-prime interval function bounds an actual prime MR witness under GRH. -/
theorem exists_prime_lowPrimeSelected {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧ (p : ℝ) ≤ lowPrimeSelected n ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  rw [← lowPrime_eq_selected hn]
  exact exists_prime_lowPrimeEnvelope hn ho hc hGRH

/-- The selected low-prime interval function also bounds the least rejecting prime. -/
theorem exists_least_lowPrimeSelected {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ lowPrimeSelected n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  rw [← lowPrime_eq_selected hn]
  exact exists_least_lowPrimeEnvelope hn ho hc hGRH

/-- Throughout the full low-prime range the candidate minimum strictly improves its base. -/
theorem lowPrime_lt_improved {n : ℕ} (hN : 3000 ≤ n) (hU : Real.log n ≤ 553 / 50) :
    lowPrimeEnvelope n < improvedWitnessEnvelope n := by exact lowPrimeEnvelope_lt_improved hN hU

/-- The explicit low-prime selection strictly improves the previous selected function. -/
theorem lowPrimeSelected_lt_improvedSelected {n : ℕ} (hN : 3000 ≤ n) (hU : Real.log n ≤ 553 / 50) :
    lowPrimeSelected n < improvedSelectedEnvelope n := by
  have hn : 1 < n := lt_of_lt_of_le (by norm_num only : 1 < 3000) hN
  rw [← lowPrime_eq_selected hn, ← improved_eq_selected hn]
  exact lowPrimeEnvelope_lt_improved hN hU

end PseudoPrime.PrimeTestBounds.MillerRabin

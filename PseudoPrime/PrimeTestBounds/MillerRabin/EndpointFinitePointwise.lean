/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointFiniteEnvelope

/-! # Monotone pointwise normal form of the thirteen finite principal guards -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The thirteen finite-principal upper guards, with the pointwise cutoff as the base. -/
noncomputable def lowFinitePointwise (L : ℝ) : ℝ :=
  min (LLS.PaperStatements.pointwiseCutoff L)
    (allFiniteProfiles.inf' ⟨_, mem_allFiniteProfiles .p23⟩ fun f ↦
      LLS.PaperStatements.upperGuardPointwise f.logCap f.bound L)

/-- The pointwise normal form increases on all real logarithmic levels. -/
theorem lowFinitePointwise_mono : Monotone lowFinitePointwise := by
  intro L K hLK
  have hp := LLS.PaperStatements.pointwiseCutoff_mono hLK
  have hi :
    (allFiniteProfiles.inf' ⟨_, mem_allFiniteProfiles .p23⟩ fun f ↦
        LLS.PaperStatements.upperGuardPointwise f.logCap f.bound L) ≤
      (allFiniteProfiles.inf' ⟨_, mem_allFiniteProfiles .p23⟩ fun f ↦
        LLS.PaperStatements.upperGuardPointwise f.logCap f.bound K) := by
    apply Finset.le_inf'
    intro f hf
    exact
      (Finset.inf'_le _ hf).trans
        (LLS.PaperStatements.upperGuardPointwise_mono f.logCap f.bound hLK)
  exact le_min ((min_le_left _ _).trans hp) ((min_le_right _ _).trans hi)

/-- A common lower bound of the pointwise base and valid fixed guards bounds their minimum. -/
theorem lowFinitePointwise_lower {L C : ℝ} (hP : C ≤ LLS.PaperStatements.pointwiseCutoff L)
    (hF : ∀ f : Analysis.FinitePrimeProfile, L ≤ f.logCap → C ≤ f.bound) :
    C ≤ lowFinitePointwise L := by
  apply le_min hP
  apply Finset.le_inf'
  intro f _
  dsimp only [LLS.PaperStatements.upperGuardPointwise]
  split_ifs with h
  · exact le_min (hF f h) hP
  · exact hP

/-- The pointwise normal form is at least 23 at every real level. -/
theorem lowFinitePointwise_floor23 (L : ℝ) : (23 : ℝ) ≤ lowFinitePointwise L := by
  apply lowFinitePointwise_lower
  · have hs := (LLS.PaperStatements.pointwiseRadius_spec L).1
    dsimp only [LLS.PaperStatements.pointwiseCutoff]
    nlinarith only [hs]
  · intro f _
    cases f <;> norm_num only [Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat]

/-- The pointwise normal form is bounded by its base. -/
theorem lowFinitePointwise_le_base (L : ℝ) :
    lowFinitePointwise L ≤ LLS.PaperStatements.pointwiseCutoff L := by exact min_le_left _ _

/-- Each valid finite-principal guard bounds the pointwise normal form. -/
theorem lowFinitePointwise_le_profile (f : Analysis.FinitePrimeProfile) {L : ℝ}
    (hL : L ≤ f.logCap) : lowFinitePointwise L ≤ f.bound := by
  have hi :=
    Finset.inf'_le
      (fun f : Analysis.FinitePrimeProfile ↦
        LLS.PaperStatements.upperGuardPointwise f.logCap f.bound L)
      (mem_allFiniteProfiles f)
  have hf : LLS.PaperStatements.upperGuardPointwise f.logCap f.bound L ≤ f.bound := by
    rw [LLS.PaperStatements.upperGuardPointwise, ite_eq_left hL]
    exact min_le_left _ _
  exact (min_le_right _ _).trans (hi.trans hf)

/-- Above the final upper cap, all thirteen guards return the pointwise base. -/
theorem lowFinitePointwise_eq_pointwise {L : ℝ} (hL : 12373 / 1000 < L) :
    lowFinitePointwise L = LLS.PaperStatements.pointwiseCutoff L := by
  apply le_antisymm (lowFinitePointwise_le_base L)
  apply lowFinitePointwise_lower le_rfl
  intro f hf
  cases f <;>
    norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] at hf <;>
    linarith only [hL, hf]

/-- The pointwise base reaches every fixed cutoff after the preceding strengthened cap. -/
theorem lowFinitePointwise_base_lower (f : Analysis.FinitePrimeProfile) {L : ℝ}
    (hL : (lowFinitePreviousCap f : ℝ) < L) :
    (f.bound : ℝ) ≤ LLS.PaperStatements.pointwiseCutoff L := by
  have h64 : (64 : ℝ) ≤ LLS.PaperStatements.pointwiseCutoff L := by
    have hs := (LLS.PaperStatements.pointwiseRadius_spec L).1
    dsimp only [LLS.PaperStatements.pointwiseCutoff]
    nlinarith only [hs]
  cases f
  · norm_num only [Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat]
    linarith only [h64]
  · norm_num only [Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat]
    linarith only [h64]
  · norm_num only [Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat]
    linarith only [h64]
  · norm_num only [Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat]
    linarith only [h64]
  · norm_num only [Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat]
    linarith only [h64]
  · norm_num only [Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat]
    linarith only [h64]
  · norm_num only [Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat]
    linarith only [h64]
  · norm_num only [Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat]
    linarith only [h64]
  · norm_num only [Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat]
    linarith only [h64]
  · norm_num only [Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat]
    linarith only [h64]
  · have hp :=
      (LLS.PaperStatements.finiteRound_pointwise_lower .p61 (L := L)
          (by
            norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat] at hL
            norm_num only [LLS.PaperStatements.FiniteRoundCell.left, Rat.cast_div, Rat.cast_ofNat]
            linarith only [hL])).le
    simpa only [LLS.PaperStatements.FiniteRoundCell.profile, Analysis.FinitePrimeProfile.nextPrime,
      Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using hp
  · have hp :=
      (LLS.PaperStatements.finiteRound_pointwise_lower .p67 (L := L)
          (by
            norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat] at hL
            norm_num only [LLS.PaperStatements.FiniteRoundCell.left, Rat.cast_div, Rat.cast_ofNat]
            linarith only [hL])).le
    simpa only [LLS.PaperStatements.FiniteRoundCell.profile, Analysis.FinitePrimeProfile.nextPrime,
      Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using hp
  · have hp :=
      (LLS.PaperStatements.finiteRound_pointwise_lower .p71 (L := L)
          (by
            norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat] at hL
            norm_num only [LLS.PaperStatements.FiniteRoundCell.left, Rat.cast_div, Rat.cast_ofNat]
            linarith only [hL])).le
    simpa only [LLS.PaperStatements.FiniteRoundCell.profile, Analysis.FinitePrimeProfile.nextPrime,
      Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using hp

/-- The increasing fixed bounds respect the ordering of the strengthened caps. -/
theorem lowFinitePointwise_bounds_order (f g : Analysis.FinitePrimeProfile) {L : ℝ}
    (hL : (lowFinitePreviousCap f : ℝ) < L) (hG : L ≤ g.logCap) : (f.bound : ℝ) ≤ g.bound := by
  cases f <;> cases g <;>
    norm_num only [lowFinitePreviousCap, Analysis.FinitePrimeProfile.logCap,
      Analysis.FinitePrimeProfile.bound, Rat.cast_div, Rat.cast_ofNat,
      Nat.cast_ofNat] at hL hG ⊢ <;>
    linarith only [hL, hG]

/-- Each new fixed-prime interval is also exact for the pointwise normal form. -/
theorem lowFinitePointwise_eq_profile (f : Analysis.FinitePrimeProfile) {L : ℝ}
    (hL : (lowFinitePreviousCap f : ℝ) < L) (hU : L ≤ f.logCap) :
    lowFinitePointwise L = f.bound := by
  apply le_antisymm (lowFinitePointwise_le_profile f hU)
  exact
    lowFinitePointwise_lower (lowFinitePointwise_base_lower f hL)
      (fun g hG ↦ lowFinitePointwise_bounds_order f g hL hG)

/-- Up to the last finite cap, the exact selected value equals the pointwise normal form. -/
theorem lowFinitePointwise_eq_selected {n : ℕ} (hn : 1 < n) (hN : 3000 ≤ n)
    (hU : Real.log n ≤ 12373 / 1000) : lowFinitePointwise (Real.log n) = lowFiniteSelected n := by
  have hsmall : ¬n < 3000 := not_lt.mpr hN
  by_cases h23 : Real.log n ≤ 8087 / 1000
  · have he :=
      lowFinitePointwise_eq_profile .p23 (L := Real.log n)
        (by
          norm_num only [lowFinitePreviousCap, Rat.cast_zero]
          exact Real.log_pos (by exact_mod_cast hn))
        (by
          norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h23])
    simpa only [lowFiniteSelected, ite_eq_right hsmall, ite_eq_left h23,
      Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h29 : Real.log n ≤ 8325 / 1000
  · have he :=
      lowFinitePointwise_eq_profile .p29 (L := Real.log n)
        (by
          norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h23])
        (by
          norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h29])
    simpa only [lowFiniteSelected, ite_eq_right hsmall, ite_eq_right h23, ite_eq_left h29,
      Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h31 : Real.log n ≤ 8987 / 1000
  · have he :=
      lowFinitePointwise_eq_profile .p31 (L := Real.log n)
        (by
          norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h29])
        (by
          norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h31])
    simpa only [lowFiniteSelected, ite_eq_right hsmall, ite_eq_right h23, ite_eq_right h29,
      ite_eq_left h31, Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h37 : Real.log n ≤ 9390 / 1000
  · have he :=
      lowFinitePointwise_eq_profile .p37 (L := Real.log n)
        (by
          norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h31])
        (by
          norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h37])
    simpa only [lowFiniteSelected, ite_eq_right hsmall, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_left h37, Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h41 : Real.log n ≤ 9583 / 1000
  · have he :=
      lowFinitePointwise_eq_profile .p41 (L := Real.log n)
        (by
          norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h37])
        (by
          norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h41])
    simpa only [lowFiniteSelected, ite_eq_right hsmall, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_left h41, Analysis.FinitePrimeProfile.bound,
      Nat.cast_ofNat] using he
  by_cases h43 : Real.log n ≤ 9952 / 1000
  · have he :=
      lowFinitePointwise_eq_profile .p43 (L := Real.log n)
        (by
          norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h41])
        (by
          norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h43])
    simpa only [lowFiniteSelected, ite_eq_right hsmall, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_left h43,
      Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h47 : Real.log n ≤ 10471 / 1000
  · have he :=
      lowFinitePointwise_eq_profile .p47 (L := Real.log n)
        (by
          norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h43])
        (by
          norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h47])
    simpa only [lowFiniteSelected, ite_eq_right hsmall, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_right h43, ite_eq_left h47,
      Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h53 : Real.log n ≤ 10955 / 1000
  · have he :=
      lowFinitePointwise_eq_profile .p53 (L := Real.log n)
        (by
          norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h47])
        (by
          norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h53])
    simpa only [lowFiniteSelected, ite_eq_right hsmall, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_right h43, ite_eq_right h47,
      ite_eq_left h53, Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h59 : Real.log n ≤ 11109 / 1000
  · have he :=
      lowFinitePointwise_eq_profile .p59 (L := Real.log n)
        (by
          norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h53])
        (by
          norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h59])
    simpa only [lowFiniteSelected, ite_eq_right hsmall, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_right h43, ite_eq_right h47,
      ite_eq_right h53, ite_eq_left h59, Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h61 : Real.log n ≤ 11546 / 1000
  · have he :=
      lowFinitePointwise_eq_profile .p61 (L := Real.log n)
        (by
          norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h59])
        (by
          norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h61])
    simpa only [lowFiniteSelected, ite_eq_right hsmall, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_right h43, ite_eq_right h47,
      ite_eq_right h53, ite_eq_right h59, ite_eq_left h61, Analysis.FinitePrimeProfile.bound,
      Nat.cast_ofNat] using he
  by_cases h67 : Real.log n ≤ 11830 / 1000
  · have he :=
      lowFinitePointwise_eq_profile .p67 (L := Real.log n)
        (by
          norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h61])
        (by
          norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h67])
    simpa only [lowFiniteSelected, ite_eq_right hsmall, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_right h43, ite_eq_right h47,
      ite_eq_right h53, ite_eq_right h59, ite_eq_right h61, ite_eq_left h67,
      Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h71 : Real.log n ≤ 11970 / 1000
  · have he :=
      lowFinitePointwise_eq_profile .p71 (L := Real.log n)
        (by
          norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h67])
        (by
          norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h71])
    simpa only [lowFiniteSelected, ite_eq_right hsmall, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_right h43, ite_eq_right h47,
      ite_eq_right h53, ite_eq_right h59, ite_eq_right h61, ite_eq_right h67, ite_eq_left h71,
      Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h73 : Real.log n ≤ 12373 / 1000
  · have he :=
      lowFinitePointwise_eq_profile .p73 (L := Real.log n)
        (by
          norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h71])
        (by
          norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h73])
    simpa only [lowFiniteSelected, ite_eq_right hsmall, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_right h43, ite_eq_right h47,
      ite_eq_right h53, ite_eq_right h59, ite_eq_right h61, ite_eq_right h67, ite_eq_right h71,
      ite_eq_left h73, Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  exact False.elim (h73 hU)

/-- On the thirteen fixed-prime intervals, the selected value is at most 73. -/
theorem lowFiniteSelected_le73 {n : ℕ} (hn : 1 < n) (hN : 3000 ≤ n)
    (hU : Real.log n ≤ 12373 / 1000) : lowFiniteSelected n ≤ (73 : ℝ) := by
  rw [← lowFinitePointwise_eq_selected hn hN hU]
  have hp :=
    lowFinitePointwise_le_profile .p73 (L := Real.log n)
      (by
        norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
        linarith only [hU])
  simpa only [Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using hp

end PseudoPrime.PrimeTestBounds.MillerRabin

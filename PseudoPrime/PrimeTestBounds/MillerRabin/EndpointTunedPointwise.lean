/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointTunedEnvelope

/-! # Monotone pointwise normal form of the fourteen finite principal guards -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The fourteen finite-principal upper guards, with the pointwise cutoff as the base. -/
noncomputable def tunedFinitePointwise (L : ℝ) : ℝ :=
  min (LLS.PaperStatements.pointwiseCutoff L)
    (allTunedProfiles.inf' ⟨_, mem_allTunedProfiles (.finite .p23)⟩ fun f ↦
      LLS.PaperStatements.upperGuardPointwise f.logCap f.bound L)

/-- The pointwise normal form increases on all real logarithmic levels. -/
theorem tunedFinitePointwise_mono : Monotone tunedFinitePointwise := by
  intro L K hLK
  have hp := LLS.PaperStatements.pointwiseCutoff_mono hLK
  have hi :
    (allTunedProfiles.inf' ⟨_, mem_allTunedProfiles (.finite .p23)⟩ fun f ↦
        LLS.PaperStatements.upperGuardPointwise f.logCap f.bound L) ≤
      (allTunedProfiles.inf' ⟨_, mem_allTunedProfiles (.finite .p23)⟩ fun f ↦
        LLS.PaperStatements.upperGuardPointwise f.logCap f.bound K) := by
    apply Finset.le_inf'
    intro f hf
    exact
      (Finset.inf'_le _ hf).trans
        (LLS.PaperStatements.upperGuardPointwise_mono f.logCap f.bound hLK)
  exact le_min ((min_le_left _ _).trans hp) ((min_le_right _ _).trans hi)

/-- A common lower bound of the pointwise base and valid fixed guards bounds their minimum. -/
theorem tunedFinitePointwise_lower {L C : ℝ} (hP : C ≤ LLS.PaperStatements.pointwiseCutoff L)
    (hF : ∀ f : Analysis.TunedPrimeProfile, L ≤ f.logCap → C ≤ f.bound) :
    C ≤ tunedFinitePointwise L := by
  apply le_min hP
  apply Finset.le_inf'
  intro f _
  dsimp only [LLS.PaperStatements.upperGuardPointwise]
  split_ifs with h
  · exact le_min (hF f h) hP
  · exact hP

/-- The pointwise normal form is at least 23 at every real level. -/
theorem tunedFinitePointwise_floor23 (L : ℝ) : (23 : ℝ) ≤ tunedFinitePointwise L := by
  apply tunedFinitePointwise_lower
  · have hs := (LLS.PaperStatements.pointwiseRadius_spec L).1
    dsimp only [LLS.PaperStatements.pointwiseCutoff]
    nlinarith only [hs]
  · intro f _
    cases f with
    | finite f =>
      cases f <;>
        norm_num only [Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound,
          Nat.cast_ofNat]
    | p79 => norm_num only [Analysis.TunedPrimeProfile.bound, Nat.cast_ofNat]

/-- The pointwise normal form is bounded by its base. -/
theorem tunedFinitePointwise_le_base (L : ℝ) :
    tunedFinitePointwise L ≤ LLS.PaperStatements.pointwiseCutoff L := by exact min_le_left _ _

/-- Each valid finite-principal guard bounds the pointwise normal form. -/
theorem tunedFinitePointwise_le_profile (f : Analysis.TunedPrimeProfile) {L : ℝ}
    (hL : L ≤ f.logCap) : tunedFinitePointwise L ≤ f.bound := by
  have hi :=
    Finset.inf'_le
      (fun f : Analysis.TunedPrimeProfile ↦
        LLS.PaperStatements.upperGuardPointwise f.logCap f.bound L)
      (mem_allTunedProfiles f)
  have hf : LLS.PaperStatements.upperGuardPointwise f.logCap f.bound L ≤ f.bound := by
    rw [LLS.PaperStatements.upperGuardPointwise, ite_eq_left hL]
    exact min_le_left _ _
  exact (min_le_right _ _).trans (hi.trans hf)

/-- Above the final upper cap, all fourteen guards return the pointwise base. -/
theorem tunedFinitePointwise_eq_pointwise {L : ℝ} (hL : 126409 / 10000 < L) :
    tunedFinitePointwise L = LLS.PaperStatements.pointwiseCutoff L := by
  apply le_antisymm (tunedFinitePointwise_le_base L)
  apply tunedFinitePointwise_lower le_rfl
  intro f hf
  cases f with
  | finite f =>
    cases f <;>
      norm_num only [Analysis.TunedPrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
        Rat.cast_div, Rat.cast_ofNat] at hf <;>
      linarith only [hL, hf]
  | p79 =>
    norm_num only [Analysis.TunedPrimeProfile.logCap, Analysis.prime79Cap, Rat.cast_div,
      Rat.cast_ofNat] at hf
    linarith only [hL, hf]

/-- Each newly selected fixed cutoff is below the pointwise base after the previous tuned cap. -/
theorem tunedFinitePointwise_base_lower (f : Analysis.TunedPrimeProfile) {L : ℝ}
    (hL : (f.previousCap : ℝ) < L) : (f.bound : ℝ) ≤ LLS.PaperStatements.pointwiseCutoff L := by
  have h64 : (64 : ℝ) ≤ LLS.PaperStatements.pointwiseCutoff L := by
    have hs := (LLS.PaperStatements.pointwiseRadius_spec L).1
    dsimp only [LLS.PaperStatements.pointwiseCutoff]
    nlinarith only [hs]
  cases f with
  | finite f =>
    cases f
    · norm_num only [Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound,
        Nat.cast_ofNat]
      linarith only [h64]
    · norm_num only [Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound,
        Nat.cast_ofNat]
      linarith only [h64]
    · norm_num only [Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound,
        Nat.cast_ofNat]
      linarith only [h64]
    · norm_num only [Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound,
        Nat.cast_ofNat]
      linarith only [h64]
    · norm_num only [Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound,
        Nat.cast_ofNat]
      linarith only [h64]
    · norm_num only [Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound,
        Nat.cast_ofNat]
      linarith only [h64]
    · norm_num only [Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound,
        Nat.cast_ofNat]
      linarith only [h64]
    · norm_num only [Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound,
        Nat.cast_ofNat]
      linarith only [h64]
    · norm_num only [Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound,
        Nat.cast_ofNat]
      linarith only [h64]
    · norm_num only [Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound,
        Nat.cast_ofNat]
      linarith only [h64]
    · have hp :=
        (LLS.PaperStatements.finiteRound_pointwise_lower .p61 (L := L)
            (by
              norm_num only [Analysis.TunedPrimeProfile.previousCap,
                Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat] at hL
              norm_num only [LLS.PaperStatements.FiniteRoundCell.left, Rat.cast_div, Rat.cast_ofNat]
              linarith only [hL])).le
      simpa only [LLS.PaperStatements.FiniteRoundCell.profile,
        Analysis.FinitePrimeProfile.nextPrime, Analysis.TunedPrimeProfile.bound,
        Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using hp
    · have hp :=
        (LLS.PaperStatements.finiteRound_pointwise_lower .p67 (L := L)
            (by
              norm_num only [Analysis.TunedPrimeProfile.previousCap,
                Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat] at hL
              norm_num only [LLS.PaperStatements.FiniteRoundCell.left, Rat.cast_div, Rat.cast_ofNat]
              linarith only [hL])).le
      simpa only [LLS.PaperStatements.FiniteRoundCell.profile,
        Analysis.FinitePrimeProfile.nextPrime, Analysis.TunedPrimeProfile.bound,
        Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using hp
    · have hp :=
        (LLS.PaperStatements.finiteRound_pointwise_lower .p71 (L := L)
            (by
              norm_num only [Analysis.TunedPrimeProfile.previousCap,
                Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat] at hL
              norm_num only [LLS.PaperStatements.FiniteRoundCell.left, Rat.cast_div, Rat.cast_ofNat]
              linarith only [hL])).le
      simpa only [LLS.PaperStatements.FiniteRoundCell.profile,
        Analysis.FinitePrimeProfile.nextPrime, Analysis.TunedPrimeProfile.bound,
        Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using hp
  | p79 =>
    have hp :=
      (LLS.PaperStatements.finiteRound_pointwise_lower .p73 (L := L)
          (by
            norm_num only [Analysis.TunedPrimeProfile.previousCap,
              Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat] at hL
            norm_num only [LLS.PaperStatements.FiniteRoundCell.left, Rat.cast_div, Rat.cast_ofNat]
            linarith only [hL])).le
    simpa only [LLS.PaperStatements.FiniteRoundCell.profile, Analysis.FinitePrimeProfile.nextPrime,
      Analysis.TunedPrimeProfile.bound, Nat.cast_ofNat] using hp

/-- Every tuned interval is exact also for the fourteen-guard pointwise normal form. -/
theorem tunedFinitePointwise_eq_profile (f : Analysis.TunedPrimeProfile) {L : ℝ}
    (hL : (f.previousCap : ℝ) < L) (hU : L ≤ f.logCap) : tunedFinitePointwise L = f.bound := by
  apply le_antisymm (tunedFinitePointwise_le_profile f hU)
  exact
    tunedFinitePointwise_lower (tunedFinitePointwise_base_lower f hL)
      (fun g hG ↦ tunedFinite_bounds_order f g hL hG)

/-- On the fourteen tuned intervals, the selected value equals the pointwise normal form. -/
theorem tunedFinitePointwise_eq_selected {n : ℕ} (hn : 1 < n) (hN : 3000 ≤ n)
    (hU : Real.log n ≤ 126409 / 10000) :
    tunedFinitePointwise (Real.log n) = tunedFiniteSelected n := by
  have hsmall : ¬n < 3000 := not_lt.mpr hN
  by_cases h23 : Real.log n ≤ 80901 / 10000
  · have he :=
      tunedFinitePointwise_eq_profile (.finite .p23) (L := Real.log n)
        (by
          norm_num only [Analysis.TunedPrimeProfile.previousCap, Rat.cast_zero]
          exact Real.log_pos (by exact_mod_cast hn))
        (by
          norm_num only [Analysis.TunedPrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
            Analysis.prime79Cap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h23])
    simpa only [tunedFiniteSelected, ite_eq_right hsmall, ite_eq_left h23,
      Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h29 : Real.log n ≤ 83320 / 10000
  · have he :=
      tunedFinitePointwise_eq_profile (.finite .p29) (L := Real.log n)
        (by
          norm_num only [Analysis.TunedPrimeProfile.previousCap,
            Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h23])
        (by
          norm_num only [Analysis.TunedPrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
            Analysis.prime79Cap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h29])
    simpa only [tunedFiniteSelected, ite_eq_right hsmall, ite_eq_right h23, ite_eq_left h29,
      Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h31 : Real.log n ≤ 90031 / 10000
  · have he :=
      tunedFinitePointwise_eq_profile (.finite .p31) (L := Real.log n)
        (by
          norm_num only [Analysis.TunedPrimeProfile.previousCap,
            Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h29])
        (by
          norm_num only [Analysis.TunedPrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
            Analysis.prime79Cap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h31])
    simpa only [tunedFiniteSelected, ite_eq_right hsmall, ite_eq_right h23, ite_eq_right h29,
      ite_eq_left h31, Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound,
      Nat.cast_ofNat] using he
  by_cases h37 : Real.log n ≤ 93961 / 10000
  · have he :=
      tunedFinitePointwise_eq_profile (.finite .p37) (L := Real.log n)
        (by
          norm_num only [Analysis.TunedPrimeProfile.previousCap,
            Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h31])
        (by
          norm_num only [Analysis.TunedPrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
            Analysis.prime79Cap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h37])
    simpa only [tunedFiniteSelected, ite_eq_right hsmall, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_left h37, Analysis.TunedPrimeProfile.bound,
      Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h41 : Real.log n ≤ 95875 / 10000
  · have he :=
      tunedFinitePointwise_eq_profile (.finite .p41) (L := Real.log n)
        (by
          norm_num only [Analysis.TunedPrimeProfile.previousCap,
            Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h37])
        (by
          norm_num only [Analysis.TunedPrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
            Analysis.prime79Cap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h41])
    simpa only [tunedFiniteSelected, ite_eq_right hsmall, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_left h41, Analysis.TunedPrimeProfile.bound,
      Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h43 : Real.log n ≤ 99619 / 10000
  · have he :=
      tunedFinitePointwise_eq_profile (.finite .p43) (L := Real.log n)
        (by
          norm_num only [Analysis.TunedPrimeProfile.previousCap,
            Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h41])
        (by
          norm_num only [Analysis.TunedPrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
            Analysis.prime79Cap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h43])
    simpa only [tunedFiniteSelected, ite_eq_right hsmall, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_left h43,
      Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h47 : Real.log n ≤ 104895 / 10000
  · have he :=
      tunedFinitePointwise_eq_profile (.finite .p47) (L := Real.log n)
        (by
          norm_num only [Analysis.TunedPrimeProfile.previousCap,
            Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h43])
        (by
          norm_num only [Analysis.TunedPrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
            Analysis.prime79Cap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h47])
    simpa only [tunedFiniteSelected, ite_eq_right hsmall, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_right h43, ite_eq_left h47,
      Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h53 : Real.log n ≤ 109671 / 10000
  · have he :=
      tunedFinitePointwise_eq_profile (.finite .p53) (L := Real.log n)
        (by
          norm_num only [Analysis.TunedPrimeProfile.previousCap,
            Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h47])
        (by
          norm_num only [Analysis.TunedPrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
            Analysis.prime79Cap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h53])
    simpa only [tunedFiniteSelected, ite_eq_right hsmall, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_right h43, ite_eq_right h47,
      ite_eq_left h53, Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound,
      Nat.cast_ofNat] using he
  by_cases h59 : Real.log n ≤ 111199 / 10000
  · have he :=
      tunedFinitePointwise_eq_profile (.finite .p59) (L := Real.log n)
        (by
          norm_num only [Analysis.TunedPrimeProfile.previousCap,
            Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h53])
        (by
          norm_num only [Analysis.TunedPrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
            Analysis.prime79Cap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h59])
    simpa only [tunedFiniteSelected, ite_eq_right hsmall, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_right h43, ite_eq_right h47,
      ite_eq_right h53, ite_eq_left h59, Analysis.TunedPrimeProfile.bound,
      Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h61 : Real.log n ≤ 115654 / 10000
  · have he :=
      tunedFinitePointwise_eq_profile (.finite .p61) (L := Real.log n)
        (by
          norm_num only [Analysis.TunedPrimeProfile.previousCap,
            Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h59])
        (by
          norm_num only [Analysis.TunedPrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
            Analysis.prime79Cap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h61])
    simpa only [tunedFiniteSelected, ite_eq_right hsmall, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_right h43, ite_eq_right h47,
      ite_eq_right h53, ite_eq_right h59, ite_eq_left h61, Analysis.TunedPrimeProfile.bound,
      Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h67 : Real.log n ≤ 118463 / 10000
  · have he :=
      tunedFinitePointwise_eq_profile (.finite .p67) (L := Real.log n)
        (by
          norm_num only [Analysis.TunedPrimeProfile.previousCap,
            Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h61])
        (by
          norm_num only [Analysis.TunedPrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
            Analysis.prime79Cap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h67])
    simpa only [tunedFiniteSelected, ite_eq_right hsmall, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_right h43, ite_eq_right h47,
      ite_eq_right h53, ite_eq_right h59, ite_eq_right h61, ite_eq_left h67,
      Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h71 : Real.log n ≤ 119879 / 10000
  · have he :=
      tunedFinitePointwise_eq_profile (.finite .p71) (L := Real.log n)
        (by
          norm_num only [Analysis.TunedPrimeProfile.previousCap,
            Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h67])
        (by
          norm_num only [Analysis.TunedPrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
            Analysis.prime79Cap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h71])
    simpa only [tunedFiniteSelected, ite_eq_right hsmall, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_right h43, ite_eq_right h47,
      ite_eq_right h53, ite_eq_right h59, ite_eq_right h61, ite_eq_right h67, ite_eq_left h71,
      Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h73 : Real.log n ≤ 123975 / 10000
  · have he :=
      tunedFinitePointwise_eq_profile (.finite .p73) (L := Real.log n)
        (by
          norm_num only [Analysis.TunedPrimeProfile.previousCap,
            Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h71])
        (by
          norm_num only [Analysis.TunedPrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
            Analysis.prime79Cap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h73])
    simpa only [tunedFiniteSelected, ite_eq_right hsmall, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_right h43, ite_eq_right h47,
      ite_eq_right h53, ite_eq_right h59, ite_eq_right h61, ite_eq_right h67, ite_eq_right h71,
      ite_eq_left h73, Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound,
      Nat.cast_ofNat] using he
  by_cases h79 : Real.log n ≤ 126409 / 10000
  · have he :=
      tunedFinitePointwise_eq_profile (.p79) (L := Real.log n)
        (by
          norm_num only [Analysis.TunedPrimeProfile.previousCap,
            Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h73])
        (by
          norm_num only [Analysis.TunedPrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
            Analysis.prime79Cap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h79])
    simpa only [tunedFiniteSelected, ite_eq_right hsmall, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_right h43, ite_eq_right h47,
      ite_eq_right h53, ite_eq_right h59, ite_eq_right h61, ite_eq_right h67, ite_eq_right h71,
      ite_eq_right h73, ite_eq_left h79, Analysis.TunedPrimeProfile.bound,
      Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  exact False.elim (h79 hU)

/-- The selected fixed-prime range never exceeds its final cutoff 79. -/
theorem tunedFiniteSelected_le79 {n : ℕ} (hn : 1 < n) (hN : 3000 ≤ n)
    (hU : Real.log n ≤ 126409 / 10000) : tunedFiniteSelected n ≤ (79 : ℝ) := by
  rw [← tunedFinitePointwise_eq_selected hn hN hU]
  have hp :=
    tunedFinitePointwise_le_profile .p79 (L := Real.log n)
      (by
        norm_num only [Analysis.TunedPrimeProfile.logCap, Analysis.prime79Cap, Rat.cast_div,
          Rat.cast_ofNat]
        linarith only [hU])
  simpa only [Analysis.TunedPrimeProfile.bound, Nat.cast_ofNat] using hp

/-- Every single tuned upper guard bounds the pointwise normal form, even when inactive. -/
theorem tunedFinitePointwise_le_guard (f : Analysis.TunedPrimeProfile) (L : ℝ) :
    tunedFinitePointwise L ≤ LLS.PaperStatements.upperGuardPointwise f.logCap f.bound L := by
  exact (min_le_right _ _).trans (Finset.inf'_le _ (mem_allTunedProfiles f))

/-- Extending all current finite caps and adding 79 cannot increase the pointwise normal form. -/
theorem tunedFinitePointwise_le_current (L : ℝ) :
    tunedFinitePointwise L ≤ lowFinitePointwise L := by
  apply le_min (tunedFinitePointwise_le_base L)
  apply Finset.le_inf'
  intro f _
  have hcap : (f.logCap : ℝ) ≤ f.tunedCap :=
    (Rat.cast_le (K := ℝ)).mpr (Analysis.finiteTuned_cap_extends f)
  exact
    (tunedFinitePointwise_le_guard (.finite f) L).trans
      (LLS.PaperStatements.upperGuardPointwise_antitone_cap hcap f.bound L)

end PseudoPrime.PrimeTestBounds.MillerRabin

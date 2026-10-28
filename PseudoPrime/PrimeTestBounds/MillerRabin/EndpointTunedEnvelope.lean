/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointTunedBase

/-! # Fourteen tuned fixed-prime guards and their exact interval selection -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The fourteen tuned fixed-prime profiles in increasing cap order. -/
def allTunedProfiles : Finset Analysis.TunedPrimeProfile :=
  {.finite .p23, .finite .p29, .finite .p31, .finite .p37,
    .finite .p41, .finite .p43, .finite .p47, .finite .p53, .finite .p59, .finite .p61,
    .finite .p67, .finite .p71, .finite .p73, .p79}

/-- Every tuned fixed-prime profile belongs to the finite guard set. -/
theorem mem_allTunedProfiles (f : Analysis.TunedPrimeProfile) : f ∈ allTunedProfiles := by
  cases f with
  | finite f => cases f <;> decide +kernel
  | p79 => decide +kernel

/-- Valid tuned fixed cutoffs together with the current sharp value form a finite candidate set. -/
noncomputable def tunedFiniteCandidates (n : ℕ) : Finset ℝ := by
  classical
    exact
    insert (sharpWitnessEnvelope n)
      (allTunedProfiles.image fun f ↦
        if Real.log n ≤ (f.logCap : ℝ) then (f.bound : ℝ) else sharpWitnessEnvelope n)

/-- The current sharp value always belongs to the tuned candidate set. -/
theorem tunedFinite_mem_base (n : ℕ) : sharpWitnessEnvelope n ∈ tunedFiniteCandidates n := by
  classical exact Finset.mem_insert_self _ _

/-- The tuned fourteen-profile minimum preserves the specified small-input branch. -/
noncomputable def tunedFiniteWitness (n : ℕ) : ℝ :=
  if n < 3000 then smallIntervalBound n
  else (tunedFiniteCandidates n).min' ⟨_, tunedFinite_mem_base n⟩

/-- The exact ascending-cap selection with current sharp fallback. -/
noncomputable def tunedFiniteSelected (n : ℕ) : ℝ :=
  if n < 3000 then smallIntervalBound n
  else
    if Real.log n ≤ 80901 / 10000 then 23
    else
      if Real.log n ≤ 83320 / 10000 then 29
      else
        if Real.log n ≤ 90031 / 10000 then 31
        else
          if Real.log n ≤ 93961 / 10000 then 37
          else
            if Real.log n ≤ 95875 / 10000 then 41
            else
              if Real.log n ≤ 99619 / 10000 then 43
              else
                if Real.log n ≤ 104895 / 10000 then 47
                else
                  if Real.log n ≤ 109671 / 10000 then 53
                  else
                    if Real.log n ≤ 111199 / 10000 then 59
                    else
                      if Real.log n ≤ 115654 / 10000 then 61
                      else
                        if Real.log n ≤ 118463 / 10000 then 67
                        else
                          if Real.log n ≤ 119879 / 10000 then 71
                          else
                            if Real.log n ≤ 123975 / 10000 then 73
                            else if Real.log n ≤ 126409 / 10000 then 79 else sharpSelectedEnvelope n

/-- Every input below 3000 keeps its small-interval value. -/
theorem tunedFiniteWitness_eq_small {n : ℕ} (hN : n < 3000) :
    tunedFiniteWitness n = smallIntervalBound n := by exact ite_eq_left hN

/-- The tuned guarded minimum never exceeds the current sharp value above one. -/
theorem tunedFiniteWitness_le_sharp {n : ℕ} (_hn : 1 < n) :
    tunedFiniteWitness n ≤ sharpWitnessEnvelope n := by
  classical
  by_cases hN : n < 3000
  · rw [tunedFiniteWitness_eq_small hN, sharpWitness_eq_small hN]
  · rw [tunedFiniteWitness, ite_eq_right hN]
    exact Finset.min'_le _ _ (tunedFinite_mem_base n)

/-- A common lower bound of current sharp and all valid fixed profiles bounds their minimum. -/
theorem tunedFinite_lower_of_candidates {n : ℕ} (_hn : 1 < n) {C : ℝ}
    (hB : C ≤ sharpWitnessEnvelope n)
    (hF : ∀ f : Analysis.TunedPrimeProfile, Real.log n ≤ f.logCap → C ≤ f.bound) :
    C ≤ tunedFiniteWitness n := by
  classical
  by_cases hN : n < 3000
  · rw [tunedFiniteWitness_eq_small hN]
    simpa only [sharpWitness_eq_small hN] using hB
  · rw [tunedFiniteWitness, ite_eq_right hN]
    apply Finset.le_min'
    intro v hv
    rcases Finset.mem_insert.mp hv with he | hv
    · rw [he]
      exact hB
    · obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hv
      split_ifs with h
      · exact hF f h
      · exact hB

/-- Each applicable tuned fixed profile bounds the guarded minimum. -/
theorem tunedFinite_le_profile (f : Analysis.TunedPrimeProfile) {n : ℕ}
    (hL : Real.log n ≤ f.logCap) : tunedFiniteWitness n ≤ f.bound := by
  classical
  by_cases hN : n < 3000
  · rw [tunedFiniteWitness_eq_small hN]
    dsimp only [smallIntervalBound]
    cases f with
    | finite f =>
      cases f <;> split_ifs <;>
        norm_num only [Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound,
          Nat.cast_ofNat]
    | p79 => split_ifs <;> norm_num only [Analysis.TunedPrimeProfile.bound, Nat.cast_ofNat]
  · rw [tunedFiniteWitness, ite_eq_right hN]
    have hm :
      (if Real.log n ≤ (f.logCap : ℝ) then (f.bound : ℝ) else sharpWitnessEnvelope n) ∈
        tunedFiniteCandidates n :=
      Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨f, mem_allTunedProfiles f, rfl⟩)
    simpa only [ite_eq_left hL] using Finset.min'_le _ _ hm

/-- The increasing fixed cutoffs respect the ordering of the tuned caps on real levels. -/
theorem tunedFinite_bounds_order (f g : Analysis.TunedPrimeProfile) {L : ℝ}
    (hL : (f.previousCap : ℝ) < L) (hG : L ≤ g.logCap) : (f.bound : ℝ) ≤ g.bound := by
  cases f with
  | finite f =>
    cases g with
    | finite g =>
      cases f <;> cases g <;>
        norm_num only [Analysis.TunedPrimeProfile.previousCap, Analysis.TunedPrimeProfile.logCap,
          Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.tunedCap,
          Analysis.FinitePrimeProfile.bound, Analysis.prime79Cap, Rat.cast_div, Rat.cast_ofNat,
          Rat.cast_zero, Nat.cast_ofNat] at hL hG ⊢ <;>
        linarith only [hL, hG]
    | p79 =>
      cases f <;>
        norm_num only [Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound,
          Nat.cast_ofNat]
  | p79 =>
    cases g with
    | finite g =>
      cases g <;>
        norm_num only [Analysis.TunedPrimeProfile.previousCap, Analysis.TunedPrimeProfile.logCap,
          Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.tunedCap,
          Analysis.FinitePrimeProfile.bound, Analysis.prime79Cap, Rat.cast_div, Rat.cast_ofNat,
          Rat.cast_zero, Nat.cast_ofNat] at hL hG ⊢ <;>
        linarith only [hL, hG]
    | p79 => norm_num only [Analysis.TunedPrimeProfile.bound, Nat.cast_ofNat]

/-- Each ascending tuned interval selects exactly its fixed prime cutoff. -/
theorem tunedFinite_eq_profile (f : Analysis.TunedPrimeProfile) {n : ℕ} (hn : 1 < n) (hN : 3000 ≤ n)
    (hL : (f.previousCap : ℝ) < Real.log n) (hU : Real.log n ≤ f.logCap) :
    tunedFiniteWitness n = f.bound := by
  apply le_antisymm (tunedFinite_le_profile f hU)
  exact
    tunedFinite_lower_of_candidates hn (tunedFinite_base_lower f hn hN hL hU)
      (fun g hG ↦ tunedFinite_bounds_order f g hL hG)

/-- Above the final tuned cap, all fixed guards return the current sharp value. -/
theorem tunedFinite_eq_sharp_of_log {n : ℕ} (hn : 1 < n) (hL : 126409 / 10000 < Real.log n) :
    tunedFiniteWitness n = sharpWitnessEnvelope n := by
  apply le_antisymm (tunedFiniteWitness_le_sharp hn)
  apply tunedFinite_lower_of_candidates hn le_rfl
  intro f hF
  cases f with
  | finite f =>
    cases f <;>
      norm_num only [Analysis.TunedPrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
        Rat.cast_div, Rat.cast_ofNat] at hF <;>
      linarith only [hF, hL]
  | p79 =>
    norm_num only [Analysis.TunedPrimeProfile.logCap, Analysis.prime79Cap, Rat.cast_div,
      Rat.cast_ofNat] at hF
    linarith only [hF, hL]

/-- The guarded minimum equals its fourteen explicit fixed-prime intervals above one. -/
theorem tunedFinite_eq_selected {n : ℕ} (hn : 1 < n) :
    tunedFiniteWitness n = tunedFiniteSelected n := by
  by_cases hN : n < 3000
  · rw [tunedFiniteWitness_eq_small hN]
    exact (ite_eq_left hN).symm
  have hlarge : 3000 ≤ n := le_of_not_gt hN
  by_cases h23 : Real.log n ≤ 80901 / 10000
  · have he :=
      tunedFinite_eq_profile (.finite .p23) hn hlarge
        (by
          norm_num only [Analysis.TunedPrimeProfile.previousCap, Rat.cast_zero]
          exact Real.log_pos (by exact_mod_cast hn))
        (by
          norm_num only [Analysis.TunedPrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
            Analysis.prime79Cap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h23])
    simpa only [tunedFiniteSelected, ite_eq_right hN, ite_eq_left h23,
      Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h29 : Real.log n ≤ 83320 / 10000
  · have he :=
      tunedFinite_eq_profile (.finite .p29) hn hlarge
        (by
          norm_num only [Analysis.TunedPrimeProfile.previousCap,
            Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h23])
        (by
          norm_num only [Analysis.TunedPrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
            Analysis.prime79Cap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h29])
    simpa only [tunedFiniteSelected, ite_eq_right hN, ite_eq_right h23, ite_eq_left h29,
      Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h31 : Real.log n ≤ 90031 / 10000
  · have he :=
      tunedFinite_eq_profile (.finite .p31) hn hlarge
        (by
          norm_num only [Analysis.TunedPrimeProfile.previousCap,
            Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h29])
        (by
          norm_num only [Analysis.TunedPrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
            Analysis.prime79Cap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h31])
    simpa only [tunedFiniteSelected, ite_eq_right hN, ite_eq_right h23, ite_eq_right h29,
      ite_eq_left h31, Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound,
      Nat.cast_ofNat] using he
  by_cases h37 : Real.log n ≤ 93961 / 10000
  · have he :=
      tunedFinite_eq_profile (.finite .p37) hn hlarge
        (by
          norm_num only [Analysis.TunedPrimeProfile.previousCap,
            Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h31])
        (by
          norm_num only [Analysis.TunedPrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
            Analysis.prime79Cap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h37])
    simpa only [tunedFiniteSelected, ite_eq_right hN, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_left h37, Analysis.TunedPrimeProfile.bound,
      Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h41 : Real.log n ≤ 95875 / 10000
  · have he :=
      tunedFinite_eq_profile (.finite .p41) hn hlarge
        (by
          norm_num only [Analysis.TunedPrimeProfile.previousCap,
            Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h37])
        (by
          norm_num only [Analysis.TunedPrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
            Analysis.prime79Cap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h41])
    simpa only [tunedFiniteSelected, ite_eq_right hN, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_left h41, Analysis.TunedPrimeProfile.bound,
      Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h43 : Real.log n ≤ 99619 / 10000
  · have he :=
      tunedFinite_eq_profile (.finite .p43) hn hlarge
        (by
          norm_num only [Analysis.TunedPrimeProfile.previousCap,
            Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h41])
        (by
          norm_num only [Analysis.TunedPrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
            Analysis.prime79Cap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h43])
    simpa only [tunedFiniteSelected, ite_eq_right hN, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_left h43,
      Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h47 : Real.log n ≤ 104895 / 10000
  · have he :=
      tunedFinite_eq_profile (.finite .p47) hn hlarge
        (by
          norm_num only [Analysis.TunedPrimeProfile.previousCap,
            Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h43])
        (by
          norm_num only [Analysis.TunedPrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
            Analysis.prime79Cap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h47])
    simpa only [tunedFiniteSelected, ite_eq_right hN, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_right h43, ite_eq_left h47,
      Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h53 : Real.log n ≤ 109671 / 10000
  · have he :=
      tunedFinite_eq_profile (.finite .p53) hn hlarge
        (by
          norm_num only [Analysis.TunedPrimeProfile.previousCap,
            Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h47])
        (by
          norm_num only [Analysis.TunedPrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
            Analysis.prime79Cap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h53])
    simpa only [tunedFiniteSelected, ite_eq_right hN, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_right h43, ite_eq_right h47,
      ite_eq_left h53, Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound,
      Nat.cast_ofNat] using he
  by_cases h59 : Real.log n ≤ 111199 / 10000
  · have he :=
      tunedFinite_eq_profile (.finite .p59) hn hlarge
        (by
          norm_num only [Analysis.TunedPrimeProfile.previousCap,
            Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h53])
        (by
          norm_num only [Analysis.TunedPrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
            Analysis.prime79Cap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h59])
    simpa only [tunedFiniteSelected, ite_eq_right hN, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_right h43, ite_eq_right h47,
      ite_eq_right h53, ite_eq_left h59, Analysis.TunedPrimeProfile.bound,
      Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h61 : Real.log n ≤ 115654 / 10000
  · have he :=
      tunedFinite_eq_profile (.finite .p61) hn hlarge
        (by
          norm_num only [Analysis.TunedPrimeProfile.previousCap,
            Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h59])
        (by
          norm_num only [Analysis.TunedPrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
            Analysis.prime79Cap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h61])
    simpa only [tunedFiniteSelected, ite_eq_right hN, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_right h43, ite_eq_right h47,
      ite_eq_right h53, ite_eq_right h59, ite_eq_left h61, Analysis.TunedPrimeProfile.bound,
      Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h67 : Real.log n ≤ 118463 / 10000
  · have he :=
      tunedFinite_eq_profile (.finite .p67) hn hlarge
        (by
          norm_num only [Analysis.TunedPrimeProfile.previousCap,
            Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h61])
        (by
          norm_num only [Analysis.TunedPrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
            Analysis.prime79Cap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h67])
    simpa only [tunedFiniteSelected, ite_eq_right hN, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_right h43, ite_eq_right h47,
      ite_eq_right h53, ite_eq_right h59, ite_eq_right h61, ite_eq_left h67,
      Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h71 : Real.log n ≤ 119879 / 10000
  · have he :=
      tunedFinite_eq_profile (.finite .p71) hn hlarge
        (by
          norm_num only [Analysis.TunedPrimeProfile.previousCap,
            Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h67])
        (by
          norm_num only [Analysis.TunedPrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
            Analysis.prime79Cap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h71])
    simpa only [tunedFiniteSelected, ite_eq_right hN, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_right h43, ite_eq_right h47,
      ite_eq_right h53, ite_eq_right h59, ite_eq_right h61, ite_eq_right h67, ite_eq_left h71,
      Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h73 : Real.log n ≤ 123975 / 10000
  · have he :=
      tunedFinite_eq_profile (.finite .p73) hn hlarge
        (by
          norm_num only [Analysis.TunedPrimeProfile.previousCap,
            Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h71])
        (by
          norm_num only [Analysis.TunedPrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
            Analysis.prime79Cap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h73])
    simpa only [tunedFiniteSelected, ite_eq_right hN, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_right h43, ite_eq_right h47,
      ite_eq_right h53, ite_eq_right h59, ite_eq_right h61, ite_eq_right h67, ite_eq_right h71,
      ite_eq_left h73, Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound,
      Nat.cast_ofNat] using he
  by_cases h79 : Real.log n ≤ 126409 / 10000
  · have he :=
      tunedFinite_eq_profile (.p79) hn hlarge
        (by
          norm_num only [Analysis.TunedPrimeProfile.previousCap,
            Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h73])
        (by
          norm_num only [Analysis.TunedPrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
            Analysis.prime79Cap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h79])
    simpa only [tunedFiniteSelected, ite_eq_right hN, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_right h43, ite_eq_right h47,
      ite_eq_right h53, ite_eq_right h59, ite_eq_right h61, ite_eq_right h67, ite_eq_right h71,
      ite_eq_right h73, ite_eq_left h79, Analysis.TunedPrimeProfile.bound,
      Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  rw [tunedFinite_eq_sharp_of_log hn (lt_of_not_ge h79), sharp_eq_selected hn]
  simp only [tunedFiniteSelected, ite_eq_right hN, ite_eq_right h23, ite_eq_right h29,
    ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_right h43, ite_eq_right h47,
    ite_eq_right h53, ite_eq_right h59, ite_eq_right h61, ite_eq_right h67, ite_eq_right h71,
    ite_eq_right h73, ite_eq_right h79]

/-- A current least rejecting prime lies below every valid tuned profile and their minimum. -/
theorem exists_least_tunedFiniteWitness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ tunedFiniteWitness n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_sharpEnvelope hn ho hc hGRH
  have transfer (f : Analysis.TunedPrimeProfile) (hL : Real.log n ≤ f.logCap) :
    (p : ℝ) ≤ f.bound := by
    obtain ⟨q, hq, hqb, hqr⟩ := exists_prime_tunedProfile f hn ho hc hGRH hL
    exact (Nat.cast_le.mpr (hm q hq hqr)).trans hqb
  exact ⟨p, hp, hr, tunedFinite_lower_of_candidates hn hb transfer, hm⟩

/-- Forget leastness to obtain an actual rejecting prime below the tuned finite minimum. -/
theorem exists_prime_tunedFiniteWitness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ tunedFiniteWitness n ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hr, hb, _⟩ := exists_least_tunedFiniteWitness hn ho hc hGRH
  exact ⟨p, hp, hb, hr⟩

end PseudoPrime.PrimeTestBounds.MillerRabin

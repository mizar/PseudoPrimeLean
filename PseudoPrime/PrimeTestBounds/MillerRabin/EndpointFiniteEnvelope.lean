/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointFiniteComparison
public import PseudoPrime.LLS.PaperStatements.EndpointPointwiseMonotone

/-! # Thirteen finite principal candidates and their exact interval selection -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The thirteen finite principal profiles in increasing cap order. -/
def allFiniteProfiles : Finset Analysis.FinitePrimeProfile :=
  {.p23, .p29, .p31, .p37, .p41, .p43, .p47,
    .p53, .p59, .p61, .p67, .p71, .p73}

/-- Every finite principal profile occurs in the candidate set. -/
theorem mem_allFiniteProfiles (f : Analysis.FinitePrimeProfile) : f ∈ allFiniteProfiles := by
  cases f <;> decide +kernel

/-- Valid finite-principal constants and the current refined envelope form a nonempty set. -/
noncomputable def lowFiniteCandidates (n : ℕ) : Finset ℝ := by
  classical
    exact
    insert (refinedWitnessEnvelope n)
      (allFiniteProfiles.image fun f ↦
        if Real.log n ≤ (f.logCap : ℝ) then (f.bound : ℝ) else refinedWitnessEnvelope n)

/-- The current refined value belongs to the finite candidate set. -/
theorem lowFinite_mem_base (n : ℕ) : refinedWitnessEnvelope n ∈ lowFiniteCandidates n := by
  classical exact Finset.mem_insert_self _ _

/-- The guarded thirteen-candidate minimum preserves every input below 3000. -/
noncomputable def lowFiniteWitness (n : ℕ) : ℝ :=
  if n < 3000 then smallIntervalBound n else (lowFiniteCandidates n).min' ⟨_, lowFinite_mem_base n⟩

/-- The exact increasing-cap interval formula with the current refined fallback. -/
noncomputable def lowFiniteSelected (n : ℕ) : ℝ :=
  if n < 3000 then smallIntervalBound n
  else
    if Real.log n ≤ 8087 / 1000 then 23
    else
      if Real.log n ≤ 8325 / 1000 then 29
      else
        if Real.log n ≤ 8987 / 1000 then 31
        else
          if Real.log n ≤ 9390 / 1000 then 37
          else
            if Real.log n ≤ 9583 / 1000 then 41
            else
              if Real.log n ≤ 9952 / 1000 then 43
              else
                if Real.log n ≤ 10471 / 1000 then 47
                else
                  if Real.log n ≤ 10955 / 1000 then 53
                  else
                    if Real.log n ≤ 11109 / 1000 then 59
                    else
                      if Real.log n ≤ 11546 / 1000 then 61
                      else
                        if Real.log n ≤ 11830 / 1000 then 67
                        else
                          if Real.log n ≤ 11970 / 1000 then 71
                          else if Real.log n ≤ 12373 / 1000 then 73 else refinedSelectedEnvelope n

/-- Every natural input below 3000 keeps the small-interval value. -/
theorem lowFiniteWitness_eq_small {n : ℕ} (hN : n < 3000) :
    lowFiniteWitness n = smallIntervalBound n := by exact ite_eq_left hN

/-- The guarded finite-principal minimum is no larger than the current refined value. -/
theorem lowFiniteWitness_le_refined {n : ℕ} (hn : 1 < n) :
    lowFiniteWitness n ≤ refinedWitnessEnvelope n := by
  classical
  by_cases hN : n < 3000
  · rw [lowFiniteWitness_eq_small hN, refined_eq_small hn hN]
  · rw [lowFiniteWitness, ite_eq_right hN]
    exact Finset.min'_le _ _ (lowFinite_mem_base n)

/-- A common lower bound of the current value and valid profiles bounds the new minimum. -/
theorem lowFinite_lower_of_candidates {n : ℕ} (hn : 1 < n) {C : ℝ}
    (hB : C ≤ refinedWitnessEnvelope n)
    (hF : ∀ f : Analysis.FinitePrimeProfile, Real.log n ≤ f.logCap → C ≤ f.bound) :
    C ≤ lowFiniteWitness n := by
  classical
  by_cases hN : n < 3000
  · rw [lowFiniteWitness_eq_small hN]
    simpa only [refined_eq_small hn hN] using hB
  · rw [lowFiniteWitness, ite_eq_right hN]
    apply Finset.le_min'
    intro v hv
    rcases Finset.mem_insert.mp hv with he | hv
    · rw [he]
      exact hB
    · obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hv
      split_ifs with h
      · exact hF f h
      · exact hB

/-- Every valid fixed profile bounds the guarded finite-principal minimum. -/
theorem lowFinite_le_profile (f : Analysis.FinitePrimeProfile) {n : ℕ}
    (hL : Real.log n ≤ f.logCap) : lowFiniteWitness n ≤ f.bound := by
  classical
  by_cases hN : n < 3000
  · rw [lowFiniteWitness_eq_small hN]
    dsimp only [smallIntervalBound]
    cases f <;> split_ifs <;> norm_num only [Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat]
  · rw [lowFiniteWitness, ite_eq_right hN]
    have hm :
      (if Real.log n ≤ (f.logCap : ℝ) then (f.bound : ℝ) else refinedWitnessEnvelope n) ∈
        lowFiniteCandidates n :=
      Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨f, mem_allFiniteProfiles f, rfl⟩)
    simpa only [ite_eq_left hL] using Finset.min'_le _ _ hm

/-- Every profile selected above the preceding cap is no larger than another valid profile. -/
theorem lowFinite_bounds_order (f g : Analysis.FinitePrimeProfile) {n : ℕ}
    (hL : (lowFinitePreviousCap f : ℝ) < Real.log n) (hG : Real.log n ≤ g.logCap) :
    (f.bound : ℝ) ≤ g.bound := by
  cases f <;> cases g <;>
    norm_num only [lowFinitePreviousCap, Analysis.FinitePrimeProfile.logCap,
      Analysis.FinitePrimeProfile.bound, Rat.cast_div, Rat.cast_ofNat,
      Nat.cast_ofNat] at hL hG ⊢ <;>
    linarith only [hL, hG]

/-- On each new cap interval, the guarded minimum equals its fixed prime bound. -/
theorem lowFinite_eq_profile (f : Analysis.FinitePrimeProfile) {n : ℕ} (hn : 1 < n) (hN : 3000 ≤ n)
    (hL : (lowFinitePreviousCap f : ℝ) < Real.log n) (hU : Real.log n ≤ f.logCap) :
    lowFiniteWitness n = f.bound := by
  apply le_antisymm (lowFinite_le_profile f hU)
  exact
    lowFinite_lower_of_candidates hn (lowFinite_base_lower f hn hN hL hU)
      (fun g hG ↦ lowFinite_bounds_order f g hL hG)

/-- Above the final finite cap, the minimum reduces to the current refined envelope. -/
theorem lowFinite_eq_refined_of_log {n : ℕ} (hn : 1 < n) (hL : 12373 / 1000 < Real.log n) :
    lowFiniteWitness n = refinedWitnessEnvelope n := by
  apply le_antisymm (lowFiniteWitness_le_refined hn)
  apply lowFinite_lower_of_candidates hn le_rfl
  intro f hF
  cases f <;>
    norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] at hF <;>
    linarith only [hF, hL]

/-- The numerical minimum equals the explicit thirteen-interval selection
for every input above one. -/
theorem lowFinite_eq_selected {n : ℕ} (hn : 1 < n) : lowFiniteWitness n = lowFiniteSelected n := by
  by_cases hN : n < 3000
  · rw [lowFiniteWitness_eq_small hN]
    exact (ite_eq_left hN).symm
  have hlarge : 3000 ≤ n := le_of_not_gt hN
  by_cases h23 : Real.log n ≤ 8087 / 1000
  · have he :=
      lowFinite_eq_profile .p23 hn hlarge
        (by
          norm_num only [lowFinitePreviousCap, Rat.cast_zero]
          exact Real.log_pos (by exact_mod_cast hn))
        (by
          norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h23])
    simpa only [lowFiniteSelected, ite_eq_right hN, ite_eq_left h23,
      Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h29 : Real.log n ≤ 8325 / 1000
  · have he :=
      lowFinite_eq_profile .p29 hn hlarge
        (by
          norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h23])
        (by
          norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h29])
    simpa only [lowFiniteSelected, ite_eq_right hN, ite_eq_right h23, ite_eq_left h29,
      Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h31 : Real.log n ≤ 8987 / 1000
  · have he :=
      lowFinite_eq_profile .p31 hn hlarge
        (by
          norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h29])
        (by
          norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h31])
    simpa only [lowFiniteSelected, ite_eq_right hN, ite_eq_right h23, ite_eq_right h29,
      ite_eq_left h31, Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h37 : Real.log n ≤ 9390 / 1000
  · have he :=
      lowFinite_eq_profile .p37 hn hlarge
        (by
          norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h31])
        (by
          norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h37])
    simpa only [lowFiniteSelected, ite_eq_right hN, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_left h37, Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h41 : Real.log n ≤ 9583 / 1000
  · have he :=
      lowFinite_eq_profile .p41 hn hlarge
        (by
          norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h37])
        (by
          norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h41])
    simpa only [lowFiniteSelected, ite_eq_right hN, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_left h41, Analysis.FinitePrimeProfile.bound,
      Nat.cast_ofNat] using he
  by_cases h43 : Real.log n ≤ 9952 / 1000
  · have he :=
      lowFinite_eq_profile .p43 hn hlarge
        (by
          norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h41])
        (by
          norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h43])
    simpa only [lowFiniteSelected, ite_eq_right hN, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_left h43,
      Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h47 : Real.log n ≤ 10471 / 1000
  · have he :=
      lowFinite_eq_profile .p47 hn hlarge
        (by
          norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h43])
        (by
          norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h47])
    simpa only [lowFiniteSelected, ite_eq_right hN, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_right h43, ite_eq_left h47,
      Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h53 : Real.log n ≤ 10955 / 1000
  · have he :=
      lowFinite_eq_profile .p53 hn hlarge
        (by
          norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h47])
        (by
          norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h53])
    simpa only [lowFiniteSelected, ite_eq_right hN, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_right h43, ite_eq_right h47,
      ite_eq_left h53, Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h59 : Real.log n ≤ 11109 / 1000
  · have he :=
      lowFinite_eq_profile .p59 hn hlarge
        (by
          norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h53])
        (by
          norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h59])
    simpa only [lowFiniteSelected, ite_eq_right hN, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_right h43, ite_eq_right h47,
      ite_eq_right h53, ite_eq_left h59, Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h61 : Real.log n ≤ 11546 / 1000
  · have he :=
      lowFinite_eq_profile .p61 hn hlarge
        (by
          norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h59])
        (by
          norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h61])
    simpa only [lowFiniteSelected, ite_eq_right hN, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_right h43, ite_eq_right h47,
      ite_eq_right h53, ite_eq_right h59, ite_eq_left h61, Analysis.FinitePrimeProfile.bound,
      Nat.cast_ofNat] using he
  by_cases h67 : Real.log n ≤ 11830 / 1000
  · have he :=
      lowFinite_eq_profile .p67 hn hlarge
        (by
          norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h61])
        (by
          norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h67])
    simpa only [lowFiniteSelected, ite_eq_right hN, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_right h43, ite_eq_right h47,
      ite_eq_right h53, ite_eq_right h59, ite_eq_right h61, ite_eq_left h67,
      Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h71 : Real.log n ≤ 11970 / 1000
  · have he :=
      lowFinite_eq_profile .p71 hn hlarge
        (by
          norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h67])
        (by
          norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h71])
    simpa only [lowFiniteSelected, ite_eq_right hN, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_right h43, ite_eq_right h47,
      ite_eq_right h53, ite_eq_right h59, ite_eq_right h61, ite_eq_right h67, ite_eq_left h71,
      Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  by_cases h73 : Real.log n ≤ 12373 / 1000
  · have he :=
      lowFinite_eq_profile .p73 hn hlarge
        (by
          norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [lt_of_not_ge h71])
        (by
          norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
          linarith only [h73])
    simpa only [lowFiniteSelected, ite_eq_right hN, ite_eq_right h23, ite_eq_right h29,
      ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_right h43, ite_eq_right h47,
      ite_eq_right h53, ite_eq_right h59, ite_eq_right h61, ite_eq_right h67, ite_eq_right h71,
      ite_eq_left h73, Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat] using he
  rw [lowFinite_eq_refined_of_log hn (lt_of_not_ge h73), refined_eq_selected hn]
  simp only [lowFiniteSelected, ite_eq_right hN, ite_eq_right h23, ite_eq_right h29,
    ite_eq_right h31, ite_eq_right h37, ite_eq_right h41, ite_eq_right h43, ite_eq_right h47,
    ite_eq_right h53, ite_eq_right h59, ite_eq_right h61, ite_eq_right h67, ite_eq_right h71,
    ite_eq_right h73]

/-- One current least rejecting prime lies below all thirteen valid finite candidates. -/
theorem exists_least_lowFiniteWitness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ lowFiniteWitness n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p, hp, hr, hb, hm⟩ := exists_least_refinedEnvelope hn ho hc hGRH
  have transfer (f : Analysis.FinitePrimeProfile) (hL : Real.log n ≤ f.logCap) :
    (p : ℝ) ≤ f.bound := by
    obtain ⟨q, hq, hqb, hqr⟩ := exists_prime_finitePrincipal f hn ho hc hGRH hL
    exact (Nat.cast_le.mpr (hm q hq hqr)).trans hqb
  exact ⟨p, hp, hr, lowFinite_lower_of_candidates hn hb transfer, hm⟩

/-- Forget leastness to obtain an actual prime witness below the new finite minimum. -/
theorem exists_prime_lowFiniteWitness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧ (p : ℝ) ≤ lowFiniteWitness n ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hr, hb, _⟩ := exists_least_lowFiniteWitness hn ho hc hGRH
  exact ⟨p, hp, hb, hr⟩

end PseudoPrime.PrimeTestBounds.MillerRabin

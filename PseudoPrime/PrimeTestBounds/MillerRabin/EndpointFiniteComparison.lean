/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointFinitePrincipal
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedIntervalSelection
public import PseudoPrime.LLS.PaperStatements.EndpointFiniteRoundCells

/-! # Strict finite-principal improvement over the current refined envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Embed the nine existing low profiles into the thirteen finite-principal profiles. -/
def lowPrincipalProfile : LLS.PaperStatements.LowPrimeProfile → Analysis.FinitePrimeProfile
  | .p23 => .p23
  | .p29 => .p29
  | .p31 => .p31
  | .p37 => .p37
  | .p41 => .p41
  | .p43 => .p43
  | .p47 => .p47
  | .p53 => .p53
  | .p59 => .p59

/-- Between each current and strengthened cap, the current selected value is the next prime. -/
theorem finitePrincipal_low_current (f : LLS.PaperStatements.LowPrimeProfile) {n : ℕ} (hn : 1 < n)
    (hN : 3000 ≤ n) (hL : (f.tightLogCap : ℝ) < Real.log n)
    (hU : Real.log n ≤ (lowPrincipalProfile f).logCap) :
    refinedSelectedEnvelope n = f.nextPrime := by
  cases f
  · norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, lowPrincipalProfile,
      Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] at hL hU
    have he :=
      refinedSelected_eq_profile .p29 hn hN
        (by
          norm_num only [tightLowPreviousCap]; linarith only [hL])
        (by
          norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
            Rat.cast_ofNat];
          linarith only [hU])
    simpa only [LLS.PaperStatements.LowPrimeProfile.bound,
      LLS.PaperStatements.LowPrimeProfile.nextPrime, Nat.cast_ofNat] using he
  · norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, lowPrincipalProfile,
      Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] at hL hU
    have he :=
      refinedSelected_eq_profile .p31 hn hN
        (by
          norm_num only [tightLowPreviousCap]; linarith only [hL])
        (by
          norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
            Rat.cast_ofNat];
          linarith only [hU])
    simpa only [LLS.PaperStatements.LowPrimeProfile.bound,
      LLS.PaperStatements.LowPrimeProfile.nextPrime, Nat.cast_ofNat] using he
  · norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, lowPrincipalProfile,
      Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] at hL hU
    have he :=
      refinedSelected_eq_profile .p37 hn hN
        (by
          norm_num only [tightLowPreviousCap]; linarith only [hL])
        (by
          norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
            Rat.cast_ofNat];
          linarith only [hU])
    simpa only [LLS.PaperStatements.LowPrimeProfile.bound,
      LLS.PaperStatements.LowPrimeProfile.nextPrime, Nat.cast_ofNat] using he
  · norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, lowPrincipalProfile,
      Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] at hL hU
    have he :=
      refinedSelected_eq_profile .p41 hn hN
        (by
          norm_num only [tightLowPreviousCap]; linarith only [hL])
        (by
          norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
            Rat.cast_ofNat];
          linarith only [hU])
    simpa only [LLS.PaperStatements.LowPrimeProfile.bound,
      LLS.PaperStatements.LowPrimeProfile.nextPrime, Nat.cast_ofNat] using he
  · norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, lowPrincipalProfile,
      Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] at hL hU
    have he :=
      refinedSelected_eq_profile .p43 hn hN
        (by
          norm_num only [tightLowPreviousCap]; linarith only [hL])
        (by
          norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
            Rat.cast_ofNat];
          linarith only [hU])
    simpa only [LLS.PaperStatements.LowPrimeProfile.bound,
      LLS.PaperStatements.LowPrimeProfile.nextPrime, Nat.cast_ofNat] using he
  · norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, lowPrincipalProfile,
      Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] at hL hU
    have he :=
      refinedSelected_eq_profile .p47 hn hN
        (by
          norm_num only [tightLowPreviousCap]; linarith only [hL])
        (by
          norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
            Rat.cast_ofNat];
          linarith only [hU])
    simpa only [LLS.PaperStatements.LowPrimeProfile.bound,
      LLS.PaperStatements.LowPrimeProfile.nextPrime, Nat.cast_ofNat] using he
  · norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, lowPrincipalProfile,
      Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] at hL hU
    have he :=
      refinedSelected_eq_profile .p53 hn hN
        (by
          norm_num only [tightLowPreviousCap]; linarith only [hL])
        (by
          norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
            Rat.cast_ofNat];
          linarith only [hU])
    simpa only [LLS.PaperStatements.LowPrimeProfile.bound,
      LLS.PaperStatements.LowPrimeProfile.nextPrime, Nat.cast_ofNat] using he
  · norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, lowPrincipalProfile,
      Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] at hL hU
    have he :=
      refinedSelected_eq_profile .p59 hn hN
        (by
          norm_num only [tightLowPreviousCap]; linarith only [hL])
        (by
          norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
            Rat.cast_ofNat];
          linarith only [hU])
    simpa only [LLS.PaperStatements.LowPrimeProfile.bound,
      LLS.PaperStatements.LowPrimeProfile.nextPrime, Nat.cast_ofNat] using he
  · norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, lowPrincipalProfile,
      Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] at hL hU
    rw [refinedSelected_eq_next_low hn (by linarith only [hL]) (by linarith only [hU]), ←
      next_eq_selected hn, next_eq_fixed61 hn hN (by linarith only [hL]) (by linarith only [hU])]
    norm_num only [LLS.PaperStatements.LowPrimeProfile.nextPrime, Nat.cast_ofNat]

/-- All nine strengthened low caps strictly beat both current public values on their extensions. -/
theorem finitePrincipal_low_strict (f : LLS.PaperStatements.LowPrimeProfile) {n : ℕ} (hn : 1 < n)
    (hN : 3000 ≤ n) (hL : (f.tightLogCap : ℝ) < Real.log n)
    (hU : Real.log n ≤ (lowPrincipalProfile f).logCap) :
    ((lowPrincipalProfile f).bound : ℝ) < refinedSelectedEnvelope n ∧
      ((lowPrincipalProfile f).bound : ℝ) < refinedPrimeEnvelope n := by
  have he := finitePrincipal_low_current f hn hN hL hU
  have hp : Nat.Prime f.nextPrime := by cases f <;> decide +kernel
  have hlt : ((lowPrincipalProfile f).bound : ℝ) < f.nextPrime := by
    cases f <;>
      norm_num only [lowPrincipalProfile, Analysis.FinitePrimeProfile.bound,
        LLS.PaperStatements.LowPrimeProfile.nextPrime, Nat.cast_ofNat]
  constructor
  · rw [he]
    exact hlt
  · rw [refinedPrimeEnvelope, refined_eq_selected hn, he, primeRound_prime hp]
    exact hlt

/-- On each of the four specified closed cells, both current public cutoffs reach the next prime. -/
theorem finitePrincipal_upper_current (c : LLS.PaperStatements.FiniteRoundCell) {n : ℕ} (hn : 1 < n)
    (hL : (c.left : ℝ) ≤ Real.log n) (hU : Real.log n ≤ c.profile.logCap) :
    (c.profile.nextPrime : ℝ) ≤ refinedSelectedEnvelope n ∧
      (c.profile.nextPrime : ℝ) ≤ refinedPrimeEnvelope n := by
  have hp := (LLS.PaperStatements.finiteRound_pointwise_lower c hL).le
  have hsmall : Real.log n < 63 := by
    cases c <;>
      norm_num only [LLS.PaperStatements.FiniteRoundCell.profile,
        Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] at hU <;>
      linarith only [hU]
  have hlarge : 11062 / 1000 < Real.log n := by
    cases c <;>
      norm_num only [LLS.PaperStatements.FiniteRoundCell.left, Rat.cast_div,
        Rat.cast_ofNat] at hL <;>
      linarith only [hL]
  have he : refinedSelectedEnvelope n = nextWitnessEnvelope n := by
    rw [refinedSelected_eq_next_low hn hlarge hsmall, next_eq_selected hn]
  have hb : (c.profile.nextPrime : ℝ) ≤ nextWitnessEnvelope n := by
    cases c <;>
      norm_num only [LLS.PaperStatements.FiniteRoundCell.left,
        LLS.PaperStatements.FiniteRoundCell.profile, Analysis.FinitePrimeProfile.logCap,
        Analysis.FinitePrimeProfile.nextPrime, Rat.cast_div, Rat.cast_ofNat,
        Nat.cast_ofNat] at hL hU hp ⊢
    · rw [next_eq_min67 hn (by linarith only [hL]) (by linarith only [hU])]
      exact le_min le_rfl hp
    · rw [next_eq_min71 hn (by linarith only [hL]) (by linarith only [hU])]
      exact le_min le_rfl hp
    · rw [next_eq_min73 hn (by linarith only [hL]) (by linarith only [hU])]
      exact le_min le_rfl hp
    · rw [next_eq_pointwise hn (by linarith only [hL]) (by linarith only [hU])]
      exact hp
  have hq : Nat.Prime c.profile.nextPrime := by cases c <;> decide +kernel
  constructor
  · rw [he]
    exact hb
  · rw [refinedPrimeEnvelope, refined_eq_selected hn, he]
    exact prime_le_primeRound hq hb

/-- The last four finite profiles strictly improve both current cutoffs on their closed cells. -/
theorem finitePrincipal_upper_strict (c : LLS.PaperStatements.FiniteRoundCell) {n : ℕ} (hn : 1 < n)
    (hL : (c.left : ℝ) ≤ Real.log n) (hU : Real.log n ≤ c.profile.logCap) :
    (c.profile.bound : ℝ) < refinedSelectedEnvelope n ∧
      (c.profile.bound : ℝ) < refinedPrimeEnvelope n := by
  have hq : (c.profile.bound : ℝ) < c.profile.nextPrime := by
    cases c <;>
      norm_num only [LLS.PaperStatements.FiniteRoundCell.profile, Analysis.FinitePrimeProfile.bound,
        Analysis.FinitePrimeProfile.nextPrime, Nat.cast_ofNat]
  have hc := finitePrincipal_upper_current c hn hL hU
  exact ⟨hq.trans_le hc.1, hq.trans_le hc.2⟩

/-- The preceding new cap, with zero at the first finite profile. -/
def lowFinitePreviousCap : Analysis.FinitePrimeProfile → ℚ
  | .p23 => 0
  | .p29 => 8087 / 1000
  | .p31 => 8325 / 1000
  | .p37 => 8987 / 1000
  | .p41 => 9390 / 1000
  | .p43 => 9583 / 1000
  | .p47 => 9952 / 1000
  | .p53 => 10471 / 1000
  | .p59 => 10955 / 1000
  | .p61 => 11109 / 1000
  | .p67 => 11546 / 1000
  | .p71 => 11830 / 1000
  | .p73 => 11970 / 1000

/-- A profile selected after the previous new cap is bounded by the current refined value. -/
theorem lowFinite_base_lower (f : Analysis.FinitePrimeProfile) {n : ℕ} (hn : 1 < n) (hN : 3000 ≤ n)
    (hL : (lowFinitePreviousCap f : ℝ) < Real.log n) (hU : Real.log n ≤ f.logCap) :
    (f.bound : ℝ) ≤ refinedWitnessEnvelope n := by
  rw [refined_eq_selected hn]
  cases f
  · norm_num only [lowFinitePreviousCap, Analysis.FinitePrimeProfile.logCap, Rat.cast_div,
      Rat.cast_ofNat] at hL hU
    by_cases hOld : Real.log n ≤ (LLS.PaperStatements.LowPrimeProfile.tightLogCap .p23 : ℝ)
    · rw [refinedSelected_eq_profile .p23 hn hN
          (by
            norm_num only [tightLowPreviousCap]; linarith only [hL])
          hOld]
      norm_num only [Analysis.FinitePrimeProfile.bound, LLS.PaperStatements.LowPrimeProfile.bound,
        Nat.cast_ofNat]
    · have hs :=
        (finitePrincipal_low_strict .p23 hn hN (lt_of_not_ge hOld)
            (by
              norm_num only [lowPrincipalProfile, Analysis.FinitePrimeProfile.logCap, Rat.cast_div,
                Rat.cast_ofNat];
              linarith only [hU])).1.le
      simpa only [lowPrincipalProfile] using hs
  · norm_num only [lowFinitePreviousCap, Analysis.FinitePrimeProfile.logCap, Rat.cast_div,
      Rat.cast_ofNat] at hL hU
    by_cases hOld : Real.log n ≤ (LLS.PaperStatements.LowPrimeProfile.tightLogCap .p29 : ℝ)
    · rw [refinedSelected_eq_profile .p29 hn hN
          (by
            norm_num only [tightLowPreviousCap]; linarith only [hL])
          hOld]
      norm_num only [Analysis.FinitePrimeProfile.bound, LLS.PaperStatements.LowPrimeProfile.bound,
        Nat.cast_ofNat]
    · have hs :=
        (finitePrincipal_low_strict .p29 hn hN (lt_of_not_ge hOld)
            (by
              norm_num only [lowPrincipalProfile, Analysis.FinitePrimeProfile.logCap, Rat.cast_div,
                Rat.cast_ofNat];
              linarith only [hU])).1.le
      simpa only [lowPrincipalProfile] using hs
  · norm_num only [lowFinitePreviousCap, Analysis.FinitePrimeProfile.logCap, Rat.cast_div,
      Rat.cast_ofNat] at hL hU
    by_cases hOld : Real.log n ≤ (LLS.PaperStatements.LowPrimeProfile.tightLogCap .p31 : ℝ)
    · rw [refinedSelected_eq_profile .p31 hn hN
          (by
            norm_num only [tightLowPreviousCap]; linarith only [hL])
          hOld]
      norm_num only [Analysis.FinitePrimeProfile.bound, LLS.PaperStatements.LowPrimeProfile.bound,
        Nat.cast_ofNat]
    · have hs :=
        (finitePrincipal_low_strict .p31 hn hN (lt_of_not_ge hOld)
            (by
              norm_num only [lowPrincipalProfile, Analysis.FinitePrimeProfile.logCap, Rat.cast_div,
                Rat.cast_ofNat];
              linarith only [hU])).1.le
      simpa only [lowPrincipalProfile] using hs
  · norm_num only [lowFinitePreviousCap, Analysis.FinitePrimeProfile.logCap, Rat.cast_div,
      Rat.cast_ofNat] at hL hU
    by_cases hOld : Real.log n ≤ (LLS.PaperStatements.LowPrimeProfile.tightLogCap .p37 : ℝ)
    · rw [refinedSelected_eq_profile .p37 hn hN
          (by
            norm_num only [tightLowPreviousCap]; linarith only [hL])
          hOld]
      norm_num only [Analysis.FinitePrimeProfile.bound, LLS.PaperStatements.LowPrimeProfile.bound,
        Nat.cast_ofNat]
    · have hs :=
        (finitePrincipal_low_strict .p37 hn hN (lt_of_not_ge hOld)
            (by
              norm_num only [lowPrincipalProfile, Analysis.FinitePrimeProfile.logCap, Rat.cast_div,
                Rat.cast_ofNat];
              linarith only [hU])).1.le
      simpa only [lowPrincipalProfile] using hs
  · norm_num only [lowFinitePreviousCap, Analysis.FinitePrimeProfile.logCap, Rat.cast_div,
      Rat.cast_ofNat] at hL hU
    by_cases hOld : Real.log n ≤ (LLS.PaperStatements.LowPrimeProfile.tightLogCap .p41 : ℝ)
    · rw [refinedSelected_eq_profile .p41 hn hN
          (by
            norm_num only [tightLowPreviousCap]; linarith only [hL])
          hOld]
      norm_num only [Analysis.FinitePrimeProfile.bound, LLS.PaperStatements.LowPrimeProfile.bound,
        Nat.cast_ofNat]
    · have hs :=
        (finitePrincipal_low_strict .p41 hn hN (lt_of_not_ge hOld)
            (by
              norm_num only [lowPrincipalProfile, Analysis.FinitePrimeProfile.logCap, Rat.cast_div,
                Rat.cast_ofNat];
              linarith only [hU])).1.le
      simpa only [lowPrincipalProfile] using hs
  · norm_num only [lowFinitePreviousCap, Analysis.FinitePrimeProfile.logCap, Rat.cast_div,
      Rat.cast_ofNat] at hL hU
    by_cases hOld : Real.log n ≤ (LLS.PaperStatements.LowPrimeProfile.tightLogCap .p43 : ℝ)
    · rw [refinedSelected_eq_profile .p43 hn hN
          (by
            norm_num only [tightLowPreviousCap]; linarith only [hL])
          hOld]
      norm_num only [Analysis.FinitePrimeProfile.bound, LLS.PaperStatements.LowPrimeProfile.bound,
        Nat.cast_ofNat]
    · have hs :=
        (finitePrincipal_low_strict .p43 hn hN (lt_of_not_ge hOld)
            (by
              norm_num only [lowPrincipalProfile, Analysis.FinitePrimeProfile.logCap, Rat.cast_div,
                Rat.cast_ofNat];
              linarith only [hU])).1.le
      simpa only [lowPrincipalProfile] using hs
  · norm_num only [lowFinitePreviousCap, Analysis.FinitePrimeProfile.logCap, Rat.cast_div,
      Rat.cast_ofNat] at hL hU
    by_cases hOld : Real.log n ≤ (LLS.PaperStatements.LowPrimeProfile.tightLogCap .p47 : ℝ)
    · rw [refinedSelected_eq_profile .p47 hn hN
          (by
            norm_num only [tightLowPreviousCap]; linarith only [hL])
          hOld]
      norm_num only [Analysis.FinitePrimeProfile.bound, LLS.PaperStatements.LowPrimeProfile.bound,
        Nat.cast_ofNat]
    · have hs :=
        (finitePrincipal_low_strict .p47 hn hN (lt_of_not_ge hOld)
            (by
              norm_num only [lowPrincipalProfile, Analysis.FinitePrimeProfile.logCap, Rat.cast_div,
                Rat.cast_ofNat];
              linarith only [hU])).1.le
      simpa only [lowPrincipalProfile] using hs
  · norm_num only [lowFinitePreviousCap, Analysis.FinitePrimeProfile.logCap, Rat.cast_div,
      Rat.cast_ofNat] at hL hU
    by_cases hOld : Real.log n ≤ (LLS.PaperStatements.LowPrimeProfile.tightLogCap .p53 : ℝ)
    · rw [refinedSelected_eq_profile .p53 hn hN
          (by
            norm_num only [tightLowPreviousCap]; linarith only [hL])
          hOld]
      norm_num only [Analysis.FinitePrimeProfile.bound, LLS.PaperStatements.LowPrimeProfile.bound,
        Nat.cast_ofNat]
    · have hs :=
        (finitePrincipal_low_strict .p53 hn hN (lt_of_not_ge hOld)
            (by
              norm_num only [lowPrincipalProfile, Analysis.FinitePrimeProfile.logCap, Rat.cast_div,
                Rat.cast_ofNat];
              linarith only [hU])).1.le
      simpa only [lowPrincipalProfile] using hs
  · norm_num only [lowFinitePreviousCap, Analysis.FinitePrimeProfile.logCap, Rat.cast_div,
      Rat.cast_ofNat] at hL hU
    by_cases hOld : Real.log n ≤ (LLS.PaperStatements.LowPrimeProfile.tightLogCap .p59 : ℝ)
    · rw [refinedSelected_eq_profile .p59 hn hN
          (by
            norm_num only [tightLowPreviousCap]; linarith only [hL])
          hOld]
      norm_num only [Analysis.FinitePrimeProfile.bound, LLS.PaperStatements.LowPrimeProfile.bound,
        Nat.cast_ofNat]
    · have hs :=
        (finitePrincipal_low_strict .p59 hn hN (lt_of_not_ge hOld)
            (by
              norm_num only [lowPrincipalProfile, Analysis.FinitePrimeProfile.logCap, Rat.cast_div,
                Rat.cast_ofNat];
              linarith only [hU])).1.le
      simpa only [lowPrincipalProfile] using hs
  · norm_num only [lowFinitePreviousCap, Analysis.FinitePrimeProfile.logCap, Rat.cast_div,
      Rat.cast_ofNat] at hL hU
    rw [refinedSelected_eq_next_low hn (by linarith only [hL]) (by linarith only [hU]), ←
      next_eq_selected hn]
    norm_num only [Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat]
    by_cases hOld : Real.log n ≤ 11509 / 1000
    · rw [next_eq_fixed61 hn hN (by linarith only [hL]) hOld]
    · rw [next_eq_min67 hn (lt_of_not_ge hOld) (by linarith only [hU])]
      apply le_min (by norm_num only)
      have hs := LLS.PaperStatements.pointwiseRadius_spec (Real.log n)
      dsimp only [LLS.PaperStatements.pointwiseCutoff]
      nlinarith only [hs.1]
  · norm_num only [lowFinitePreviousCap, Analysis.FinitePrimeProfile.logCap, Rat.cast_div,
      Rat.cast_ofNat] at hL hU
    rw [refinedSelected_eq_next_low hn (by linarith only [hL]) (by linarith only [hU]), ←
      next_eq_selected hn]
    norm_num only [Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat]
    have hp :=
      (LLS.PaperStatements.finiteRound_pointwise_lower .p61 (L := Real.log n)
          (by
            norm_num only [LLS.PaperStatements.FiniteRoundCell.left, Rat.cast_div, Rat.cast_ofNat];
            linarith only [hL])).le
    norm_num only [LLS.PaperStatements.FiniteRoundCell.profile,
      Analysis.FinitePrimeProfile.nextPrime, Nat.cast_ofNat] at hp
    by_cases hOld : Real.log n ≤ 1179 / 100
    · rw [next_eq_min67 hn (by linarith only [hL]) hOld]
      exact le_min le_rfl hp
    · rw [next_eq_min71 hn (lt_of_not_ge hOld) (by linarith only [hU])]
      exact le_min (by norm_num only) hp
  · norm_num only [lowFinitePreviousCap, Analysis.FinitePrimeProfile.logCap, Rat.cast_div,
      Rat.cast_ofNat] at hL hU
    rw [refinedSelected_eq_next_low hn (by linarith only [hL]) (by linarith only [hU]), ←
      next_eq_selected hn]
    norm_num only [Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat]
    have hp :=
      (LLS.PaperStatements.finiteRound_pointwise_lower .p67 (L := Real.log n)
          (by
            norm_num only [LLS.PaperStatements.FiniteRoundCell.left, Rat.cast_div, Rat.cast_ofNat];
            linarith only [hL])).le
    norm_num only [LLS.PaperStatements.FiniteRoundCell.profile,
      Analysis.FinitePrimeProfile.nextPrime, Nat.cast_ofNat] at hp
    by_cases hOld : Real.log n ≤ 1193 / 100
    · rw [next_eq_min71 hn (by linarith only [hL]) hOld]
      exact le_min le_rfl hp
    · rw [next_eq_min73 hn (lt_of_not_ge hOld) (by linarith only [hU])]
      exact le_min (by norm_num only) hp
  · norm_num only [lowFinitePreviousCap, Analysis.FinitePrimeProfile.logCap, Rat.cast_div,
      Rat.cast_ofNat] at hL hU
    rw [refinedSelected_eq_next_low hn (by linarith only [hL]) (by linarith only [hU]), ←
      next_eq_selected hn]
    norm_num only [Analysis.FinitePrimeProfile.bound, Nat.cast_ofNat]
    have hp :=
      (LLS.PaperStatements.finiteRound_pointwise_lower .p71 (L := Real.log n)
          (by
            norm_num only [LLS.PaperStatements.FiniteRoundCell.left, Rat.cast_div, Rat.cast_ofNat];
            linarith only [hL])).le
    norm_num only [LLS.PaperStatements.FiniteRoundCell.profile,
      Analysis.FinitePrimeProfile.nextPrime, Nat.cast_ofNat] at hp
    by_cases hOld : Real.log n ≤ 12337 / 1000
    · rw [next_eq_min73 hn (by linarith only [hL]) hOld]
      exact le_min le_rfl hp
    · rw [next_eq_pointwise hn (lt_of_not_ge hOld) (by linarith only [hU])]
      exact hp

end PseudoPrime.PrimeTestBounds.MillerRabin

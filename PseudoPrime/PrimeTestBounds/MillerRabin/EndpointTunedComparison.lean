/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointFiniteTuned
public import PseudoPrime.PrimeTestBounds.MillerRabin.SharpNormalForm

/-! # Strict tuned finite-principal gains against the current sharp public cutoffs -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Across each tuned extension, both current sharp cutoffs reach the next prime. -/
theorem finiteTuned_current_lower (f : Analysis.FinitePrimeProfile) {n : ℕ} (hn : 1 < n)
    (hN : 3000 ≤ n) (hL : (f.logCap : ℝ) < Real.log n) (hU : Real.log n ≤ f.tunedCap) :
    (f.nextPrime : ℝ) ≤ sharpSelectedEnvelope n ∧ (f.nextPrime : ℝ) ≤ sharpPrimeEnvelope n := by
  have hb : (f.nextPrime : ℝ) ≤ sharpSelectedEnvelope n := by
    cases f
    · norm_num only [Analysis.FinitePrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
        Rat.cast_div, Rat.cast_ofNat] at hL hU
      rw [sharpSelected_eq_low hN (by linarith only [hU]), ← lowFinite_eq_selected hn]
      have he :=
        lowFinite_eq_profile .p29 hn hN
          (by
            norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
            linarith only [hL])
          (by
            norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
            linarith only [hU])
      simpa only [Analysis.FinitePrimeProfile.bound, Analysis.FinitePrimeProfile.nextPrime,
        Nat.cast_ofNat] using he.ge
    · norm_num only [Analysis.FinitePrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
        Rat.cast_div, Rat.cast_ofNat] at hL hU
      rw [sharpSelected_eq_low hN (by linarith only [hU]), ← lowFinite_eq_selected hn]
      have he :=
        lowFinite_eq_profile .p31 hn hN
          (by
            norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
            linarith only [hL])
          (by
            norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
            linarith only [hU])
      simpa only [Analysis.FinitePrimeProfile.bound, Analysis.FinitePrimeProfile.nextPrime,
        Nat.cast_ofNat] using he.ge
    · norm_num only [Analysis.FinitePrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
        Rat.cast_div, Rat.cast_ofNat] at hL hU
      rw [sharpSelected_eq_low hN (by linarith only [hU]), ← lowFinite_eq_selected hn]
      have he :=
        lowFinite_eq_profile .p37 hn hN
          (by
            norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
            linarith only [hL])
          (by
            norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
            linarith only [hU])
      simpa only [Analysis.FinitePrimeProfile.bound, Analysis.FinitePrimeProfile.nextPrime,
        Nat.cast_ofNat] using he.ge
    · norm_num only [Analysis.FinitePrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
        Rat.cast_div, Rat.cast_ofNat] at hL hU
      rw [sharpSelected_eq_low hN (by linarith only [hU]), ← lowFinite_eq_selected hn]
      have he :=
        lowFinite_eq_profile .p41 hn hN
          (by
            norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
            linarith only [hL])
          (by
            norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
            linarith only [hU])
      simpa only [Analysis.FinitePrimeProfile.bound, Analysis.FinitePrimeProfile.nextPrime,
        Nat.cast_ofNat] using he.ge
    · norm_num only [Analysis.FinitePrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
        Rat.cast_div, Rat.cast_ofNat] at hL hU
      rw [sharpSelected_eq_low hN (by linarith only [hU]), ← lowFinite_eq_selected hn]
      have he :=
        lowFinite_eq_profile .p43 hn hN
          (by
            norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
            linarith only [hL])
          (by
            norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
            linarith only [hU])
      simpa only [Analysis.FinitePrimeProfile.bound, Analysis.FinitePrimeProfile.nextPrime,
        Nat.cast_ofNat] using he.ge
    · norm_num only [Analysis.FinitePrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
        Rat.cast_div, Rat.cast_ofNat] at hL hU
      rw [sharpSelected_eq_low hN (by linarith only [hU]), ← lowFinite_eq_selected hn]
      have he :=
        lowFinite_eq_profile .p47 hn hN
          (by
            norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
            linarith only [hL])
          (by
            norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
            linarith only [hU])
      simpa only [Analysis.FinitePrimeProfile.bound, Analysis.FinitePrimeProfile.nextPrime,
        Nat.cast_ofNat] using he.ge
    · norm_num only [Analysis.FinitePrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
        Rat.cast_div, Rat.cast_ofNat] at hL hU
      rw [sharpSelected_eq_low hN (by linarith only [hU]), ← lowFinite_eq_selected hn]
      have he :=
        lowFinite_eq_profile .p53 hn hN
          (by
            norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
            linarith only [hL])
          (by
            norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
            linarith only [hU])
      simpa only [Analysis.FinitePrimeProfile.bound, Analysis.FinitePrimeProfile.nextPrime,
        Nat.cast_ofNat] using he.ge
    · norm_num only [Analysis.FinitePrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
        Rat.cast_div, Rat.cast_ofNat] at hL hU
      rw [sharpSelected_eq_low hN (by linarith only [hU]), ← lowFinite_eq_selected hn]
      have he :=
        lowFinite_eq_profile .p59 hn hN
          (by
            norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
            linarith only [hL])
          (by
            norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
            linarith only [hU])
      simpa only [Analysis.FinitePrimeProfile.bound, Analysis.FinitePrimeProfile.nextPrime,
        Nat.cast_ofNat] using he.ge
    · norm_num only [Analysis.FinitePrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
        Rat.cast_div, Rat.cast_ofNat] at hL hU
      rw [sharpSelected_eq_low hN (by linarith only [hU]), ← lowFinite_eq_selected hn]
      have he :=
        lowFinite_eq_profile .p61 hn hN
          (by
            norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
            linarith only [hL])
          (by
            norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
            linarith only [hU])
      simpa only [Analysis.FinitePrimeProfile.bound, Analysis.FinitePrimeProfile.nextPrime,
        Nat.cast_ofNat] using he.ge
    · norm_num only [Analysis.FinitePrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
        Rat.cast_div, Rat.cast_ofNat] at hL hU
      rw [sharpSelected_eq_low hN (by linarith only [hU]), ← lowFinite_eq_selected hn]
      have he :=
        lowFinite_eq_profile .p67 hn hN
          (by
            norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
            linarith only [hL])
          (by
            norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
            linarith only [hU])
      simpa only [Analysis.FinitePrimeProfile.bound, Analysis.FinitePrimeProfile.nextPrime,
        Nat.cast_ofNat] using he.ge
    · norm_num only [Analysis.FinitePrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
        Rat.cast_div, Rat.cast_ofNat] at hL hU
      rw [sharpSelected_eq_low hN (by linarith only [hU]), ← lowFinite_eq_selected hn]
      have he :=
        lowFinite_eq_profile .p71 hn hN
          (by
            norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
            linarith only [hL])
          (by
            norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
            linarith only [hU])
      simpa only [Analysis.FinitePrimeProfile.bound, Analysis.FinitePrimeProfile.nextPrime,
        Nat.cast_ofNat] using he.ge
    · norm_num only [Analysis.FinitePrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
        Rat.cast_div, Rat.cast_ofNat] at hL hU
      rw [sharpSelected_eq_low hN (by linarith only [hU]), ← lowFinite_eq_selected hn]
      have he :=
        lowFinite_eq_profile .p73 hn hN
          (by
            norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
            linarith only [hL])
          (by
            norm_num only [Analysis.FinitePrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat]
            linarith only [hU])
      simpa only [Analysis.FinitePrimeProfile.bound, Analysis.FinitePrimeProfile.nextPrime,
        Nat.cast_ofNat] using he.ge
    · norm_num only [Analysis.FinitePrimeProfile.logCap, Analysis.FinitePrimeProfile.tunedCap,
        Rat.cast_div, Rat.cast_ofNat] at hL hU
      rw [sharpSelected_eq_low hN (by linarith only [hU]),
        lowFiniteSelected_eq_refined hn (by linarith only [hL]),
        refined_eq_pointwise_low hn (by linarith only [hL]) (by linarith only [hU])]
      have hp :=
        (LLS.PaperStatements.finiteRound_pointwise_lower .p73 (L := Real.log n)
            (by
              norm_num only [LLS.PaperStatements.FiniteRoundCell.left, Rat.cast_div, Rat.cast_ofNat]
              linarith only [hL])).le
      simpa only [LLS.PaperStatements.FiniteRoundCell.profile] using hp
  have hq : Nat.Prime f.nextPrime := by cases f <;> decide +kernel
  refine ⟨hb, ?_⟩
  rw [sharpPrimeEnvelope, sharp_eq_selected hn]
  exact prime_le_primeRound hq hb

/-- Each of the thirteen tuned caps strictly improves both current sharp public cutoffs. -/
theorem finiteTuned_strict (f : Analysis.FinitePrimeProfile) {n : ℕ} (hn : 1 < n) (hN : 3000 ≤ n)
    (hL : (f.logCap : ℝ) < Real.log n) (hU : Real.log n ≤ f.tunedCap) :
    (f.bound : ℝ) < sharpSelectedEnvelope n ∧ (f.bound : ℝ) < sharpPrimeEnvelope n := by
  have hq : (f.bound : ℝ) < f.nextPrime := by
    cases f <;>
      norm_num only [Analysis.FinitePrimeProfile.bound, Analysis.FinitePrimeProfile.nextPrime,
        Nat.cast_ofNat]
  have hc := finiteTuned_current_lower f hn hN hL hU
  exact ⟨hq.trans_le hc.1, hq.trans_le hc.2⟩

end PseudoPrime.PrimeTestBounds.MillerRabin

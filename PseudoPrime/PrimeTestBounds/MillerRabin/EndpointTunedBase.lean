/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.EndpointTunedProfiles
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointTunedComparison
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointPrime79

/-! # Actual tuned profile witnesses and current sharp lower bounds -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Every one of fourteen tuned profiles supplies an actual rejecting prime through its cap. -/
theorem exists_prime_tunedProfile (f : Analysis.TunedPrimeProfile) {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hc : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ≤ f.logCap) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ f.bound ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  cases f with
  | finite f => exact exists_prime_finiteTuned f hn ho hc hGRH hL
  | p79 =>
    simpa only [Analysis.TunedPrimeProfile.bound, Nat.cast_ofNat] using
      exists_prime_endpoint79 hn ho hc hGRH hL

/-- The least rejecting prime satisfies every applicable tuned profile cutoff. -/
theorem exists_least_tunedProfile (f : Analysis.TunedPrimeProfile) {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hc : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ≤ f.logCap) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ f.bound ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact
    exists_least_prime_reject_of_exists_prime_reject (exists_prime_tunedProfile f hn ho hc hGRH hL)

/-- A newly selected fixed profile is below the current sharp value throughout its interval. -/
theorem tunedFinite_base_lower (f : Analysis.TunedPrimeProfile) {n : ℕ} (hn : 1 < n) (hN : 3000 ≤ n)
    (hL : (f.previousCap : ℝ) < Real.log n) (hU : Real.log n ≤ f.logCap) :
    (f.bound : ℝ) ≤ sharpWitnessEnvelope n := by
  rw [sharp_eq_selected hn]
  cases f with
  | finite f =>
    cases f
    · norm_num only [Analysis.TunedPrimeProfile.previousCap, Analysis.TunedPrimeProfile.logCap,
        Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero] at hL hU
      by_cases hOld : Real.log n ≤ (Analysis.FinitePrimeProfile.p23.logCap : ℝ)
      · have he :=
          lowFinite_eq_profile .p23 hn hN
            (by
              norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
              linarith only [hL])
            hOld
        rw [sharpSelected_eq_low hN (by linarith only [hU]), ← lowFinite_eq_selected hn, he]
        norm_num only [Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound,
          Nat.cast_ofNat]
      · have hs :=
          (finiteTuned_strict .p23 hn hN (lt_of_not_ge hOld)
              (by
                norm_num only [Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
                linarith only [hU])).1.le
        simpa only [Analysis.TunedPrimeProfile.bound] using hs
    · norm_num only [Analysis.TunedPrimeProfile.previousCap, Analysis.TunedPrimeProfile.logCap,
        Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero] at hL hU
      by_cases hOld : Real.log n ≤ (Analysis.FinitePrimeProfile.p29.logCap : ℝ)
      · have he :=
          lowFinite_eq_profile .p29 hn hN
            (by
              norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
              linarith only [hL])
            hOld
        rw [sharpSelected_eq_low hN (by linarith only [hU]), ← lowFinite_eq_selected hn, he]
        norm_num only [Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound,
          Nat.cast_ofNat]
      · have hs :=
          (finiteTuned_strict .p29 hn hN (lt_of_not_ge hOld)
              (by
                norm_num only [Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
                linarith only [hU])).1.le
        simpa only [Analysis.TunedPrimeProfile.bound] using hs
    · norm_num only [Analysis.TunedPrimeProfile.previousCap, Analysis.TunedPrimeProfile.logCap,
        Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero] at hL hU
      by_cases hOld : Real.log n ≤ (Analysis.FinitePrimeProfile.p31.logCap : ℝ)
      · have he :=
          lowFinite_eq_profile .p31 hn hN
            (by
              norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
              linarith only [hL])
            hOld
        rw [sharpSelected_eq_low hN (by linarith only [hU]), ← lowFinite_eq_selected hn, he]
        norm_num only [Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound,
          Nat.cast_ofNat]
      · have hs :=
          (finiteTuned_strict .p31 hn hN (lt_of_not_ge hOld)
              (by
                norm_num only [Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
                linarith only [hU])).1.le
        simpa only [Analysis.TunedPrimeProfile.bound] using hs
    · norm_num only [Analysis.TunedPrimeProfile.previousCap, Analysis.TunedPrimeProfile.logCap,
        Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero] at hL hU
      by_cases hOld : Real.log n ≤ (Analysis.FinitePrimeProfile.p37.logCap : ℝ)
      · have he :=
          lowFinite_eq_profile .p37 hn hN
            (by
              norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
              linarith only [hL])
            hOld
        rw [sharpSelected_eq_low hN (by linarith only [hU]), ← lowFinite_eq_selected hn, he]
        norm_num only [Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound,
          Nat.cast_ofNat]
      · have hs :=
          (finiteTuned_strict .p37 hn hN (lt_of_not_ge hOld)
              (by
                norm_num only [Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
                linarith only [hU])).1.le
        simpa only [Analysis.TunedPrimeProfile.bound] using hs
    · norm_num only [Analysis.TunedPrimeProfile.previousCap, Analysis.TunedPrimeProfile.logCap,
        Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero] at hL hU
      by_cases hOld : Real.log n ≤ (Analysis.FinitePrimeProfile.p41.logCap : ℝ)
      · have he :=
          lowFinite_eq_profile .p41 hn hN
            (by
              norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
              linarith only [hL])
            hOld
        rw [sharpSelected_eq_low hN (by linarith only [hU]), ← lowFinite_eq_selected hn, he]
        norm_num only [Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound,
          Nat.cast_ofNat]
      · have hs :=
          (finiteTuned_strict .p41 hn hN (lt_of_not_ge hOld)
              (by
                norm_num only [Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
                linarith only [hU])).1.le
        simpa only [Analysis.TunedPrimeProfile.bound] using hs
    · norm_num only [Analysis.TunedPrimeProfile.previousCap, Analysis.TunedPrimeProfile.logCap,
        Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero] at hL hU
      by_cases hOld : Real.log n ≤ (Analysis.FinitePrimeProfile.p43.logCap : ℝ)
      · have he :=
          lowFinite_eq_profile .p43 hn hN
            (by
              norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
              linarith only [hL])
            hOld
        rw [sharpSelected_eq_low hN (by linarith only [hU]), ← lowFinite_eq_selected hn, he]
        norm_num only [Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound,
          Nat.cast_ofNat]
      · have hs :=
          (finiteTuned_strict .p43 hn hN (lt_of_not_ge hOld)
              (by
                norm_num only [Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
                linarith only [hU])).1.le
        simpa only [Analysis.TunedPrimeProfile.bound] using hs
    · norm_num only [Analysis.TunedPrimeProfile.previousCap, Analysis.TunedPrimeProfile.logCap,
        Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero] at hL hU
      by_cases hOld : Real.log n ≤ (Analysis.FinitePrimeProfile.p47.logCap : ℝ)
      · have he :=
          lowFinite_eq_profile .p47 hn hN
            (by
              norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
              linarith only [hL])
            hOld
        rw [sharpSelected_eq_low hN (by linarith only [hU]), ← lowFinite_eq_selected hn, he]
        norm_num only [Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound,
          Nat.cast_ofNat]
      · have hs :=
          (finiteTuned_strict .p47 hn hN (lt_of_not_ge hOld)
              (by
                norm_num only [Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
                linarith only [hU])).1.le
        simpa only [Analysis.TunedPrimeProfile.bound] using hs
    · norm_num only [Analysis.TunedPrimeProfile.previousCap, Analysis.TunedPrimeProfile.logCap,
        Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero] at hL hU
      by_cases hOld : Real.log n ≤ (Analysis.FinitePrimeProfile.p53.logCap : ℝ)
      · have he :=
          lowFinite_eq_profile .p53 hn hN
            (by
              norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
              linarith only [hL])
            hOld
        rw [sharpSelected_eq_low hN (by linarith only [hU]), ← lowFinite_eq_selected hn, he]
        norm_num only [Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound,
          Nat.cast_ofNat]
      · have hs :=
          (finiteTuned_strict .p53 hn hN (lt_of_not_ge hOld)
              (by
                norm_num only [Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
                linarith only [hU])).1.le
        simpa only [Analysis.TunedPrimeProfile.bound] using hs
    · norm_num only [Analysis.TunedPrimeProfile.previousCap, Analysis.TunedPrimeProfile.logCap,
        Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero] at hL hU
      by_cases hOld : Real.log n ≤ (Analysis.FinitePrimeProfile.p59.logCap : ℝ)
      · have he :=
          lowFinite_eq_profile .p59 hn hN
            (by
              norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
              linarith only [hL])
            hOld
        rw [sharpSelected_eq_low hN (by linarith only [hU]), ← lowFinite_eq_selected hn, he]
        norm_num only [Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound,
          Nat.cast_ofNat]
      · have hs :=
          (finiteTuned_strict .p59 hn hN (lt_of_not_ge hOld)
              (by
                norm_num only [Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
                linarith only [hU])).1.le
        simpa only [Analysis.TunedPrimeProfile.bound] using hs
    · norm_num only [Analysis.TunedPrimeProfile.previousCap, Analysis.TunedPrimeProfile.logCap,
        Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero] at hL hU
      by_cases hOld : Real.log n ≤ (Analysis.FinitePrimeProfile.p61.logCap : ℝ)
      · have he :=
          lowFinite_eq_profile .p61 hn hN
            (by
              norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
              linarith only [hL])
            hOld
        rw [sharpSelected_eq_low hN (by linarith only [hU]), ← lowFinite_eq_selected hn, he]
        norm_num only [Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound,
          Nat.cast_ofNat]
      · have hs :=
          (finiteTuned_strict .p61 hn hN (lt_of_not_ge hOld)
              (by
                norm_num only [Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
                linarith only [hU])).1.le
        simpa only [Analysis.TunedPrimeProfile.bound] using hs
    · norm_num only [Analysis.TunedPrimeProfile.previousCap, Analysis.TunedPrimeProfile.logCap,
        Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero] at hL hU
      by_cases hOld : Real.log n ≤ (Analysis.FinitePrimeProfile.p67.logCap : ℝ)
      · have he :=
          lowFinite_eq_profile .p67 hn hN
            (by
              norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
              linarith only [hL])
            hOld
        rw [sharpSelected_eq_low hN (by linarith only [hU]), ← lowFinite_eq_selected hn, he]
        norm_num only [Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound,
          Nat.cast_ofNat]
      · have hs :=
          (finiteTuned_strict .p67 hn hN (lt_of_not_ge hOld)
              (by
                norm_num only [Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
                linarith only [hU])).1.le
        simpa only [Analysis.TunedPrimeProfile.bound] using hs
    · norm_num only [Analysis.TunedPrimeProfile.previousCap, Analysis.TunedPrimeProfile.logCap,
        Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero] at hL hU
      by_cases hOld : Real.log n ≤ (Analysis.FinitePrimeProfile.p71.logCap : ℝ)
      · have he :=
          lowFinite_eq_profile .p71 hn hN
            (by
              norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
              linarith only [hL])
            hOld
        rw [sharpSelected_eq_low hN (by linarith only [hU]), ← lowFinite_eq_selected hn, he]
        norm_num only [Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound,
          Nat.cast_ofNat]
      · have hs :=
          (finiteTuned_strict .p71 hn hN (lt_of_not_ge hOld)
              (by
                norm_num only [Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
                linarith only [hU])).1.le
        simpa only [Analysis.TunedPrimeProfile.bound] using hs
    · norm_num only [Analysis.TunedPrimeProfile.previousCap, Analysis.TunedPrimeProfile.logCap,
        Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat, Rat.cast_zero] at hL hU
      by_cases hOld : Real.log n ≤ (Analysis.FinitePrimeProfile.p73.logCap : ℝ)
      · have he :=
          lowFinite_eq_profile .p73 hn hN
            (by
              norm_num only [lowFinitePreviousCap, Rat.cast_div, Rat.cast_ofNat]
              linarith only [hL])
            hOld
        rw [sharpSelected_eq_low hN (by linarith only [hU]), ← lowFinite_eq_selected hn, he]
        norm_num only [Analysis.TunedPrimeProfile.bound, Analysis.FinitePrimeProfile.bound,
          Nat.cast_ofNat]
      · have hs :=
          (finiteTuned_strict .p73 hn hN (lt_of_not_ge hOld)
              (by
                norm_num only [Analysis.FinitePrimeProfile.tunedCap, Rat.cast_div, Rat.cast_ofNat]
                linarith only [hU])).1.le
        simpa only [Analysis.TunedPrimeProfile.bound] using hs
  | p79 =>
    norm_num only [Analysis.TunedPrimeProfile.previousCap, Analysis.FinitePrimeProfile.tunedCap,
      Analysis.TunedPrimeProfile.logCap, Analysis.prime79Cap, Rat.cast_div, Rat.cast_ofNat] at hL hU
    rw [sharpSelected_eq_low hN (by linarith only [hU]),
      lowFiniteSelected_eq_refined hn (by linarith only [hL]),
      refined_eq_pointwise_low hn (by linarith only [hL]) (by linarith only [hU])]
    have hp :=
      (LLS.PaperStatements.finiteRound_pointwise_lower .p73 (L := Real.log n)
          (by
            norm_num only [LLS.PaperStatements.FiniteRoundCell.left, Rat.cast_div, Rat.cast_ofNat]
            linarith only [hL])).le
    simpa only [LLS.PaperStatements.FiniteRoundCell.profile, Analysis.FinitePrimeProfile.nextPrime,
      Analysis.TunedPrimeProfile.bound, Nat.cast_ofNat] using hp

end PseudoPrime.PrimeTestBounds.MillerRabin

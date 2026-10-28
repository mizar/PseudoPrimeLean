/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedWitnessEnvelope
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianRecoveredOrder
public import PseudoPrime.PrimeTestBounds.MillerRabin.PointwisePrimeRound

/-! # Refined envelope intervals, preserved small values, and strict gains -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For every natural input above one, the refined interval value is no larger
than the fixed baseline selection. Rewrite both exact selection identities and
use the guarded envelope projection. -/
theorem refinedSelected_le_next {n : ℕ} (hn : 1 < n) :
    refinedSelectedEnvelope n ≤ nextSelectedEnvelope n := by
  rw [← refined_eq_selected hn, ← next_eq_selected hn]
  exact refinedWitnessEnvelope_le_next n

/-- For inputs above one, total prime rounding is no larger than the refined
interval value. Rewrite its exact guarded form and apply rounding non-worsening. -/
theorem refinedPrime_le_selected {n : ℕ} (hn : 1 < n) :
    refinedPrimeEnvelope n ≤ refinedSelectedEnvelope n := by
  rw [← refined_eq_selected hn]
  exact refinedPrimeEnvelope_le_refined n

/-- Any strict numerical improvement by the refined selected value also holds
for the rounded public cutoff. Compose the non-worsening rounding inequality. -/
theorem refinedPrime_lt_of_selected {n : ℕ} (hn : 1 < n) {B : ℝ}
    (hB : refinedSelectedEnvelope n < B) : refinedPrimeEnvelope n < B := by
  exact (refinedPrime_le_selected hn).trans_lt hB

/-- Below logarithmic scale 63, all new analytic guards are inactive and the
refined interval formula is exactly the extended low-prime selection. -/
theorem refinedSelected_eq_low {n : ℕ} (hL : Real.log n < 63) :
    refinedSelectedEnvelope n = lowPrimeTightSelected n := by exact ite_eq_left hL

/-- Every natural input below 3000 has logarithm below 63, including zero.
Separate zero and use the existing certified logarithm bound at 46000 for positive inputs. -/
theorem log_lt63_of_small {n : ℕ} (hN : n < 3000) : Real.log n < (63 : ℝ) := by
  by_cases hz : n = 0
  · rw [hz]
    norm_num only [Nat.cast_zero, Real.log_zero]
  · have hcast : (n : ℝ) ≤ 46000 := by
      exact_mod_cast (hN.le.trans (by norm_num only : 3000 ≤ 46000))
    have hL :=
      (Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hz)) hcast).trans_lt
        Analysis.log_46000_lt_eleven
    linarith only [hL]

/-- Every input below 3000 retains the existing small-interval value. Use its
logarithmic bound to deactivate analytic guards before selecting the low-prime value. -/
theorem refinedSelected_eq_small {n : ℕ} (hN : n < 3000) :
    refinedSelectedEnvelope n = smallIntervalBound n := by
  rw [refinedSelected_eq_low (log_lt63_of_small hN)]
  exact ite_eq_left hN

/-- For inputs above one and below 3000, the unrounded guarded envelope preserves
the existing small-interval bound. Apply the exact interval identity. -/
theorem refined_eq_small {n : ℕ} (hn : 1 < n) (hN : n < 3000) :
    refinedWitnessEnvelope n = smallIntervalBound n := by
  rw [refined_eq_selected hn]
  exact refinedSelected_eq_small hN

/-- For inputs above one and below 3000, the rounded public cutoff preserves
the small-interval bound. Both possible values, two and three, are already prime. -/
theorem refinedPrime_eq_small {n : ℕ} (hn : 1 < n) (hN : n < 3000) :
    refinedPrimeEnvelope n = smallIntervalBound n := by
  rw [refinedPrimeEnvelope, refined_eq_small hn hN]
  dsimp only [smallIntervalBound]
  split_ifs
  · simpa only [Nat.cast_ofNat] using primeRound_prime (by decide +kernel : Nat.Prime 2)
  · simpa only [Nat.cast_ofNat] using primeRound_prime (by decide +kernel : Nat.Prime 3)

/-- Each of the nine extended logarithmic caps is below the first analytic
entrance 63. Verify the finite rational data to justify all low-prime interval reductions. -/
theorem tightCap_lt63 (f : LLS.PaperStatements.LowPrimeProfile) : (f.tightLogCap : ℝ) < 63 := by
  cases f <;>
    norm_num only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div, Rat.cast_ofNat]

/-- On a profile's extended interval for inputs at least 3000, the refined
selection equals its prime bound. All analytic guards are inactive and the exact
low-prime profile-selection theorem applies. -/
theorem refinedSelected_eq_profile (f : LLS.PaperStatements.LowPrimeProfile) {n : ℕ} (hn : 1 < n)
    (hN : 3000 ≤ n) (hL : tightLowPreviousCap f < Real.log n) (hU : Real.log n ≤ f.tightLogCap) :
    refinedSelectedEnvelope n = f.bound := by
  rw [refinedSelected_eq_low (hU.trans_lt (tightCap_lt63 f)), ← lowPrimeTight_eq_selected hn]
  exact lowPrimeTight_eq_profile f hn hN hL hU

/-- On each extended low-prime interval, rounding preserves the selected prime
constant. Resolve the low-prime selection and check that all nine bounds are prime. -/
theorem refinedPrime_eq_profile (f : LLS.PaperStatements.LowPrimeProfile) {n : ℕ} (hn : 1 < n)
    (hN : 3000 ≤ n) (hL : tightLowPreviousCap f < Real.log n) (hU : Real.log n ≤ f.tightLogCap) :
    refinedPrimeEnvelope n = f.bound := by
  rw [refinedPrimeEnvelope, refined_eq_selected hn, refinedSelected_eq_profile f hn hN hL hU]
  exact primeRound_prime (by cases f <;> decide +kernel : Nat.Prime f.bound)

/-- Between the last extended low-prime cap and logarithmic scale 63, the
refined selection equals the fixed baseline. All new low and analytic guards are inactive. -/
theorem refinedSelected_eq_next_low {n : ℕ} (hn : 1 < n) (hL : 11062 / 1000 < Real.log n)
    (hU : Real.log n < 63) : refinedSelectedEnvelope n = nextSelectedEnvelope n := by
  rw [refinedSelected_eq_low hU, ← lowPrimeTight_eq_selected hn, lowPrimeTight_eq_next_of_log hL,
    next_eq_selected hn]

/-- For logarithmic scale in the full real interval [29/2,15], the rounded
refined public cutoff is exactly 113. Reduce inactive guards to the baseline and
use its continuous pointwise prime-rounding certificate. -/
theorem refinedPrime_eq113 {n : ℕ} (hn : 1 < n) (hL : 29 / 2 ≤ Real.log n) (hU : Real.log n ≤ 15) :
    refinedPrimeEnvelope n = 113 := by
  rw [refinedPrimeEnvelope, refined_eq_selected hn,
    refinedSelected_eq_next_low hn (by linarith only [hL]) (by linarith only [hU])]
  exact (nextSelected_primeRound113 hn hL hU).1

/-- From scale 63 up to 101, retain only the valid Gaussian and seeded
candidates together with the low-prime base. Resolve the ordered interval guards. -/
theorem refinedSelected_eq_before101 {n : ℕ} (hL : 63 ≤ Real.log n) (hU : Real.log n < 101) :
    refinedSelectedEnvelope n =
      min (lowPrimeTightSelected n)
        (min (Analysis.gaussianRecoveredBound (Real.log n))
          (Analysis.gaussianRecoveredSeeded (Real.log n))) := by
  simp only [refinedSelectedEnvelope, refinedGuardSelected, ite_eq_right (not_lt.mpr hL),
    ite_eq_left hU]

/-- From scale 101 up to 1.1 trillion, Gamma joins the two valid Gaussian
candidates. The interval formula contains no triangular candidate before its certified entrance. -/
theorem refinedSelected_eq_analytic {n : ℕ} (hL : 101 ≤ Real.log n)
    (hU : Real.log n < 1100000000000) :
    refinedSelectedEnvelope n =
      min (lowPrimeTightSelected n)
        (min (Analysis.gaussianRecoveredBound (Real.log n))
          (min (gammaRecoveredBound (Real.log n))
            (Analysis.gaussianRecoveredSeeded (Real.log n)))) := by
  have h63 : ¬Real.log n < 63 := by linarith only [hL]
  simp only [refinedSelectedEnvelope, refinedGuardSelected, ite_eq_right h63,
    ite_eq_right (not_lt.mpr hL), ite_eq_left hU]

/-- From scale 1.1 trillion up to two trillion, the coefficient-0.284 candidate
joins the three analytic candidates. Resolve only certified entrances, retaining valid minima. -/
theorem refinedSelected_eq_earlier {n : ℕ} (hL : 1100000000000 ≤ Real.log n)
    (hU : Real.log n < 2000000000000) :
    refinedSelectedEnvelope n =
      min (lowPrimeTightSelected n)
        (min (Analysis.gaussianRecoveredBound (Real.log n))
          (min (gammaRecoveredBound (Real.log n))
            (min (Analysis.gaussianRecoveredSeeded (Real.log n))
              ((71 / 250) * Real.log n ^ 2)))) := by
  have h63 : ¬Real.log n < 63 := by linarith only [hL]
  have h101 : ¬Real.log n < 101 := by linarith only [hL]
  simp only [refinedSelectedEnvelope, refinedGuardSelected, ite_eq_right h63, ite_eq_right h101,
    ite_eq_right (not_lt.mpr hL), ite_eq_left hU]

/-- At scales at least two trillion, keep the sharper triangular coefficient
0.28237 and remove its dominated coefficient-0.284 companion. The square of the
logarithm is nonnegative, so the coefficient comparison is valid throughout the half-line. -/
theorem refinedSelected_eq_high {n : ℕ} (hL : 2000000000000 ≤ Real.log n) :
    refinedSelectedEnvelope n =
      min (lowPrimeTightSelected n)
        (min (Analysis.gaussianRecoveredBound (Real.log n))
          (min (gammaRecoveredBound (Real.log n))
            (min (Analysis.gaussianRecoveredSeeded (Real.log n))
              ((28237 / 100000) * Real.log n ^ 2)))) := by
  have h63 : ¬Real.log n < 63 := by linarith only [hL]
  have h101 : ¬Real.log n < 101 := by linarith only [hL]
  have he : ¬Real.log n < 1100000000000 := by linarith only [hL]
  have hcoef : (28237 / 100000 : ℝ) * Real.log n ^ 2 ≤ (71 / 250) * Real.log n ^ 2 := by
    nlinarith only [sq_nonneg (Real.log n)]
  simp only [refinedSelectedEnvelope, refinedGuardSelected, ite_eq_right h63, ite_eq_right h101,
    ite_eq_right he, ite_eq_right (not_lt.mpr hL), min_eq_right hcoef]

/-- On every old-open to new-closed low-prime cap interval, the refined
selection strictly improves the fixed baseline for inputs at least 3000. Project
to the tight low-prime envelope and use its continuous strict comparison. -/
theorem refinedSelected_low_strict (f : LLS.PaperStatements.LowPrimeProfile) {n : ℕ} (hn : 1 < n)
    (hN : 3000 ≤ n) (hL : (f.logCap : ℝ) < Real.log n) (hU : Real.log n ≤ f.tightLogCap) :
    refinedSelectedEnvelope n < nextSelectedEnvelope n := by
  rw [← refined_eq_selected hn]
  exact (refinedWitnessEnvelope_le_low n).trans_lt (lowPrimeTight_strict f hn hN hL hU)

/-- On the full logarithmic interval [108,126], the refined selection strictly
improves the fixed baseline. The Gamma guard is active and its recovered cutoff
strictly improves every surviving baseline candidate. -/
theorem refinedSelected_gamma_strict {n : ℕ} (hn : 1 < n) (hL : 108 ≤ Real.log n)
    (hU : Real.log n ≤ 126) : refinedSelectedEnvelope n < nextSelectedEnvelope n := by
  rw [← refined_eq_selected hn]
  exact
    (refined_le_gamma (by linarith only [hL])).trans_lt (gammaRecovered_lt_nextSelected hn hL hU)

/-- On the full logarithmic interval [132,235], the refined selection strictly
improves the fixed baseline. Project to the recovered single-root Gaussian cutoff
and use its continuous strict comparison. -/
theorem refinedSelected_gaussian_strict {n : ℕ} (hn : 1 < n) (hL : 132 ≤ Real.log n)
    (hU : Real.log n ≤ 235) : refinedSelectedEnvelope n < nextSelectedEnvelope n := by
  rw [← refined_eq_selected hn]
  exact (refined_le_gaussian (by linarith only [hL])).trans_lt (gaussianRecovered_lt_next hn hL hU)

/-- Before the old triangular entrance, both varying baseline seeded regions
strictly improve under the refined selection. The exact switch hypotheses exclude
plateaus, and imply the certified seeded entrance. -/
theorem refinedSelected_seeded_strict {n : ℕ} (hn : 1 < n) (hU : Real.log n < 1500000000000)
    (hstrict :
      (Analysis.gaussianSeededSwitch false 35000 < Real.log n ∧
          Real.log n < Analysis.gaussianSeededSwitch false 50000) ∨
        Analysis.gaussianSeededSwitch true 50000 < Real.log n) :
    refinedSelectedEnvelope n < nextSelectedEnvelope n := by
  have h63 : (63 : ℝ) ≤ Real.log n := by
    rcases hstrict with h | h
    · linarith only [h.1, Analysis.gaussianSeeded_switch35_bounds.1]
    · linarith only [h, (Analysis.gaussianSeeded_switch50_bounds true).1]
  rw [← refined_eq_selected hn]
  exact (refined_le_seeded h63).trans_lt (recoveredSeeded_lt_nextSelected hn hU hstrict)

/-- From logarithmic scale 1.1 trillion up to 1.5 trillion, the refined selection
strictly improves the fixed baseline. Project to the newly available triangular
cutoff and use its continuous comparison with the old seeded branch. -/
theorem refinedSelected_earlier_strict {n : ℕ} (hn : 1 < n) (hL : (1100000000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n < 1500000000000) : refinedSelectedEnvelope n < nextSelectedEnvelope n := by
  rw [← refined_eq_selected hn]
  exact (refined_le_earlier hL).trans_lt (triangularEarlier_lt_nextSelected hn hL hU)

/-- At logarithmic scales at least two trillion, the refined selection strictly
improves the fixed baseline. The rational coefficient decreases from 0.2827
to 0.28237 on a strictly positive logarithm square. -/
theorem refinedSelected_triangular_strict {n : ℕ} (hn : 1 < n)
    (hL : (2000000000000 : ℝ) ≤ Real.log n) :
    refinedSelectedEnvelope n < nextSelectedEnvelope n := by
  rw [← refined_eq_selected hn]
  exact (refined_le_triangular hL).trans_lt (triangularRefined_lt_nextSelected hn hL)

/-- For inputs above one, the rounded refined cutoff is no larger than the
fixed baseline selection. Compose rounding and analytic non-worsening. -/
theorem refinedPrime_le_nextSelected {n : ℕ} (hn : 1 < n) :
    refinedPrimeEnvelope n ≤ nextSelectedEnvelope n := by
  exact (refinedPrime_le_selected hn).trans (refinedSelected_le_next hn)

/-- Below 2047, the refined numerical selection retains the value two.
Resolve the preserved small-interval definition; no primality assumption is needed. -/
theorem refinedSelected_small_two {n : ℕ} (hN : n < 2047) : refinedSelectedEnvelope n = 2 := by
  rw [refinedSelected_eq_small (hN.trans (by norm_num only : 2047 < 3000))]
  exact ite_eq_left hN

/-- For 2047 through 2999, the refined numerical selection retains the value
three. This includes inputs strictly above 2047 and preserves the requested public interval. -/
theorem refinedSelected_small_three {n : ℕ} (hL : 2047 ≤ n) (hU : n < 3000) :
    refinedSelectedEnvelope n = 3 := by
  rw [refinedSelected_eq_small hU]
  exact ite_eq_right (not_lt.mpr hL)

/-- For inputs above one and below 2047, the rounded refined cutoff remains
two because the preserved small-interval constant is already prime. -/
theorem refinedPrime_small_two {n : ℕ} (hn : 1 < n) (hN : n < 2047) :
    refinedPrimeEnvelope n = 2 := by
  rw [refinedPrime_eq_small hn (hN.trans (by norm_num only : 2047 < 3000))]
  exact ite_eq_left hN

/-- For 2047 through 2999, the rounded refined cutoff remains three.
Use preservation of the small-interval bound and its upper branch. -/
theorem refinedPrime_small_three {n : ℕ} (hL : 2047 ≤ n) (hU : n < 3000) :
    refinedPrimeEnvelope n = 3 := by
  have hn : 1 < n := (by norm_num only : 1 < 2047).trans_le hL
  rw [refinedPrime_eq_small hn hU]
  exact ite_eq_right (not_lt.mpr hL)

end PseudoPrime.PrimeTestBounds.MillerRabin

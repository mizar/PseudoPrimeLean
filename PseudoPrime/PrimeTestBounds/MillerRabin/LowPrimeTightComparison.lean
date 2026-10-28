/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointLowPrimeTight
public import PseudoPrime.PrimeTestBounds.MillerRabin.NextIntervalSelection

/-! # Strict low-prime improvement over the current envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For every profile, its bound strictly improves the current selected envelope
between the old open cap and the new closed cap, for inputs at least 3000. Resolve the
current low-prime selection, using the fixed-61 branch for the final profile. -/
theorem lowPrimeTight_lt_next (f : LLS.PaperStatements.LowPrimeProfile) {n : ℕ} (hn : 1 < n)
    (hN : 3000 ≤ n) (hL : (f.logCap : ℝ) < Real.log n) (hU : Real.log n ≤ f.tightLogCap) :
    (f.bound : ℝ) < nextSelectedEnvelope n := by
  have hsmall : ¬n < 3000 := not_lt.mpr hN
  cases f
  · norm_num only [LLS.PaperStatements.LowPrimeProfile.logCap,
      LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div, Rat.cast_ofNat] at hL hU
    rw [← next_eq_selected hn, next_eq_low (by linarith only [hU]), lowPrime_eq_selected hn]
    simp only [lowPrimeSelected, ite_eq_right hsmall,
      ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 401 / 50),
      ite_eq_left (by linarith only [hU] : Real.log n ≤ 413 / 50)]
    norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
  · norm_num only [LLS.PaperStatements.LowPrimeProfile.logCap,
      LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div, Rat.cast_ofNat] at hL hU
    rw [← next_eq_selected hn, next_eq_low (by linarith only [hU]), lowPrime_eq_selected hn]
    simp only [lowPrimeSelected, ite_eq_right hsmall,
      ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 401 / 50),
      ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 413 / 50),
      ite_eq_left (by linarith only [hU] : Real.log n ≤ 893 / 100)]
    norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
  · norm_num only [LLS.PaperStatements.LowPrimeProfile.logCap,
      LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div, Rat.cast_ofNat] at hL hU
    rw [← next_eq_selected hn, next_eq_low (by linarith only [hU]), lowPrime_eq_selected hn]
    simp only [lowPrimeSelected, ite_eq_right hsmall,
      ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 401 / 50),
      ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 413 / 50),
      ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 893 / 100),
      ite_eq_left (by linarith only [hU] : Real.log n ≤ 933 / 100)]
    norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
  · norm_num only [LLS.PaperStatements.LowPrimeProfile.logCap,
      LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div, Rat.cast_ofNat] at hL hU
    rw [← next_eq_selected hn, next_eq_low (by linarith only [hU]), lowPrime_eq_selected hn]
    simp only [lowPrimeSelected, ite_eq_right hsmall,
      ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 401 / 50),
      ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 413 / 50),
      ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 893 / 100),
      ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 933 / 100),
      ite_eq_left (by linarith only [hU] : Real.log n ≤ 238 / 25)]
    norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
  · norm_num only [LLS.PaperStatements.LowPrimeProfile.logCap,
      LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div, Rat.cast_ofNat] at hL hU
    rw [← next_eq_selected hn, next_eq_low (by linarith only [hU]), lowPrime_eq_selected hn]
    simp only [lowPrimeSelected, ite_eq_right hsmall,
      ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 401 / 50),
      ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 413 / 50),
      ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 893 / 100),
      ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 933 / 100),
      ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 238 / 25),
      ite_eq_left (by linarith only [hU] : Real.log n ≤ 989 / 100)]
    norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
  · norm_num only [LLS.PaperStatements.LowPrimeProfile.logCap,
      LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div, Rat.cast_ofNat] at hL hU
    rw [← next_eq_selected hn, next_eq_low (by linarith only [hU]), lowPrime_eq_selected hn]
    simp only [lowPrimeSelected, ite_eq_right hsmall,
      ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 401 / 50),
      ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 413 / 50),
      ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 893 / 100),
      ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 933 / 100),
      ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 238 / 25),
      ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 989 / 100),
      ite_eq_left (by linarith only [hU] : Real.log n ≤ 521 / 50)]
    norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
  · norm_num only [LLS.PaperStatements.LowPrimeProfile.logCap,
      LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div, Rat.cast_ofNat] at hL hU
    rw [← next_eq_selected hn, next_eq_low (by linarith only [hU]), lowPrime_eq_selected hn]
    simp only [lowPrimeSelected, ite_eq_right hsmall,
      ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 401 / 50),
      ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 413 / 50),
      ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 893 / 100),
      ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 933 / 100),
      ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 238 / 25),
      ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 989 / 100),
      ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 521 / 50),
      ite_eq_left (by linarith only [hU] : Real.log n ≤ 109 / 10)]
    norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
  · norm_num only [LLS.PaperStatements.LowPrimeProfile.logCap,
      LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div, Rat.cast_ofNat] at hL hU
    rw [← next_eq_selected hn, next_eq_low (by linarith only [hU]), lowPrime_eq_selected hn]
    simp only [lowPrimeSelected, ite_eq_right hsmall,
      ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 401 / 50),
      ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 413 / 50),
      ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 893 / 100),
      ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 933 / 100),
      ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 238 / 25),
      ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 989 / 100),
      ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 521 / 50),
      ite_eq_right (by linarith only [hL] : ¬Real.log n ≤ 109 / 10),
      ite_eq_left (by linarith only [hU] : Real.log n ≤ 553 / 50)]
    norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]
  · norm_num only [LLS.PaperStatements.LowPrimeProfile.logCap,
      LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div, Rat.cast_ofNat] at hL hU
    rw [← next_eq_selected hn, next_eq_fixed61 hn hN hL (by linarith only [hU])]
    norm_num only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat]

end PseudoPrime.PrimeTestBounds.MillerRabin

/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.ImprovedFixedRadius

/-! # Strict improvement intervals for fixed triangular profiles -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A common lower bound for the old high-window candidate and the variable branches bounds the
mean selection. -/
theorem fixedMean_lower {n : ℕ} {C : ℝ} (hL : (80000 : ℝ) ≤ Real.log n) (hC : C ≤ 2 / 5)
    (hprev : C * Real.log n ^ 2 ≤ highWindowExtended n) : C * Real.log n ^ 2 ≤ meanSelected n := by
  have h70 : (70000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hu := high_log_twice_ge_22 h70
  have hpair := pairedAlpha_ge_653 hu
  have hfac := (factorialAlpha_bounds hu).1
  have hpair2 : C ≤ (pairedAlpha (2 * Real.log (Real.log n))) ^ 2 := by
    nlinarith only [hC, hpair, sq_nonneg (pairedAlpha (2 * Real.log (Real.log n)) - 653 / 1000)]
  have hfac2 : C ≤ (factorialAlpha (2 * Real.log (Real.log n))) ^ 2 := by
    nlinarith only [hC, hfac, sq_nonneg (factorialAlpha (2 * Real.log (Real.log n)) - 647 / 1000)]
  rw [meanSelected, ite_eq_left hL, factorialSelected, ite_eq_left hL, pairedSelected,
    ite_eq_left h70]
  refine le_min (le_min (le_min hprev ?_) ?_) ?_
  · exact mul_le_mul_of_nonneg_right hpair2 (sq_nonneg _)
  · exact mul_le_mul_of_nonneg_right hfac2 (sq_nonneg _)
  · nlinarith only [hC, sq_nonneg (Real.log n)]

/-- A fixed profile strictly improves the old selection when both its mean and triangular bounds
are strict. -/
theorem fixedProfile_strict (f : TriangularProfile) {n : ℕ} (hL : f.T ≤ Real.log n)
    (hU : Real.log n < 2000000000000) (hmean : f.C * Real.log n ^ 2 < meanSelected n)
    (hrad : f.C < triangularAdaptiveRadius (Real.log n) ^ 2) :
    fixedProfileSelected f n < gaussianAdaptiveSelected n := by
  have h30 : (30000000000 : ℝ) ≤ Real.log n := f.entry.trans hL
  have hs : 0 < Real.log n ^ 2 := sq_pos_of_pos (by linarith only [h30])
  have hr := mul_lt_mul_of_pos_right hrad hs
  have hh : f.C * Real.log n ^ 2 < triangularAdaptiveSelected n := by
    rw [triangularAdaptiveSelected, ite_eq_left h30]
    exact lt_min hmean hr
  rw [gaussianAdaptiveSelected_eq hU] at ⊢
  rw [fixedProfileSelected, ite_eq_left hL, gaussianAdaptiveSelected_eq hU]
  exact (min_le_right _ _).trans_lt hh

/-- On the first window, all preceding mean-envelope candidates exceed the two-fifths bound. -/
theorem fixedMean_lower_04 {n : ℕ} (hL : (50000000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n < 60000000000) : (2 / 5 : ℝ) * Real.log n ^ 2 ≤ meanSelected n := by
  have h30 : (30000000000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h40 : (40000000000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h45 : (45000000000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h70 : (70000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h80 : (80000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h100 : Real.log n < 100000000000 := by linarith only [hU]
  have hN := large_of_log63 h63
  have hs : 0 < Real.log n ^ 2 := sq_pos_of_pos (by linarith only [hL])
  have hB : (4145 / 10000 : ℝ) * Real.log n ^ 2 ≤ tunedFiniteSelected n := by
    rw [tunedFinite_eq_high_window h40 h100]
    nlinarith only [hs]
  have hc := highCoeff_lower_of_finite h70 h100 hB
  have hprev : (2 / 5 : ℝ) * Real.log n ^ 2 ≤ highWindowExtended n := by
    rw [highWindowExtended_eq_of_log_lt (by linarith only [hU]), highWindowSelected,
      ite_eq_right (not_lt.mpr hN),
      ite_eq_right (by linarith only [hU] : ¬(80000000000 : ℝ) ≤ Real.log n),
      ite_eq_right (not_le_of_gt hU), ite_eq_left h45]
    exact le_min (by nlinarith only [hc, hs]) le_rfl
  exact fixedMean_lower h80 (by norm_num only) hprev

/-- On the second window, the preceding mean envelope retains the coefficient `369 / 1000`. -/
theorem fixedMean_lower_0369 {n : ℕ} (hL : (70000000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n < 80000000000) : (369 / 1000 : ℝ) * Real.log n ^ 2 ≤ meanSelected n := by
  have h40 : (40000000000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h60 : (60000000000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h70 : (70000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h80 : (80000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h100 : Real.log n < 100000000000 := by linarith only [hU]
  have hN := large_of_log63 h63
  have hs : 0 < Real.log n ^ 2 := sq_pos_of_pos (by linarith only [hL])
  have hB : (4145 / 10000 : ℝ) * Real.log n ^ 2 ≤ tunedFiniteSelected n := by
    rw [tunedFinite_eq_high_window h40 h100]
    nlinarith only [hs]
  have hc := highCoeff_lower_of_finite h70 h100 hB
  have hprev : (369 / 1000 : ℝ) * Real.log n ^ 2 ≤ highWindowExtended n := by
    rw [highWindowExtended_eq_of_log_lt (by linarith only [hU]), highWindowSelected,
      ite_eq_right (not_lt.mpr hN), ite_eq_right (not_le_of_gt hU), ite_eq_left h60]
    exact le_min (by nlinarith only [hc, hs]) le_rfl
  exact fixedMean_lower h80 (by norm_num only) hprev

/-- On the third window, the preceding mean envelope retains the coefficient `323 / 1000`. -/
theorem fixedMean_lower_0323 {n : ℕ} (hL : (150000000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n < 250000000000) : (323 / 1000 : ℝ) * Real.log n ^ 2 ≤ meanSelected n := by
  have h80 : (80000000000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hn : 1 < n := lt_of_lt_of_le (by norm_num only) (large_of_log63 h63)
  have hstart : (100000000000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hs : 0 < Real.log n ^ 2 := sq_pos_of_pos (by linarith only [hL])
  have heq := tunedFinite_eq_stage 2 hn hstart hU
  change tunedFiniteSelected n = (1 / 3 : ℝ) * Real.log n ^ 2 at heq
  have hB : (3315 / 10000 : ℝ) * Real.log n ^ 2 ≤ tunedFiniteSelected n := by
    rw [heq]
    nlinarith only [hs]
  have hold := highWindow_lower_of_tuned h80 (by norm_num only) (tunedHigh_lower_03315 hU hB)
  have h120 : (120000000000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h300 : ¬(300000000000 : ℝ) ≤ Real.log n := by linarith only [hU]
  have h600 : ¬(600000000000 : ℝ) ≤ Real.log n := by linarith only [hU]
  have hprev : (323 / 1000 : ℝ) * Real.log n ^ 2 ≤ highWindowExtended n := by
    rw [highWindowExtended, ite_eq_right h600, ite_eq_right h300, ite_eq_left h120]
    exact le_min (by nlinarith only [hold, hs]) le_rfl
  exact fixedMean_lower (by linarith only [hL]) (by norm_num only) hprev

/-- On the first certified interval, the fixed-profile selection strictly improves the preceding
envelope. -/
theorem fixedImproved_lt_03869 {n : ℕ} (hL : (50000000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 50400000000) : fixedImprovedSelected n < gaussianAdaptiveSelected n := by
  have hs : 0 < Real.log n ^ 2 := sq_pos_of_pos (by linarith only [hL])
  have hm := fixedMean_lower_04 hL (show Real.log n < 60000000000 by linarith only [hU])
  have hp : (improvedProfile03869).C * Real.log n ^ 2 < meanSelected n := by
    change (3869 / 10000 : ℝ) * Real.log n ^ 2 < meanSelected n
    nlinarith only [hm, hs]
  have hr : (improvedProfile03869).C < triangularAdaptiveRadius (Real.log n) ^ 2 := by
    exact fixed_radius_03869 hL hU
  have hh :=
    fixedProfile_strict improvedProfile03869 hL
      (show Real.log n < 2000000000000 by linarith only [hU]) hp hr
  exact (min_le_left _ _).trans_lt hh

/-- On the second certified interval, the fixed-profile selection strictly improves the
preceding envelope. -/
theorem fixedImproved_lt_03552 {n : ℕ} (hL : (70000000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 70400000000) : fixedImprovedSelected n < gaussianAdaptiveSelected n := by
  have hs : 0 < Real.log n ^ 2 := sq_pos_of_pos (by linarith only [hL])
  have hm := fixedMean_lower_0369 hL (show Real.log n < 80000000000 by linarith only [hU])
  have hp : (improvedProfile03552).C * Real.log n ^ 2 < meanSelected n := by
    change (222 / 625 : ℝ) * Real.log n ^ 2 < meanSelected n
    nlinarith only [hm, hs]
  have hr : (improvedProfile03552).C < triangularAdaptiveRadius (Real.log n) ^ 2 := by
    exact fixed_radius_03552 hL hU
  have hh :=
    fixedProfile_strict improvedProfile03552 hL
      (show Real.log n < 2000000000000 by linarith only [hU]) hp hr
  exact ((min_le_right _ _).trans (min_le_left _ _)).trans_lt hh

/-- On the third certified interval, the fixed-profile selection strictly improves the preceding
envelope. -/
theorem fixedImproved_lt_03134 {n : ℕ} (hL : (150000000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 150100000000) : fixedImprovedSelected n < gaussianAdaptiveSelected n := by
  have hs : 0 < Real.log n ^ 2 := sq_pos_of_pos (by linarith only [hL])
  have hm := fixedMean_lower_0323 hL (show Real.log n < 250000000000 by linarith only [hU])
  have hp : (improvedProfile03134).C * Real.log n ^ 2 < meanSelected n := by
    change (1567 / 5000 : ℝ) * Real.log n ^ 2 < meanSelected n
    nlinarith only [hm, hs]
  have hr : (improvedProfile03134).C < triangularAdaptiveRadius (Real.log n) ^ 2 := by
    exact fixed_radius_03134 hL hU
  have hh :=
    fixedProfile_strict improvedProfile03134 hL
      (show Real.log n < 2000000000000 by linarith only [hU]) hp hr
  exact ((min_le_right _ _).trans (min_le_right _ _)).trans_lt hh

/-- The fixed-profile selection never exceeds the preceding Gaussian selection. -/
theorem fixedImprovedSelected_le (n : ℕ) :
    fixedImprovedSelected n ≤ gaussianAdaptiveSelected n := by
  have hh : fixedProfileSelected improvedProfile03869 n ≤ gaussianAdaptiveSelected n := by
    by_cases h : improvedProfile03869.T ≤ Real.log n
    · rw [fixedProfileSelected, ite_eq_left h]
      exact min_le_left _ _
    · rw [fixedProfileSelected, ite_eq_right h]
  exact (min_le_left _ _).trans hh

/-- Both fixed-profile cutoffs retain the value three on the specified small interval. -/
theorem fixedImproved_small_three {n : ℕ} (hl : 2047 ≤ n) (hu : n < 3000) :
    fixedImprovedSelected n = 3 ∧ fixedImprovedPrime n = 3 := by
  have hlog : Real.log n < 30000000000 := lt_trans (log_lt63_of_small hu) (by norm_num only)
  have hp (f : TriangularProfile) : fixedProfileSelected f n = gaussianAdaptiveSelected n := by
    rw [fixedProfileSelected, ite_eq_right (by linarith only [hlog, f.entry])]
  have hg := (gaussianAdaptive_small_three hl hu).1
  have he : fixedImprovedSelected n = 3 := by
    rw [fixedImprovedSelected, hp, hp, hp, min_self, min_self, hg]
  refine ⟨he, ?_⟩
  rw [fixedImprovedPrime, he]
  simpa only [Nat.cast_ofNat] using primeRound_prime (by decide +kernel : Nat.Prime 3)

/-- The fixed-profile selection is monotone on the small interval because it is constant there. -/
theorem fixedImproved_small_mono : MonotoneOn fixedImprovedSelected (Set.Ico 2047 3000) := by
  intro m hm n hn _
  have hm' : fixedImprovedSelected m = 3 := (fixedImproved_small_three hm.1 hm.2).1
  have hn' : fixedImprovedSelected n = 3 := (fixedImproved_small_three hn.1 hn.2).1
  rw [hm', hn']

end PseudoPrime.PrimeTestBounds.MillerRabin

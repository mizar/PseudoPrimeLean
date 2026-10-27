/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.AdaptiveReciprocalRadius

/-! # Strict logarithmic-square comparison for the adaptive radius -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a reference root between 36/5 and 21/2.
Claim: the bridge reciprocal loss is at most 1961/1250.
Proof: bound both reciprocal denominators at the interval endpoints.
Role: improve the low part of the strict log-square comparison. -/
theorem reciprocalLossBridge_le_small_cap {t : ℝ} (ht : (36 / 5 : ℝ) ≤ t) (hupper : t ≤ 21 / 2) :
    reciprocalLossBridge t ≤ (1961 / 1250 : ℝ) := by
  have htpos : 0 < t := by linarith only [ht]
  have hp :=
    div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 231 / 5000)
      (by norm_num only : (0 : ℝ) < 31 / 5) (show (31 / 5 : ℝ) ≤ t - 1 by linarith only [ht])
  have hn :=
    div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 16033 / 9000) (sq_pos_of_pos htpos)
      (show t ^ 2 ≤ (21 / 2 : ℝ) ^ 2 by nlinarith only [hupper, htpos])
  dsimp only [reciprocalLossBridge]
  linarith only [hp, hn]

/-- Input: level at least 6.39 and log level at least 2.27.
Claim: the adaptive root is strictly below the level.
Proof: retain the sharper bridge cap below level ten and use the old root bound above it.
Role: prove one global comparison for the same explicit adaptive radius. -/
theorem adaptivePart2Root_lt_level_of_log_entrance {L : ℝ} (hentry : (639 / 100 : ℝ) ≤ L)
    (hlogL : (227 / 100 : ℝ) ≤ Real.log L) : adaptivePart2CutoffRoot L < L := by
  have ht := finerPart2Root_ge_thirty_six_fifths_of_639_div_100_le hentry
  have ht7 : 7 ≤ finerPart2CutoffRoot L := le_trans (by norm_num only) ht
  by_cases h10 : L ≤ 10
  · have htupper : finerPart2CutoffRoot L ≤ (21 / 2 : ℝ) := by
      dsimp only [finerPart2CutoffRoot]
      linarith only [h10, hlogL]
    have hb := reciprocalLossBridge_le_small_cap ht htupper
    have he : finerPart2CutoffRoot L = L - 2 * Real.log L + 45571 / 10000 := rfl
    dsimp only [adaptivePart2CutoffRoot]
    linarith only [hb, he, hlogL]
  · have hc : rationalLogIntervalCheck 10 3 10 (23 / 10) (231 / 100) = true := by decide +kernel
    have hl := (rationalLogIntervalCheck_sound hc).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
    have hm := Real.log_le_log (by norm_num only : (0 : ℝ) < 10) (le_of_not_ge h10)
    have hf : finerPart2CutoffRoot L < L := by
      dsimp only [finerPart2CutoffRoot]
      linarith only [hl, hm]
    exact (adaptivePart2Root_bounds ht7).2.trans hf

/-- Input: a modulus at least 16000. Claim: its logarithm is at least 242/25.
Proof: certify the endpoint logarithm and use monotonicity.
Role: supply the lower level for the improved strict comparison. -/
theorem log_level_ge_adaptive_strict_entrance {q : ℕ} (hq : 16000 ≤ q) :
    (242 / 25 : ℝ) ≤ Real.log q := by
  have hc : rationalLogIntervalCheck 16000 14 12 (242 / 25) (969 / 100) = true := by decide +kernel
  have hl := (rationalLogIntervalCheck_sound hc).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
  exact hl.trans (Real.log_le_log (by norm_num only) (Nat.cast_le.mpr hq))

/-- Input: a modulus at least 16000. Claim: its double logarithm is at least 227/100.
Proof: certify the logarithm of the previous lower endpoint.
Role: discharge the adaptive root comparison without modulus enumeration. -/
theorem log_log_level_ge_adaptive_strict_entrance {q : ℕ} (hq : 16000 ≤ q) :
    (227 / 100 : ℝ) ≤ Real.log (Real.log q) := by
  have hc : rationalLogIntervalCheck (242 / 25) 3 12 (227 / 100) (228 / 100) = true := by
    decide +kernel
  have hl := (rationalLogIntervalCheck_sound hc).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
  exact hl.trans (Real.log_le_log (by norm_num only) (log_level_ge_adaptive_strict_entrance hq))

/-- Input: a modulus at least 16000.
Claim: the adaptive squared radius is strictly below the squared level logarithm.
Proof: compare the positive root to the level using the certified logarithmic entrances.
Role: lower the same-witness log-square comparison entrance from 17400 to 16000. -/
theorem adaptivePart2Root_sq_lt_log_sq_of_16000_le {q : ℕ} (hq : 16000 ≤ q) :
    (adaptivePart2CutoffRoot (Real.log q)) ^ 2 < (Real.log q) ^ 2 := by
  have hentry :=
    log_level_ge_adaptivePart2_entrance (le_trans (by norm_num only : (600 : ℕ) ≤ 16000) hq)
  have ht := finerPart2Root_ge_thirty_six_fifths_of_639_div_100_le hentry
  have hypos := (adaptivePart2Root_height_and_cutoff ht).1
  exact
    (sq_lt_sq₀ (by linarith only [hypos]) (by linarith only [hentry])).mpr
      (adaptivePart2Root_lt_level_of_log_entrance hentry
        (log_log_level_ge_adaptive_strict_entrance hq))

end PseudoPrime.Analysis

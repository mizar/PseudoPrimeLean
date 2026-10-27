/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FinerPart2CutoffBounds

/-! # Low-scale reciprocal obstruction for the finer Part 2 root -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a positive logarithmic level.
Claim: the finer Part 2 root is at least 5.1571 on the whole positive half-line.
Proof: apply the logarithm tangent at two and the upper bound for log two.
Role: obtain a uniform small-scale cutoff without a finite modulus table. -/
theorem finerPart2Root_ge_51571_div_10000 {L : ℝ} (hL : 0 < L) :
    (51571 / 10000 : ℝ) ≤ finerPart2CutoffRoot L := by
  have ht := log_le_log_add_sub_div (a := (2 : ℝ)) (y := L) (by norm_num only) hL
  dsimp only [finerPart2CutoffRoot]
  linarith only [ht, Real.log_two_lt_d9]

/-- Input: a positive logarithmic level.
Claim: the finer squared root is at least 53/2.
Proof: square the uniform positive root lower bound.
Role: supply the low reciprocal main-error regime. -/
theorem finerPart2Root_sq_ge_twenty_six_half {L : ℝ} (hL : 0 < L) :
    (53 / 2 : ℝ) ≤ (finerPart2CutoffRoot L) ^ 2 := by
  have ht := finerPart2Root_ge_51571_div_10000 hL
  nlinarith only [ht]

/-- Input: two ordered positive levels.
Claim: the root increment is at most the level increment.
Proof: the logarithmic correction is nondecreasing.
Role: control the logarithm of the root without differentiation. -/
theorem finerPart2Root_sub_le_level_sub {L₁ L₂ : ℝ} (h₁ : 0 < L₁) (h₁₂ : L₁ ≤ L₂) :
    finerPart2CutoffRoot L₂ - finerPart2CutoffRoot L₁ ≤ L₂ - L₁ := by
  have hl := Real.log_le_log h₁ h₁₂
  dsimp only [finerPart2CutoffRoot]
  linarith only [hl]

/-- Input: two ordered positive levels.
Claim: the log-root increment is at most one fifth of the level increment.
Proof: use the logarithm tangent, root increment bound, and root height above five.
Role: prove monotonicity of the reciprocal-only comparison. -/
theorem log_finerPart2Root_sub_le_fifth {L₁ L₂ : ℝ} (h₁ : 0 < L₁) (h₁₂ : L₁ ≤ L₂) :
    Real.log (finerPart2CutoffRoot L₂) - Real.log (finerPart2CutoffRoot L₁) ≤ (L₂ - L₁) / 5 := by
  have ht₁ := finerPart2Root_ge_51571_div_10000 h₁
  have ht₂ := finerPart2Root_ge_51571_div_10000 (h₁.trans_le h₁₂)
  have hp₁ : 0 < finerPart2CutoffRoot L₁ := by linarith only [ht₁]
  have hp₂ : 0 < finerPart2CutoffRoot L₂ := by linarith only [ht₂]
  have ht := log_le_log_add_sub_div hp₁ hp₂
  have hd := finerPart2Root_sub_le_level_sub h₁ h₁₂
  calc
    _ ≤ (finerPart2CutoffRoot L₂ - finerPart2CutoffRoot L₁) / finerPart2CutoffRoot L₁ := by
      linarith only [ht]
    _ ≤ (L₂ - L₁) / finerPart2CutoffRoot L₁ := div_le_div_of_nonneg_right hd hp₁.le
    _ ≤ (L₂ - L₁) / 5 :=
      div_le_div_of_nonneg_left (sub_nonneg.mpr h₁₂) (by norm_num only) (by linarith only [ht₁])

/-- Input: a logarithmic level.
Output: the reciprocal-only necessary-condition gap with the inverse-square factor dropped.
Role: give a monotone scalar obstruction on the low analytic range. -/
noncomputable def finerPart2ReciprocalOnlyGap (L : ℝ) : ℝ :=
  (1 / 2) * (L - 2096 / 1831) - 2 * Real.log (finerPart2CutoffRoot L) + 31551 / 20000 - 1 / 4

/-- Input: two ordered positive levels.
Claim: the reciprocal-only gap is nondecreasing.
Proof: its linear increase exceeds twice the log-root increment bound.
Role: reduce the whole low interval to its right endpoint. -/
theorem finerPart2ReciprocalOnlyGap_mono {L₁ L₂ : ℝ} (h₁ : 0 < L₁) (h₁₂ : L₁ ≤ L₂) :
    finerPart2ReciprocalOnlyGap L₁ ≤ finerPart2ReciprocalOnlyGap L₂ := by
  have h := log_finerPart2Root_sub_le_fifth h₁ h₁₂
  dsimp only [finerPart2ReciprocalOnlyGap]
  linarith only [h, h₁₂]

/-- Claim: the reciprocal-only gap is negative at log 500.
Proof: check three rational logarithm intervals and combine their endpoint bounds.
Role: certify the low-range analytic endpoint without enumerating moduli. -/
theorem finerPart2ReciprocalOnlyGap_log_five_hundred_neg :
    finerPart2ReciprocalOnlyGap (Real.log 500) < 0 := by
  have hc : rationalLogIntervalCheck 500 9 10 (621 / 100) (622 / 100) = true := by decide +kernel
  have hl := rationalLogIntervalCheck_sound hc
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
  have hc₂ : rationalLogIntervalCheck (622 / 100) 3 10 (182 / 100) (183 / 100) = true := by
    decide +kernel
  have h₂ := (rationalLogIntervalCheck_sound hc₂).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h₂
  have hlog := Real.log_le_log (show 0 < Real.log 500 by linarith only [hl.1]) hl.2
  have ht : (71 / 10 : ℝ) ≤ finerPart2CutoffRoot (Real.log 500) := by
    dsimp only [finerPart2CutoffRoot]
    linarith only [hl.1, hlog, h₂]
  have hc₃ : rationalLogIntervalCheck (71 / 10) 3 10 (196 / 100) (197 / 100) = true := by
    decide +kernel
  have h₃ := (rationalLogIntervalCheck_sound hc₃).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h₃
  have hlogt := Real.log_le_log (by norm_num only : (0 : ℝ) < 71 / 10) ht
  dsimp only [finerPart2ReciprocalOnlyGap]
  linarith only [hl.2, h₃, hlogt]

/-- Input: a positive logarithmic level at most log 500.
Claim: its reciprocal-only gap is strictly negative.
Proof: apply monotonicity and the certified endpoint obstruction.
Role: close the scalar low-range contradiction. -/
theorem finerPart2ReciprocalOnlyGap_neg_of_le_five_hundred {L : ℝ} (hL : 0 < L)
    (hupper : L ≤ Real.log 500) : finerPart2ReciprocalOnlyGap L < 0 := by
  exact
    (finerPart2ReciprocalOnlyGap_mono hL hupper).trans_lt
      finerPart2ReciprocalOnlyGap_log_five_hundred_neg

end PseudoPrime.Analysis

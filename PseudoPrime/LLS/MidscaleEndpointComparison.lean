/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MidscaleEndpointRadius
public import PseudoPrime.Analysis.AdaptiveReciprocalRadius

/-! # Certified comparison of midscale and adaptive endpoint radii -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For a reference radius at least 24, the reciprocal bridge loss is at
least 787/500. Bound its negative inverse-square term at 24 and retain the
nonnegative inverse term. This sharpens the adaptive radius lower bound. -/
theorem midscale_reciprocalLossBridge_lower {t : ℝ} (ht : 24 ≤ t) :
    (787 / 500 : ℝ) ≤ Analysis.reciprocalLossBridge t := by
  have ht0 : 0 < t - 1 := by linarith only [ht]
  have hsq : (576 : ℝ) ≤ t ^ 2 := by nlinarith only [ht]
  have hn : 0 ≤ (231 / 5000 : ℝ) / (t - 1) := div_nonneg (by norm_num only) ht0.le
  have hk :=
    div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 16033 / 9000)
      (by norm_num only : (0 : ℝ) < 576) hsq
  dsimp only [Analysis.reciprocalLossBridge]
  linarith only [hn, hk]

/-- For L>=26, the reference finer radius is at least 24. The logarithmic
tangent at 32 and a rational upper bound for log 2 certify the whole half-line.
This permits the sharper bridge estimate throughout the midscale domain. -/
theorem midscale_finerRoot_ge_twenty_four {L : ℝ} (hL : 26 ≤ L) :
    24 ≤ Analysis.finerPart2CutoffRoot L := by
  have hLp : 0 < L := by linarith only [hL]
  have ht := Real.log_le_sub_one_of_pos (div_pos hLp (by norm_num only : (0 : ℝ) < 32))
  rw [Real.log_div hLp.ne' (by norm_num only : (32 : ℝ) ≠ 0)] at ht
  have he : Real.log (32 : ℝ) = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  rw [he] at ht
  dsimp only [Analysis.finerPart2CutoffRoot]
  linarith only [hL, ht, Real.log_two_lt_d9]

/-- For L>=26 the adaptive radius is bounded below by L-2log L+91/20.
Retain the improved reciprocal bridge lower bound instead of the earlier
uniform displacement estimate. This supports strict affine comparisons. -/
theorem midscale_adaptive_lower {L : ℝ} (hL : 26 ≤ L) :
    L - 2 * Real.log L + 91 / 20 ≤ Analysis.adaptivePart2CutoffRoot L := by
  have hb := midscale_reciprocalLossBridge_lower (midscale_finerRoot_ge_twenty_four hL)
  dsimp only [Analysis.adaptivePart2CutoffRoot, Analysis.finerPart2CutoffRoot] at hb ⊢
  linarith only [hb]

/-- At positive L and C, an upper bound Z for log C yields the tangent
upper bound log L<=Z+L/C-1. This reduces each interval comparison to an
affine rational inequality rather than sampling logarithms. -/
theorem midscale_log_tangent {L C Z : ℝ} (hL : 0 < L) (hC : 0 < C) (hZ : Real.log C ≤ Z) :
    Real.log L ≤ Z + L / C - 1 := by
  have ht := Real.log_le_sub_one_of_pos (div_pos hL hC)
  rw [Real.log_div hL.ne' hC.ne'] at ht
  linarith only [ht, hZ]

/-- The former four-piece radius lies below the adaptive radius. Four
logarithmic tangents give exact affine comparisons using centers 32, 64, 128
and 200. This retained comparison transfers to the refined radius. -/
theorem midscaleEndpointRadiusOriginal_lt_adaptive {L : ℝ} (hlo : 1339 / 50 ≤ L)
    (hhi : L ≤ 26269 / 100) :
    midscaleEndpointRadiusOriginal L < Analysis.adaptivePart2CutoffRoot L := by
  have hLp : 0 < L := by linarith only [hlo]
  have hb := midscale_adaptive_lower (by linarith only [hlo] : 26 ≤ L)
  have h32 : Real.log (32 : ℝ) ≤ 1733 / 500 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_lt_d9]
  have h64 : Real.log (64 : ℝ) ≤ 4159 / 1000 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_lt_d9]
  have h128 : Real.log (128 : ℝ) ≤ 4853 / 1000 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_lt_d9]
  have h200 : Real.log (200 : ℝ) ≤ 53 / 10 := by
    rw [show (200 : ℝ) = 2 ^ 3 * 5 ^ 2 by norm_num only,
      Real.log_mul (by norm_num only) (by norm_num only), Real.log_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_lt_d9, Real.log_five_lt_d9]
  by_cases h₁ : L ≤ 703 / 20
  · rw [midscaleEndpointRadiusOriginal, ite_eq_left h₁]
    have ht := midscale_log_tangent hLp (by norm_num only : (0 : ℝ) < 32) h32
    linarith only [ht, hb, hlo, h₁]
  · by_cases h₂ : L ≤ 1706 / 25
    · rw [midscaleEndpointRadiusOriginal, ite_eq_right h₁, ite_eq_left h₂]
      have ht := midscale_log_tangent hLp (by norm_num only : (0 : ℝ) < 64) h64
      linarith only [ht, hb, h₁, h₂]
    · by_cases h₃ : L ≤ 6671 / 50
      · rw [midscaleEndpointRadiusOriginal, ite_eq_right h₁, ite_eq_right h₂, ite_eq_left h₃]
        have ht := midscale_log_tangent hLp (by norm_num only : (0 : ℝ) < 128) h128
        linarith only [ht, hb, h₂, h₃]
      · rw [midscaleEndpointRadiusOriginal, ite_eq_right h₁, ite_eq_right h₂, ite_eq_right h₃]
        have ht := midscale_log_tangent hLp (by norm_num only : (0 : ℝ) < 200) h200
        linarith only [ht, hb, h₃, hhi]

/-- The refined five-piece radius lies below the adaptive radius by comparison
with the former four-piece radius. -/
theorem midscaleEndpointRadius_lt_adaptive {L : ℝ} (hlo : 1339 / 50 ≤ L) (hhi : L ≤ 26269 / 100) :
    midscaleEndpointRadius L < Analysis.adaptivePart2CutoffRoot L := by
  exact
    lt_of_le_of_lt (midscaleEndpointRadius_le_original)
      (midscaleEndpointRadiusOriginal_lt_adaptive hlo hhi)

/-- On the interior of the replaced interval, the squared witness bound is
strictly below the former squared bound. Both radii are positive there. -/
theorem midscaleEndpointRadius_sq_lt_original_sq {L : ℝ} (hlo : 703 / 20 < L) (hhi : L < 1706 / 25)
    (hdomlo : 1339 / 50 ≤ L) (hdomhi : L ≤ 26269 / 100) :
    (midscaleEndpointRadius L) ^ 2 < (midscaleEndpointRadiusOriginal L) ^ 2 := by
  have hdiff := midscaleEndpointRadius_lt_original hlo hhi
  have hpos := (midscaleEndpointRadius_data hdomlo hdomhi).1
  have hsum : 0 < midscaleEndpointRadiusOriginal L + midscaleEndpointRadius L := by
    have hle := midscaleEndpointRadius_le_original (L := L)
    linarith only [hpos, hle]
  have hp := mul_pos (sub_pos.mpr hdiff) hsum
  have heq :
    midscaleEndpointRadiusOriginal L ^ 2 - midscaleEndpointRadius L ^ 2 =
      (midscaleEndpointRadiusOriginal L - midscaleEndpointRadius L) *
        (midscaleEndpointRadiusOriginal L + midscaleEndpointRadius L) := by
    ring
  have hpow : 0 < midscaleEndpointRadiusOriginal L ^ 2 - midscaleEndpointRadius L ^ 2 := by
    rw [heq]
    exact hp
  exact sub_pos.mp hpow

/-- On the entire certified interval, the squared midscale upper bound is
strictly smaller than the squared adaptive upper bound. Both radii are positive;
multiply their positive difference and sum. This certifies the best-bound table. -/
theorem midscaleEndpointRadius_sq_lt_adaptive_sq {L : ℝ} (hlo : 1339 / 50 ≤ L)
    (hhi : L ≤ 26269 / 100) :
    (midscaleEndpointRadius L) ^ 2 < (Analysis.adaptivePart2CutoffRoot L) ^ 2 := by
  have hr := (midscaleEndpointRadius_data hlo hhi).1
  have hc := midscaleEndpointRadius_lt_adaptive hlo hhi
  have hp :=
    mul_pos (sub_pos.mpr hc)
      (show 0 < Analysis.adaptivePart2CutoffRoot L + midscaleEndpointRadius L by
        linarith only [hr, hc])
  nlinarith only [hp]

end PseudoPrime.LLS.PaperStatements

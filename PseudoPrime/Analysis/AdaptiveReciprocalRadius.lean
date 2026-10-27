/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.PointwiseReciprocalLowerBound
public import PseudoPrime.Analysis.FinerPart2CutoffBounds

/-! # Explicit adaptive Part 2 radius from pointwise reciprocal savings -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a reference root t. Output: a rational upper envelope for losses at roots in [t-1,t].
Role: obtain an explicit smaller radius without solving an implicit equation. -/
noncomputable def reciprocalLossBridge (t : ℝ) : ℝ :=
  78861 / 50000 + (231 / 5000) / (t - 1) - (16033 / 9000) / t ^ 2

/-- Input: a reference root at least seven.
Claim: the bridge loss is strictly less than the uniform loss 31551/20000.
Proof: compare inverse terms below 22 and complete a square above 22.
Role: guarantee a strict radius improvement on the entire admitted half-line. -/
theorem reciprocalLossBridge_lt_uniform {t : ℝ} (ht : 7 ≤ t) :
    reciprocalLossBridge t < (31551 / 20000 : ℝ) := by
  have ht0 : 0 < t := by linarith only [ht]
  have hu : 0 < t - 1 := by linarith only [ht]
  by_cases h22 : t ≤ 22
  · have hm := mul_nonneg ht0.le (sub_nonneg.mpr h22)
    have hdom : (231 / 5000 : ℝ) / (t - 1) ≤ (16033 / 9000 : ℝ) / t ^ 2 :=
      (div_le_div_iff₀ hu (sq_pos_of_pos ht0)).mpr (by nlinarith only [hm, ht])
    dsimp only [reciprocalLossBridge]
    linarith only [hdom]
  · have hfrac : (231 / 5000 : ℝ) / (t - 1) ≤ (121 / 2500 : ℝ) / t :=
      (div_le_div_iff₀ hu ht0).mpr (by linarith only [h22])
    have hquad :=
      quadratic_remainder_lower (a := (16033 / 9000 : ℝ)) (b := (121 / 5000 : ℝ)) (u := 1 / t)
        (by norm_num only)
    rw [show (1 / t) ^ 2 = 1 / t ^ 2 by rw [div_pow, one_pow]] at hquad
    dsimp only [reciprocalLossBridge]
    simp only [div_eq_mul_inv] at hfrac hquad ⊢
    nlinarith only [hfrac, hquad]

/-- Input: a reference root at least seven. Claim: its bridge loss is at least 77/50.
Proof: bound the inverse-square term at seven and retain the positive term.
Role: limit how far the explicit root is moved. -/
theorem reciprocalLossBridge_ge_77_div_50 {t : ℝ} (ht : 7 ≤ t) :
    (77 / 50 : ℝ) ≤ reciprocalLossBridge t := by
  have ht0 : 0 < t - 1 := by linarith only [ht]
  have hsq : (49 : ℝ) ≤ t ^ 2 := by nlinarith only [ht]
  have hn : 0 ≤ (231 / 5000 : ℝ) / (t - 1) := div_nonneg (by norm_num only) ht0.le
  have hk :=
    div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 16033 / 9000)
      (by norm_num only : (0 : ℝ) < 49) hsq
  dsimp only [reciprocalLossBridge]
  linarith only [hn, hk]

/-- Input: a reference root t at least seven and a root y in [t-1,t].
Claim: the pointwise loss at y is at most the bridge loss at t.
Proof: compare the positive inverse and negative inverse-square terms separately.
Role: certify the explicit root using the actual reciprocal lower bound. -/
theorem pointwiseReciprocalLoss_le_bridge {t y : ℝ} (ht : 7 ≤ t) (hylo : t - 1 ≤ y) (hyhi : y ≤ t) :
    pointwiseReciprocalLoss y ≤ reciprocalLossBridge t := by
  have ht0 : 0 < t - 1 := by linarith only [ht]
  have hy0 : 0 < y := lt_of_lt_of_le ht0 hylo
  have hp := div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 231 / 5000) ht0 hylo
  have hs : y ^ 2 ≤ t ^ 2 := by nlinarith only [hy0, hyhi]
  have hn :=
    div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 16033 / 9000) (sq_pos_of_pos hy0) hs
  dsimp only [pointwiseReciprocalLoss, reciprocalLossBridge]
  linarith only [hp, hn]

/-- Input: a logarithmic level. Output: the finer root with its uniform loss replaced by the bridge.
Role: define a closed adaptive radius that avoids an implicit root equation. -/
noncomputable def adaptivePart2CutoffRoot (L : ℝ) : ℝ :=
  let t := finerPart2CutoffRoot L
  t - 31551 / 10000 + 2 * reciprocalLossBridge t

/-- Input: a reference finer root at least seven.
Claim: the adaptive root lies between t-1/10 and t, with the upper inequality strict.
Proof: use both rational bridge bounds.
Role: retain root height and certify strict improvement. -/
theorem adaptivePart2Root_bounds {L : ℝ} (ht : 7 ≤ finerPart2CutoffRoot L) :
    finerPart2CutoffRoot L - 1 / 10 ≤ adaptivePart2CutoffRoot L ∧
      adaptivePart2CutoffRoot L < finerPart2CutoffRoot L := by
  have hlo := reciprocalLossBridge_ge_77_div_50 ht
  have hhi := reciprocalLossBridge_lt_uniform ht
  dsimp only [adaptivePart2CutoffRoot]
  constructor <;> linarith only [hlo, hhi]

/-- Input: a reference finer root at least seven.
Claim: the adaptive root satisfies the pointwise-loss logarithmic root condition.
Proof: bound the actual loss by the bridge and use the root definition.
Role: supply the analytic witness criterion without a numerical solver. -/
theorem adaptivePart2Root_pointwise_condition {L : ℝ} (ht : 7 ≤ finerPart2CutoffRoot L) :
    L - 2 * Real.log L + 701 / 500 + 2 * pointwiseReciprocalLoss (adaptivePart2CutoffRoot L) ≤
      adaptivePart2CutoffRoot L := by
  have hb := adaptivePart2Root_bounds ht
  have hr :=
    pointwiseReciprocalLoss_le_bridge ht
      (show finerPart2CutoffRoot L - 1 ≤ adaptivePart2CutoffRoot L by linarith only [hb.1]) hb.2.le
  dsimp only [adaptivePart2CutoffRoot, finerPart2CutoffRoot] at hr ⊢
  linarith only [hr]

/-- Input: positive level and root, and an upper logarithmic root condition with any constant c.
Claim: the coupled level inequality needed by Part 2 holds.
Proof: multiply the logarithm tangent at the root and the supplied root inequality.
Role: generalize the former exact-root coupling to upper root conditions. -/
theorem coupled_level_bound_of_logarithmic_root_le {L y c : ℝ} (hL : 0 < L) (hy : 0 < y)
    (hroot : L - 2 * Real.log L + c ≤ y) :
    (y - 2) * L ≤ (y - 2) * y + y * (2 * Real.log y - c) := by
  have ht := log_le_log_add_sub_div (a := y) (y := L) hy hL
  have hm := mul_le_mul_of_nonneg_right ht hy.le
  rw [add_mul, div_mul_cancel₀ _ hy.ne'] at hm
  have hr := mul_le_mul_of_nonneg_right hroot hy.le
  nlinarith only [hm, hr]

/-- Input: a logarithmic level at least 6.39. Claim: its finer root is at least 36/5.
Proof: certify the tangent endpoint and use the tangent on the entire half-line.
Role: retain the cutoff after the adaptive radius reduction. -/
theorem finerPart2Root_ge_thirty_six_fifths_of_639_div_100_le {L : ℝ} (hL : (639 / 100 : ℝ) ≤ L) :
    (36 / 5 : ℝ) ≤ finerPart2CutoffRoot L := by
  have hL0 : 0 < L := by linarith only [hL]
  have hc : rationalLogIntervalCheck (639 / 100) 3 10 (185 / 100) (186 / 100) = true := by
    decide +kernel
  have hh := (rationalLogIntervalCheck_sound hc).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hh
  have ht := log_le_log_add_sub_div (a := (639 / 100 : ℝ)) (y := L) (by norm_num only) hL0
  dsimp only [finerPart2CutoffRoot]
  linarith only [ht, hh, hL]

/-- Input: a modulus at least 600. Claim: its logarithm is at least 6.39.
Proof: certify log 600 and use monotonicity.
Role: provide a fully analytic entrance for the adaptive bound. -/
theorem log_level_ge_adaptivePart2_entrance {q : ℕ} (hq : 600 ≤ q) :
    (639 / 100 : ℝ) ≤ Real.log q := by
  have hc : rationalLogIntervalCheck 600 9 10 (639 / 100) (640 / 100) = true := by decide +kernel
  have h := (rationalLogIntervalCheck_sound hc).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  exact h.trans (Real.log_le_log (by norm_num only) (Nat.cast_le.mpr hq))

/-- Input: a reference finer root at least 36/5.
Claim: the adaptive root is at least seven and its square is at least fifty.
Proof: use the maximum decrease of one tenth.
Role: discharge both small-scale comparison premises. -/
theorem adaptivePart2Root_height_and_cutoff {L : ℝ} (ht : (36 / 5 : ℝ) ≤ finerPart2CutoffRoot L) :
    7 ≤ adaptivePart2CutoffRoot L ∧ 50 ≤ (adaptivePart2CutoffRoot L) ^ 2 := by
  have hb := adaptivePart2Root_bounds (le_trans (by norm_num only) ht)
  constructor
  · linarith only [hb.1, ht]
  · nlinarith only [hb.1, ht]

/-- Input: a reference finer root at least seven.
Claim: the adaptive squared radius is strictly smaller than the finer squared radius.
Proof: both roots are nonnegative and their comparison is strict.
Role: prove improvement without combining different witnesses by a minimum. -/
theorem adaptivePart2Root_sq_lt_finer {L : ℝ} (ht : 7 ≤ finerPart2CutoffRoot L) :
    (adaptivePart2CutoffRoot L) ^ 2 < (finerPart2CutoffRoot L) ^ 2 := by
  have hb := adaptivePart2Root_bounds ht
  have hy : 0 ≤ adaptivePart2CutoffRoot L := by linarith only [ht, hb.1]
  exact (sq_lt_sq₀ hy (by linarith only [ht])).mpr hb.2

end PseudoPrime.Analysis

/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ReciprocalCostPart2Bounds
public import PseudoPrime.Analysis.LogRootSmallLevelBounds

/-! # Finer Part 2 radius and logarithmic entrance -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a logarithmic level L. Output: L-2*log(L)+4.5571.
Role: share the finer Part 2 radius between analytic, finite and primality-test bounds. -/
noncomputable def finerPart2CutoffRoot (L : ℝ) : ℝ :=
  L - 2 * Real.log L + 45571 / 10000

/-- Input: a modulus at least 1122. Claim: its logarithm is at least 17557/2500.
Proof: certify the endpoint and use logarithm monotonicity.
Role: supply the entrance for the finer analytic radius. -/
theorem log_level_ge_finerPart2_entrance {q : ℕ} (hq : 1122 ≤ q) :
    (17557 / 2500 : ℝ) ≤ Real.log q := by
  have hc : rationalLogIntervalCheck 1122 10 10 (17557 / 2500) (703 / 100) = true := by
    decide +kernel
  have h := (rationalLogIntervalCheck_sound hc).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  exact h.trans (Real.log_le_log (by norm_num only) (Nat.cast_le.mpr hq))

/-- Input: L>=17557/2500. Claim: the finer root exceeds 15/2 and its square is at least 59.
Proof: keep the tangent at the entrance and a certified logarithm upper bound.
Role: discharge the arbitrary reciprocal-cost comparison hypotheses. -/
theorem finerPart2Root_height_and_cutoff {L : ℝ} (hL : (17557 / 2500 : ℝ) ≤ L) :
    (15 / 2 : ℝ) < finerPart2CutoffRoot L ∧ 59 ≤ (finerPart2CutoffRoot L) ^ 2 := by
  have hL0 : 0 < L := by linarith only [hL]
  have hc : rationalLogIntervalCheck (17557 / 2500) 3 12 (194 / 100) (19492 / 10000) = true := by
    decide +kernel
  have h := (rationalLogIntervalCheck_sound hc).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  have ht := log_le_log_add_sub_div (a := (17557 / 2500 : ℝ)) (y := L) (by norm_num only) hL0
  have hb : (15363 / 2000 : ℝ) ≤ finerPart2CutoffRoot L := by
    unfold finerPart2CutoffRoot
    linarith only [ht, h, hL]
  constructor
  · linarith only [hb]
  · nlinarith only [hb]

/-- Input: any positive logarithmic level. Claim: the finer squared radius is strictly smaller
than the previous reciprocal-cost radius. Proof: use positive-root constant monotonicity.
Role: make the constant improvement explicit over the whole domain. -/
theorem finerPart2Root_sq_lt_reciprocal {L : ℝ} (hL : 0 < L) :
    (finerPart2CutoffRoot L) ^ 2 < (reciprocalPart2CutoffRoot L) ^ 2 := by
  exact
    logarithmicRoot_sq_strictMono_constant hL (by norm_num only : (0 : ℝ) ≤ 45571 / 10000)
      (by norm_num only : (45571 / 10000 : ℝ) < 2279 / 500)

/-- Input: a modulus at least 17400. Claim: the finer squared radius is strictly below log(q)^2.
Proof: certify two logarithm intervals and retain root positivity.
Role: lower the entrance of the strict log-square comparison. -/
theorem finerPart2Root_sq_lt_log_sq_of_17400_le {q : ℕ} (hq : 17400 ≤ q) :
    (finerPart2CutoffRoot (Real.log q)) ^ 2 < (Real.log q) ^ 2 := by
  have hc : rationalLogIntervalCheck 17400 14 12 (2441 / 250) (977 / 100) = true := by
    decide +kernel
  have hL := (rationalLogIntervalCheck_sound hc).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hL
  have hLq := hL.trans (Real.log_le_log (by norm_num only) (Nat.cast_le.mpr hq))
  have hd : rationalLogIntervalCheck (2441 / 250) 3 12 (22787 / 10000) (228 / 100) = true := by
    decide +kernel
  have hu := (rationalLogIntervalCheck_sound hd).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hu
  have hlog := hu.trans (Real.log_le_log (by norm_num only) hLq)
  have hp :=
    logarithmicRoot_pos (by linarith only [hLq] : 0 < Real.log q)
      (by norm_num only : (0 : ℝ) ≤ 45571 / 10000)
  unfold finerPart2CutoffRoot
  nlinarith only [hp, hlog]

end PseudoPrime.Analysis

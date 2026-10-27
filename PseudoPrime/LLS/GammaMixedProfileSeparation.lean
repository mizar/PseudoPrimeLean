/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaMixedProfileDualBounds
public import PseudoPrime.Analysis.RpowIntegerCertificate
public import PseudoPrime.Analysis.QuadraticGammaSmoothedNumerics

/-! # Fully certified separation on the logarithmic cell [300,310] -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: 300<=L<=310. Claim: scale, root and logarithm bounds for x=(2/5)L^2.
Proof: compare squares and use two kernel-checked logarithm intervals.
Role: provide correlated profile data without lossy independent endpoint substitutions. -/
theorem gamma_mixed_profile_geometry_300_310 {L : ℝ} (hlo : 300 ≤ L) (hhi : L ≤ 310) :
    let x := (2 / 5 : ℝ) * L ^ 2;
    36000 ≤ x ∧
      x ≤ 38440 ∧
      (79 / 125 : ℝ) * L ≤ Real.sqrt x ∧
      Real.sqrt x ≤ 1963 / 10 ∧
      Real.log x ≤ 11 ∧ Real.log ((101 / 40 : ℝ) * x) ≤ 12 ∧ Real.log ((99 / 40 : ℝ) * x) ≤ 12 := by
  dsimp only
  let x := (2 / 5 : ℝ) * L ^ 2
  have hlow := mul_nonneg (sub_nonneg.mpr hlo) (show 0 ≤ L + 300 by linarith only [hlo])
  have hupp := mul_nonneg (sub_nonneg.mpr hhi) (show 0 ≤ L + 310 by linarith only [hlo])
  have hxlo : (36000 : ℝ) ≤ x := by
    dsimp only [x]; nlinarith only [hlow]
  have hxhi : x ≤ (38440 : ℝ) := by
    dsimp only [x]; nlinarith only [hupp]
  have hx0 : 0 < x := by linarith only [hxlo]
  have hroot : (79 / 125 : ℝ) * L ≤ Real.sqrt x := by
    apply
      (Real.le_sqrt (mul_nonneg (by norm_num only) (show 0 ≤ L by linarith only [hlo])) hx0.le).mpr
    dsimp only [x]
    nlinarith only [sq_nonneg L]
  have hrhi : Real.sqrt x ≤ (1963 / 10 : ℝ) :=
    (Real.sqrt_le_iff).mpr
      ⟨by norm_num only, hxhi.trans (by norm_num only : (38440 : ℝ) ≤ (1963 / 10 : ℝ) ^ 2)⟩
  have hc11 : Analysis.rationalLogIntervalCheck 38440 16 20 10 11 = true := by decide +kernel
  have hc12 : Analysis.rationalLogIntervalCheck 97061 17 20 11 12 = true := by decide +kernel
  have hl11 := (Analysis.rationalLogIntervalCheck_sound hc11).2
  have hl12 := (Analysis.rationalLogIntervalCheck_sound hc12).2
  norm_num only [Rat.cast_ofNat] at hl11 hl12
  have hxlog := (Real.log_le_log hx0 hxhi).trans hl11
  have harg : (101 / 40 : ℝ) * x ≤ 97061 := by linarith only [hxhi]
  have hext :=
    (Real.log_le_log (mul_pos (by norm_num only : (0 : ℝ) < 101 / 40) hx0) harg).trans hl12
  have hrarg : (99 / 40 : ℝ) * x ≤ (101 / 40 : ℝ) * x := by linarith only [hx0]
  have hlogr :=
    (Real.log_le_log (mul_pos (by norm_num only : (0 : ℝ) < 99 / 40) hx0) hrarg).trans hext
  exact ⟨hxlo, hxhi, hroot, hrhi, hxlog, hext, hlogr⟩

/-- Input: 300<=L<=310. Claim: ramp, principal, pole and left-line errors obey the four caps.
Proof: preserve x=(sqrt x)^2 in the ramp and use an integer-power certificate on the left error.
Role: close all non-Euler numerical obligations for this profile cell. -/
theorem gamma_mixed_profile_errors_300_310 {L : ℝ} (hlo : 300 ≤ L) (hhi : L ≤ 310) :
    let x := (2 / 5 : ℝ) * L ^ 2;
    gammaRampPairedErrorNumerator x / Real.sqrt x ≤ 3 ∧
      (Real.sqrt x / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10) / Real.sqrt x ≤ 2 / 5 ∧
      ((7 / 6 : ℝ) * (L + 7 / 5) + 4) / Real.sqrt x ≤ 19 / 10 ∧ 43 * x ^ (-9 / 16 : ℝ) ≤ 1 / 8 := by
  dsimp only
  let x := (2 / 5 : ℝ) * L ^ 2
  change
    gammaRampPairedErrorNumerator x / Real.sqrt x ≤ 3 ∧
      (Real.sqrt x / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10) / Real.sqrt x ≤ 2 / 5 ∧
      ((7 / 6 : ℝ) * (L + 7 / 5) + 4) / Real.sqrt x ≤ 19 / 10 ∧ 43 * x ^ (-9 / 16 : ℝ) ≤ 1 / 8
  obtain ⟨hxlo, hxhi, hroot, hrhi, hlogx, hlogext, hlogr⟩ :=
    gamma_mixed_profile_geometry_300_310 hlo hhi
  change (36000 : ℝ) ≤ x at hxlo
  change x ≤ (38440 : ℝ) at hxhi
  change (79 / 125 : ℝ) * L ≤ Real.sqrt x at hroot
  change Real.sqrt x ≤ (1963 / 10 : ℝ) at hrhi
  change Real.log x ≤ 11 at hlogx
  change Real.log ((101 / 40 : ℝ) * x) ≤ 12 at hlogext
  change Real.log ((99 / 40 : ℝ) * x) ≤ 12 at hlogr
  have hx0 : 0 < x := by linarith only [hxlo]
  have hr0 := Real.sqrt_pos.mpr hx0
  have hrlo : (948 / 5 : ℝ) ≤ Real.sqrt x := by linarith only [hroot, hlo]
  have hsq := Real.sq_sqrt hx0.le
  have hprod := mul_nonneg (Real.sqrt_nonneg x) (sub_nonneg.mpr hrhi)
  have hlogr' : Real.log (x * (99 / 40)) ≤ 12 := by simpa only [mul_comm] using hlogr
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ hr0]
    unfold gammaRampPairedErrorNumerator rampSmoothedIncrementError rampExtendedSmoothedError
    nlinarith only [hsq, hprod, hlogext, hlogr', hrlo]
  · rw [div_le_iff₀ hr0]
    linarith only [hlogx, hrlo]
  · rw [div_le_iff₀ hr0]
    linarith only [hroot, hlo]
  · have hp := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 36000) hxlo 9
    have hc : (1 : ℝ) ≤ (1 / 344 : ℝ) ^ 16 * (36000 : ℝ) ^ 9 := by norm_num only
    have hd := mul_le_mul_of_nonneg_left hp (pow_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 344) 16)
    have h :=
      Analysis.rpow_neg_nat_div_le_of_power_bound hx0 (by norm_num only : (0 : ℝ) ≤ 1 / 344) 9 16
        (by norm_num only) (hc.trans hd)
    norm_num only [neg_div] at h ⊢
    linarith only [h]

/-- Input: RH and 300<=L<=310. Claim: the actual factor-free margin is at least 7/60.
Proof: combine the certified dual cap, prefix half-line lower bound, ramp mass and error caps.
Role: certify a complete analytic witness cell rather than a floating-point candidate. -/
theorem gamma_factor_free_separation_300_310 (hRH : RiemannHypothesis) {L : ℝ} (hlo : 300 ≤ L)
    (hhi : L ≤ 310) :
    7 / 60 ≤ gammaFactorFreeSeparation L ((99 / 100 : ℝ) * L ^ 2) ((2 / 5 : ℝ) * L ^ 2) := by
  let x := (2 / 5 : ℝ) * L ^ 2
  let b := (99 / 100 : ℝ) * L ^ 2
  change 7 / 60 ≤ gammaFactorFreeSeparation L b x
  have hsq := mul_nonneg (sub_nonneg.mpr hlo) (show 0 ≤ L + 300 by linarith only [hlo])
  have hb : (89100 : ℝ) ≤ b := by
    dsimp only [b]; nlinarith only [hsq]
  have hp := gamma_prefix89100_lower_halfline hRH hb
  have hd := gamma_profile_dual_le_300_310 hlo hhi
  change gammaScaleSignedDualBudget L x ≤ (67 / 10 : ℝ) at hd
  have hj :
    gammaFactorFreeJointBudget L b x ≤
      (11783423 / 25000000 : ℝ) * (L + 7 / 5) + 3 / 4 + 67 / 10 - 28923 / 2500 := by
    unfold gammaFactorFreeJointBudget
    linarith only [hp, hd]
  obtain ⟨hxlo, hxhi, hroot, hrhi, hlogx, hlogext, hlogr⟩ :=
    gamma_mixed_profile_geometry_300_310 hlo hhi
  change (79 / 125 : ℝ) * L ≤ Real.sqrt x at hroot
  have hm1 := mul_le_mul_of_nonneg_right Analysis.gamma_ramp_mass_lower (Real.sqrt_nonneg x)
  have hm2 :=
    mul_le_mul_of_nonneg_left hroot (show (0 : ℝ) ≤ 83125234337 / 100000000000 by norm_num only)
  have hm := hm2.trans hm1
  obtain ⟨he1, he2, he3, he4⟩ := gamma_mixed_profile_errors_300_310 hlo hhi
  change gammaRampPairedErrorNumerator x / Real.sqrt x ≤ 3 at he1
  change
    (Real.sqrt x / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10) / Real.sqrt x ≤
      2 / 5 at he2
  change ((7 / 6 : ℝ) * (L + 7 / 5) + 4) / Real.sqrt x ≤ 19 / 10 at he3
  change 43 * x ^ (-9 / 16 : ℝ) ≤ 1 / 8 at he4
  unfold gammaFactorFreeSeparation
  nlinarith only [hm, hj, he1, he2, he3, he4, hlo]

end PseudoPrime.LLS

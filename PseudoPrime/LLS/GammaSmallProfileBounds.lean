/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaSmallProfileCertificates
public import PseudoPrime.LLS.GammaSmallProfileSeparation

/-! # Certified mixed-profile separation on the full bridge from 290 to 300 -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Claim: the displayed rational cell passes the logarithm, error and margin checks.
Proof: exact kernel arithmetic. Role: close the elementary separation certificate. -/
theorem small_separation_290_295_check :
    gammaSmallProfileCheck 290 295 (21 / 2) (57 / 5) (29 / 10) (19 / 50) (25 / 4) 15 16 = true := by
  decide +kernel

/-- Input: L in the displayed closed cell. Claim: the actual signed dual budget is at most 25/4.
Proof: transfer the checked excess allowance 17/4 and coupled price at most two.
Role: remove the final dual numerical assumption. -/
theorem gamma_profile_dual_le_290_295 {L : ℝ} (hlo : 290 ≤ L) (hhi : L ≤ 295) :
    gammaScaleSignedDualBudget L ((2 / 5 : ℝ) * L ^ 2) ≤ 25 / 4 := by
  have h :=
    gamma_profile_dual_small_cell 290 295 (17 / 4) 532 (by norm_num only)
      Analysis.small_cell_290_295_check (by decide +kernel) Analysis.small_rows_290_295_check
      Analysis.small_sum_290_295_check hlo hhi
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  linarith only [h]

/-- Input: RH and L in the displayed closed interval. Claim: the actual margin is at least 7/60.
Proof: apply checked elementary errors and the certified dual budget, splitting at 295 if needed.
Role: connect the small analytic bridge to quadratic witness bounds. -/
theorem gamma_small_profile_separation_290_295 (hRH : RiemannHypothesis) {L : ℝ} (hlo : 290 ≤ L)
    (hhi : L ≤ 295) :
    7 / 60 ≤ gammaFactorFreeSeparation L ((99 / 100 : ℝ) * L ^ 2) ((2 / 5 : ℝ) * L ^ 2) := by
  exact
    gamma_small_profile_separation_of_check hRH 290 295 (21 / 2) (57 / 5) (29 / 10) (19 / 50)
      (25 / 4) 15 16 small_separation_290_295_check hlo hhi
      (by
        norm_num only [Rat.cast_div, Rat.cast_ofNat]; exact gamma_profile_dual_le_290_295 hlo hhi)

/-- Claim: the displayed rational cell passes the logarithm, error and margin checks.
Proof: exact kernel arithmetic. Role: close the elementary separation certificate. -/
theorem small_separation_295_300_check :
    gammaSmallProfileCheck 295 300 (21 / 2) (23 / 2) (29 / 10) (19 / 50) (25 / 4) 15 16 = true := by
  decide +kernel

/-- Input: L in the displayed closed cell. Claim: the actual signed dual budget is at most 25/4.
Proof: transfer the checked excess allowance 17/4 and coupled price at most two.
Role: remove the final dual numerical assumption. -/
theorem gamma_profile_dual_le_295_300 {L : ℝ} (hlo : 295 ≤ L) (hhi : L ≤ 300) :
    gammaScaleSignedDualBudget L ((2 / 5 : ℝ) * L ^ 2) ≤ 25 / 4 := by
  have h :=
    gamma_profile_dual_small_cell 295 300 (17 / 4) 541 (by norm_num only)
      Analysis.small_cell_295_300_check (by decide +kernel) Analysis.small_rows_295_300_check
      Analysis.small_sum_295_300_check hlo hhi
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  linarith only [h]

/-- Input: RH and L in the displayed closed interval. Claim: the actual margin is at least 7/60.
Proof: apply checked elementary errors and the certified dual budget, splitting at 295 if needed.
Role: connect the small analytic bridge to quadratic witness bounds. -/
theorem gamma_small_profile_separation_295_300 (hRH : RiemannHypothesis) {L : ℝ} (hlo : 295 ≤ L)
    (hhi : L ≤ 300) :
    7 / 60 ≤ gammaFactorFreeSeparation L ((99 / 100 : ℝ) * L ^ 2) ((2 / 5 : ℝ) * L ^ 2) := by
  exact
    gamma_small_profile_separation_of_check hRH 295 300 (21 / 2) (23 / 2) (29 / 10) (19 / 50)
      (25 / 4) 15 16 small_separation_295_300_check hlo hhi
      (by
        norm_num only [Rat.cast_div, Rat.cast_ofNat]; exact gamma_profile_dual_le_295_300 hlo hhi)

/-- Input: RH and L in the displayed closed interval. Claim: the actual margin is at least 7/60.
Proof: apply checked elementary errors and the certified dual budget, splitting at 295 if needed.
Role: connect the small analytic bridge to quadratic witness bounds. -/
theorem gamma_small_profile_separation_290_300 (hRH : RiemannHypothesis) {L : ℝ} (hlo : 290 ≤ L)
    (hhi : L ≤ 300) :
    7 / 60 ≤ gammaFactorFreeSeparation L ((99 / 100 : ℝ) * L ^ 2) ((2 / 5 : ℝ) * L ^ 2) := by
  by_cases hmid : L ≤ 295
  · exact gamma_small_profile_separation_290_295 hRH hlo hmid
  · exact gamma_small_profile_separation_295_300 hRH (lt_of_not_ge hmid).le hhi

end PseudoPrime.LLS

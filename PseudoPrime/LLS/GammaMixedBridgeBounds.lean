/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaMixedBridgeCertificates
public import PseudoPrime.LLS.GammaMixedCellTransfer
public import PseudoPrime.LLS.GammaMixedBridgeChecks

/-! # Complete mixed-Euler analytic bridge from logarithmic scale 300 to 550 -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: 310<=L<=350. Claim: the actual quadratic-profile dual budget obeys the stated cap.
Proof: apply the checked mixed-row certificate, or compose the two equal-cap cells.
Role: remove all finite excess hypotheses on this logarithmic bridge interval. -/
theorem gamma_profile_dual_le_bridge_310_350 {L : ℝ} (hlo : 310 ≤ L) (hhi : L ≤ 350) :
    gammaScaleSignedDualBudget L ((2 / 5 : ℝ) * L ^ 2) ≤ (7 : ℝ) := by
  have h :=
    gamma_profile_dual_le_of_certificate 310 350 5 631 (by norm_num only [Rat.cast_ofNat])
      Analysis.bridge_cell_310_350_check (by decide +kernel) Analysis.bridge_rows_310_350_check
      Analysis.bridge_sum_310_350_check
      (by
        norm_num only [Rat.cast_ofNat]; exact hlo)
      (by
        norm_num only [Rat.cast_ofNat]; exact hhi)
  norm_num only [Rat.cast_ofNat] at h
  exact h

/-- Input: 350<=L<=450. Claim: the actual quadratic-profile dual budget obeys the stated cap.
Proof: apply the checked mixed-row certificate, or compose the two equal-cap cells.
Role: remove all finite excess hypotheses on this logarithmic bridge interval. -/
theorem gamma_profile_dual_le_bridge_350_450 {L : ℝ} (hlo : 350 ≤ L) (hhi : L ≤ 450) :
    gammaScaleSignedDualBudget L ((2 / 5 : ℝ) * L ^ 2) ≤ (8 : ℝ) := by
  have h :=
    gamma_profile_dual_le_of_certificate 350 450 6 810 (by norm_num only [Rat.cast_ofNat])
      Analysis.bridge_cell_350_450_check (by decide +kernel) Analysis.bridge_rows_350_450_check
      Analysis.bridge_sum_350_450_check
      (by
        norm_num only [Rat.cast_ofNat]; exact hlo)
      (by
        norm_num only [Rat.cast_ofNat]; exact hhi)
  norm_num only [Rat.cast_ofNat] at h
  exact h

/-- Input: 450<=L<=550. Claim: the actual quadratic-profile dual budget obeys the stated cap.
Proof: apply the checked mixed-row certificate, or compose the two equal-cap cells.
Role: remove all finite excess hypotheses on this logarithmic bridge interval. -/
theorem gamma_profile_dual_le_bridge_450_550 {L : ℝ} (hlo : 450 ≤ L) (hhi : L ≤ 550) :
    gammaScaleSignedDualBudget L ((2 / 5 : ℝ) * L ^ 2) ≤ (8 : ℝ) := by
  have h :=
    gamma_profile_dual_le_of_certificate 450 550 6 990 (by norm_num only [Rat.cast_ofNat])
      Analysis.bridge_cell_450_550_check (by decide +kernel) Analysis.bridge_rows_450_550_check
      Analysis.bridge_sum_450_550_check
      (by
        norm_num only [Rat.cast_ofNat]; exact hlo)
      (by
        norm_num only [Rat.cast_ofNat]; exact hhi)
  norm_num only [Rat.cast_ofNat] at h
  exact h

/-- Input: 350<=L<=550. Claim: the actual quadratic-profile dual budget obeys the stated cap.
Proof: apply the checked mixed-row certificate, or compose the two equal-cap cells.
Role: remove all finite excess hypotheses on this logarithmic bridge interval. -/
theorem gamma_profile_dual_le_bridge_350_550 {L : ℝ} (hlo : 350 ≤ L) (hhi : L ≤ 550) :
    gammaScaleSignedDualBudget L ((2 / 5 : ℝ) * L ^ 2) ≤ (8 : ℝ) := by
  by_cases hm : L ≤ 450
  · exact gamma_profile_dual_le_bridge_350_450 hlo hm
  · exact gamma_profile_dual_le_bridge_450_550 (lt_of_not_ge hm).le hhi

/-- Input: RH and 310<=L<=350. Claim: the actual factor-free margin is at least 7/60.
Proof: combine the certified dual bound and the generic separation check, joining adjacent cells.
Role: certify the full bridge required by the lower witness entrance. -/
theorem gamma_factor_free_separation_bridge_310_350 (hRH : RiemannHypothesis) {L : ℝ}
    (hlo : 310 ≤ L) (hhi : L ≤ 350) :
    7 / 60 ≤ gammaFactorFreeSeparation L ((99 / 100 : ℝ) * L ^ 2) ((2 / 5 : ℝ) * L ^ 2) := by
  exact
    gamma_factor_free_separation_of_cell_check hRH 310 350 11 12 (31 / 10) (2 / 5) 7 16 17
      separation_bridge_310_350_check
      (by
        norm_num only [Rat.cast_ofNat]; exact hlo)
      (by
        norm_num only [Rat.cast_ofNat]; exact hhi)
      (by
        norm_num only [Rat.cast_ofNat]; exact gamma_profile_dual_le_bridge_310_350 hlo hhi)

/-- Input: RH and 350<=L<=550. Claim: the actual factor-free margin is at least 7/60.
Proof: combine the certified dual bound and the generic separation check, joining adjacent cells.
Role: certify the full bridge required by the lower witness entrance. -/
theorem gamma_factor_free_separation_bridge_350_550 (hRH : RiemannHypothesis) {L : ℝ}
    (hlo : 350 ≤ L) (hhi : L ≤ 550) :
    7 / 60 ≤ gammaFactorFreeSeparation L ((99 / 100 : ℝ) * L ^ 2) ((2 / 5 : ℝ) * L ^ 2) := by
  exact
    gamma_factor_free_separation_of_cell_check hRH 350 550 12 13 (37 / 10) (9 / 20) 8 17 19
      separation_bridge_350_550_check
      (by
        norm_num only [Rat.cast_ofNat]; exact hlo)
      (by
        norm_num only [Rat.cast_ofNat]; exact hhi)
      (by
        norm_num only [Rat.cast_ofNat]; exact gamma_profile_dual_le_bridge_350_550 hlo hhi)

/-- Input: RH and 300<=L<=550. Claim: the actual factor-free margin is at least 7/60.
Proof: combine the certified dual bound and the generic separation check, joining adjacent cells.
Role: certify the full bridge required by the lower witness entrance. -/
theorem gamma_factor_free_separation_bridge_300_550 (hRH : RiemannHypothesis) {L : ℝ}
    (hlo : 300 ≤ L) (hhi : L ≤ 550) :
    7 / 60 ≤ gammaFactorFreeSeparation L ((99 / 100 : ℝ) * L ^ 2) ((2 / 5 : ℝ) * L ^ 2) := by
  by_cases h310 : L ≤ 310
  · exact gamma_factor_free_separation_300_310 hRH hlo h310
  by_cases h350 : L ≤ 350
  · exact gamma_factor_free_separation_bridge_310_350 hRH (lt_of_not_ge h310).le h350
  · exact gamma_factor_free_separation_bridge_350_550 hRH (lt_of_not_ge h350).le hhi

end PseudoPrime.LLS

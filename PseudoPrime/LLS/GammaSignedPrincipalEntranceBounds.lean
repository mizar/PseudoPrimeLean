/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaScaleJointBudget
public import PseudoPrime.LLS.GammaSignedPrincipalCellCertificate
import PseudoPrime.LLS.GammaSignedPrincipalEntranceCertificates

/-! # Table-free Gamma separation bound -/

public section

namespace PseudoPrime.LLS

/-- Under RH and 260 <= L <= 264, the signed-principal margin is at least 7/60.
Cover the interval by the three adjacent cells. Role: connect the improved
entrance to the established half-line beyond 264. -/
theorem gamma_signed_principal_separation_260_264 (hRH : RiemannHypothesis) {L : ℝ} (hlo : 260 ≤ L)
    (hhi : L ≤ 264) :
    7 / 60 ≤
      gammaSignedPrincipalFactorFreeSeparation L ((9999 / 10000 : ℝ) * L ^ 2)
        ((101 / 250 : ℝ) * L ^ 2) := by
  have h0 := gamma_signed_principal_separation_on_cell hRH 0 (L := L)
  have h1 := gamma_signed_principal_separation_on_cell hRH 1 (L := L)
  have h2 := gamma_signed_principal_separation_on_cell hRH 2 (L := L)
  change (260 : ℝ) ≤ L → L ≤ 261 → _ at h0
  change (261 : ℝ) ≤ L → L ≤ 262 → _ at h1
  change (262 : ℝ) ≤ L → L ≤ 264 → _ at h2
  by_cases hfirst : L ≤ 261
  · exact h0 hlo hfirst
  · by_cases hsecond : L ≤ 262
    · exact h1 (by linarith only [hfirst]) hsecond
    · exact h2 (by linarith only [hsecond]) hhi

end PseudoPrime.LLS

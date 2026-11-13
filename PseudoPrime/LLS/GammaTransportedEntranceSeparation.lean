/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaScaleJointBudget
public import PseudoPrime.LLS.GammaSignedPrincipalCellCertificate
import PseudoPrime.LLS.GammaTransportedEntranceBounds

/-! # Table-free Gamma separation bound -/

public section

namespace PseudoPrime.LLS

/-- Input: RH and 2591/10 <= L <= 260. Claim: the retained factor-free
signed-principal margin exceeds 7/60. Combine the transported actual dual
cap, analytic prefix and polynomial profile. Role: bridge the improved
entrance to the existing half-line without new local row data. -/
theorem gamma_transported_separation (hRH : RiemannHypothesis) {L : ℝ} (hL : 2591 / 10 ≤ L)
    (hU : L ≤ 260) :
    7 / 60 <
      gammaSignedPrincipalFactorFreeSeparation L 50000 ((101 / 250 : ℝ) * L ^ 2) + 9 / 50 := by
  obtain ⟨hlo, hhi, hx, hb⟩ := gamma_transported_profile_inputs hL hU
  have hdual := gamma_transported_dual_cap (by linarith only [hL] : 0 ≤ L) hlo hhi
  have hprefix := gamma_prefix50000_lower_asymmetric hRH (le_refl (50000 : ℝ))
  have hcredit :
    gammaTransportedCredit L +
        (3 / 4 + ((5 / (4 * ((1589 / 2500 : ℝ) * (2591 / 10)))) * L + 377 / 100) + 7 / 60) / 2 ≤
      ∑ k ∈ Finset.Ioc 0 ⌊(50000 : ℝ)⌋₊, Analysis.gammaResolventMangoldtWeight k := by
    dsimp only [gammaTransportedCredit]
    linarith only [hprefix]
  exact
    gamma_retained_margin_gt_of_polynomial (by linarith only [hx]) hcredit hdual
      (gamma_transported_polynomial_condition hL)

end PseudoPrime.LLS

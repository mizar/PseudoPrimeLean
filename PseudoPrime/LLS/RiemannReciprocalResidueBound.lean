/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroMass
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroClassification
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ReciprocalTrivialZeroSeries
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ContourKernelConjugation
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ReciprocalResidueBoundGeneral
import PseudoPrime.LLS.ExplicitFormula

/-!
# RH-conditional reciprocal-kernel residue bound

This file packages the RH-conditional bound from
`AnalyticNumberTheory/RiemannZeta/ReciprocalResidueBoundGeneral.lean` as the LLS Lemma 2.4
interfaces.
The foundation's weighted-sum integral identity transports the bound from the vertical line at
`2` to any vertical line at `τ > 1`; the numerical remainder estimate then yields `log x - 8/5`.
-/

namespace PseudoPrime.LLS

open PseudoPrime.AnalyticNumberTheory.RiemannZeta in
/-- RH implies the reciprocal vertical-integral lower bound for `x > 1` and `τ > 1`.
The foundation's `reciprocalWeightedMangoldtSum_eq_integral` identifies both normalized integrals
with the same weighted sum, so the bound at `τ = 2` from `ReciprocalResidueBoundGeneral.lean`
suffices. -/
theorem llsRiemannReciprocalVerticalIntegralLowerBound_of_riemannHypothesis
    (hRH : RiemannHypothesis) : LLSRiemannReciprocalVerticalIntegralLowerBound := by
  intro x hx τ hτ
  have hx0 : (0 : ℝ) < x := by linarith
  have heq2 :=
    reciprocalWeightedMangoldtSum_eq_integral hx0 (τ :=
      2) (by norm_num only)
  have heqτ :=
    reciprocalWeightedMangoldtSum_eq_integral hx0 hτ
  have hre_eq :
    ((2 * Real.pi : ℝ)⁻¹ •
          ∫ y : ℝ,
            riemannZetaReciprocalContourKernel x
              ((τ : ℂ) + y * Complex.I)).re =
      ((2 * Real.pi : ℝ)⁻¹ •
          ∫ y : ℝ,
            riemannZetaReciprocalContourKernel x
              ((2 : ℂ) + y * Complex.I)).re := by
    rw [← heqτ, heq2]
    norm_num only [Complex.ofReal_ofNat]
  rw [hre_eq]
  exact
    re_integral_riemannZetaReciprocalContourKernel_two_ge_of_riemannHypothesis
      hRH hx

/-- RH and the numerical remainder estimate give the reciprocal lower bound `log x - 8/5`
for `x ≥ 2`, as used in LLS Section 3.1. -/
theorem llsRiemannReciprocalLowerBound_of_riemannHypothesis (hRH : RiemannHypothesis) :
    LLSRiemannReciprocalLowerBound :=
  llsRiemannReciprocalLowerBound_of_explicit_analytic
    (llsRiemannReciprocalExplicitLowerBound_of_verticalIntegralLowerBound
      (llsRiemannReciprocalVerticalIntegralLowerBound_of_riemannHypothesis hRH))

end PseudoPrime.LLS

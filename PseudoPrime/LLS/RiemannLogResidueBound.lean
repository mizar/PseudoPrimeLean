/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.FiniteZeroSums
import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroMass
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroClassification
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ReciprocalTrivialZeroSeries
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LogResidueAtZeroClosedForm
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ContourKernelConjugation
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LogResidueBoundGeneral
import PseudoPrime.LLS.ExplicitFormula

/-!
# RH-conditional logarithmic-kernel residue bound

This file packages the RH-conditional bound from
`AnalyticNumberTheory/RiemannZeta/LogResidueBoundGeneral.lean` as the LLS Lemma 2.1 interfaces.
The foundation's weighted-sum integral identity transports the bound from the vertical line at
`2` to any vertical line at `τ > 1`.
-/

namespace PseudoPrime.LLS

open PseudoPrime.AnalyticNumberTheory.RiemannZeta in
/-- RH implies the logarithmic vertical-integral lower bound for `x > 1` and `τ > 1`.
The foundation's `logWeightedMangoldtSum_eq_integral` identifies both normalized integrals with
the same weighted sum, so the bound at `τ = 2` from `LogResidueBoundGeneral.lean` suffices. -/
theorem llsRiemannLogVerticalIntegralLowerBound_of_riemannHypothesis (hRH : RiemannHypothesis) :
    LLSRiemannLogVerticalIntegralLowerBound := by
  intro x hx τ hτ
  have hx0 : (0 : ℝ) < x := by linarith
  have heq2 := logWeightedMangoldtSum_eq_integral hx0 (τ := 2) (by norm_num only)
  have heqτ := logWeightedMangoldtSum_eq_integral hx0 hτ
  have hre_eq :
    ((2 * Real.pi : ℝ)⁻¹ • ∫ y : ℝ, riemannZetaLogContourKernel x ((τ : ℂ) + y * Complex.I)).re =
      ((2 * Real.pi : ℝ)⁻¹ •
          ∫ y : ℝ, riemannZetaLogContourKernel x ((2 : ℂ) + y * Complex.I)).re := by
    rw [← heqτ, heq2]
    norm_num only [Complex.ofReal_ofNat]
  rw [hre_eq]
  exact re_integral_riemannZetaLogContourKernel_two_ge_of_riemannHypothesis hRH hx

/-- RH implies the weighted-sum lower bound used from LLS Lemma 2.1. -/
theorem llsRiemannWeightedLowerBound_of_riemannHypothesis (hRH : RiemannHypothesis) :
    LLSRiemannWeightedLowerBound :=
  llsRiemannWeightedLowerBound_of_verticalIntegralLowerBound
    (llsRiemannLogVerticalIntegralLowerBound_of_riemannHypothesis hRH)

end PseudoPrime.LLS

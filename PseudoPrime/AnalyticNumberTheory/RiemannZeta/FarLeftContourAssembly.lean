/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.UnifiedHeight
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LeftVerticalEdgeBound
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.HorizontalEdgeBound

/-!
# the zeta-side estimate: assembly of the far-left contour contributions

This file combines the horizontal far-left limit and the left-vertical limit along their common
height sequence.  The signs and the factor `I` are those of
`RectangleGeometry.rectangleBoundaryIntegral`: an upper
horizontal edge is subtracted, and a left vertical edge contributes with `-I`.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The logarithmic kernel's fixed right horizontal segment vanishes on the unified sequence. -/
theorem tendsto_intervalIntegral_riemannZetaLogContourKernel_unifiedHeightSeq {x : ℝ} (hx : 0 < x)
    {lam tau : ℝ} (hlam : -(1 : ℝ) / 2 ≤ lam) (hlamtau : lam ≤ tau) (htau : tau ≤ 2) :
    Filter.Tendsto
      (fun m : ℕ =>
        ∫ σ in lam..tau, riemannZetaLogContourKernel x (σ + unifiedContourHeightSeq m * Complex.I))
      Filter.atTop (nhds 0) := by
  exact
    (tendsto_intervalIntegral_riemannZetaLogContourKernel_goodHeightSeq hx hlam hlamtau htau).comp
      tendsto_farLeftGoodHeightIndex_atTop

/-- The reciprocal kernel's fixed right horizontal segment vanishes on the unified sequence. -/
theorem tendsto_intervalIntegral_riemannZetaReciprocalContourKernel_unifiedHeightSeq {x : ℝ}
    (hx : 0 < x) {lam tau : ℝ} (hlam : -(1 : ℝ) / 2 ≤ lam) (hlamtau : lam ≤ tau) (htau : tau ≤ 2) :
    Filter.Tendsto
      (fun m : ℕ =>
        ∫ σ in lam..tau,
          riemannZetaReciprocalContourKernel x (σ + unifiedContourHeightSeq m * Complex.I))
      Filter.atTop (nhds 0) := by
  exact
    (tendsto_intervalIntegral_riemannZetaReciprocalContourKernel_goodHeightSeq hx hlam hlamtau
          htau).comp
      tendsto_farLeftGoodHeightIndex_atTop

end PseudoPrime.AnalyticNumberTheory.RiemannZeta

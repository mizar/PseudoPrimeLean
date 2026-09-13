/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.UnifiedHeight
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LeftVerticalEdgeBound
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.HorizontalEdgeBound

/-!
# the zeta-side estimate: assembly of the far-left contour contributions

This file combines the horizontal far-left limit and the left-vertical limit along their common
height sequence.  The signs and the factor `I` are those of
`RectangleGeometry.rectangleBoundaryIntegral`: an upper
horizontal edge is subtracted, and a left vertical edge contributes with `-I`.
-/

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The logarithmic kernel's fixed right horizontal segment vanishes on the unified sequence. -/
theorem tendsto_intervalIntegral_riemannZetaLogContourKernel_unifiedHeightSeq {x : ℝ} (hx : 0 < x)
    {lam tau : ℝ} (hlam : -(1 : ℝ) / 2 ≤ lam) (hlamtau : lam ≤ tau) (htau : tau ≤ 2) :
    Filter.Tendsto
      (fun m : ℕ =>
        ∫ σ in lam..tau,
          riemannZetaLogContourKernel x
            (σ +
              unifiedContourHeightSeq m * Complex.I))
      Filter.atTop (nhds 0) := by
  exact
    (tendsto_intervalIntegral_riemannZetaLogContourKernel_goodHeightSeq
          hx hlam hlamtau htau).comp
      tendsto_farLeftGoodHeightIndex_atTop

/-- The reciprocal kernel's fixed right horizontal segment vanishes on the unified sequence. -/
theorem tendsto_intervalIntegral_riemannZetaReciprocalContourKernel_unifiedHeightSeq {x : ℝ}
    (hx : 0 < x) {lam tau : ℝ} (hlam : -(1 : ℝ) / 2 ≤ lam) (hlamtau : lam ≤ tau) (htau : tau ≤ 2) :
    Filter.Tendsto
      (fun m : ℕ =>
        ∫ σ in lam..tau,
          riemannZetaReciprocalContourKernel x
            (σ +
              unifiedContourHeightSeq m * Complex.I))
      Filter.atTop (nhds 0) := by
  exact
    (tendsto_intervalIntegral_riemannZetaReciprocalContourKernel_goodHeightSeq
          hx hlam hlamtau htau).comp
      tendsto_farLeftGoodHeightIndex_atTop

/--
The oriented far-left contribution for the logarithmic kernel.

The first term is the upper horizontal segment from `-(2m+1)` to `-1/2`.  The second is the left
vertical segment from `-Tₘ` to `Tₘ`, with the orientation factor from the rectangle boundary.
-/
noncomputable def riemannZetaLogFarLeftContourContribution (x : ℝ) (m : ℕ) : ℂ :=
  -(∫ σ in (-(2 * (m : ℝ) + 1))..(-1 / 2),
        riemannZetaLogContourKernel x
          ((σ : ℂ) +
            (farLeftHeightSeq m : ℂ) * Complex.I)) -
    Complex.I •
      (∫ t in
        (-(farLeftHeightSeq
            m))..(farLeftHeightSeq m),
        riemannZetaLogContourKernel x
          (-(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I))

end PseudoPrime.AnalyticNumberTheory.RiemannZeta

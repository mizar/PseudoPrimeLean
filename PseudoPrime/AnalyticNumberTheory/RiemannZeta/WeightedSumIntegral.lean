/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.SmoothedContour
import PseudoPrime.AnalyticNumberTheory.Arithmetic.MellinWeightedSums

/-! General smoothed-contour identities and bounds. -/

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For an admissible line `τ > 1`, the logarithmically weighted Mangoldt sum
equals the vertical integral of the logarithmic zeta contour kernel. -/
theorem logWeightedMangoldtSum_eq_integral {x : ℝ} (hx : 0 < x) {τ : ℝ} (hτ : 1 < τ) :
    (Arithmetic.logWeightedMangoldtSum x : ℂ) =
      (2 * Real.pi : ℝ)⁻¹ •
        ∫ y : ℝ,
          riemannZetaLogContourKernel x
            ((τ : ℂ) + y * Complex.I) := by
  rw [← Arithmetic.mellinWeightTwo_vonMangoldt_tsum_eq_ofReal hx,
    mellinWeightTwo_vonMangoldt_tsum_eq hx hτ]

/-- For an admissible line `τ > 1`, the reciprocally weighted Mangoldt sum
equals the vertical integral of the reciprocal zeta contour kernel. -/
theorem reciprocalWeightedMangoldtSum_eq_integral {x : ℝ} (hx : 0 < x) {τ : ℝ} (hτ : 1 < τ) :
    (Arithmetic.reciprocalWeightedMangoldtSum x : ℂ) =
      (2 * Real.pi : ℝ)⁻¹ •
        ∫ y : ℝ,
          riemannZetaReciprocalContourKernel x
            ((τ : ℂ) + y * Complex.I) := by
  rw [←
    Arithmetic.mellinWeightOne_vonMangoldt_div_tsum_eq_ofReal hx,
    mellinWeightOne_vonMangoldt_div_tsum_eq hx hτ]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta

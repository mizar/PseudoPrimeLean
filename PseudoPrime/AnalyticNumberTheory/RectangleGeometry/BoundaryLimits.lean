/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RectangleGeometry.Boundary

/-!
# Vertical limits after horizontal contour edges vanish

Separate the four-edge boundary limit into its surviving vertical contribution.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RectangleGeometry

/-- For any complex integrand and fixed real endpoints, if the upper and
lower horizontal integrals tend to zero and the rectangle boundary integrals
tend to L, the oriented vertical difference also tends to L. Subtract the
horizontal difference from the defining four-edge expression. This isolates
the vertical side of a contour limit without extra integrability premises. -/
theorem tendsto_vertical_difference_of_boundary_limit (f : ℂ → ℂ) (a b : ℝ) (U B : ℕ → ℝ) (L : ℂ)
    (hupper :
      Filter.Tendsto (fun n ↦ ∫ x in a..b, f ((x : ℂ) + U n * Complex.I)) Filter.atTop (nhds 0))
    (hlower :
      Filter.Tendsto (fun n ↦ ∫ x in a..b, f ((x : ℂ) + B n * Complex.I)) Filter.atTop (nhds 0))
    (hboundary :
      Filter.Tendsto
        (fun n ↦
          rectangleBoundaryIntegral f ((a : ℂ) + B n * Complex.I) ((b : ℂ) + U n * Complex.I))
        Filter.atTop (nhds L)) :
    Filter.Tendsto
      (fun n ↦
        Complex.I * (∫ y in B n..U n, f ((b : ℂ) + y * Complex.I)) -
          Complex.I * (∫ y in B n..U n, f ((a : ℂ) + y * Complex.I)))
      Filter.atTop (nhds L) := by
  have ht := hboundary.sub (hlower.sub hupper)
  simp only [sub_zero] at ht
  apply ht.congr
  intro n
  simp only [rectangleBoundaryIntegral, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
    mul_one, sub_zero, add_zero, zero_add, smul_eq_mul]
  ring

end PseudoPrime.AnalyticNumberTheory.RectangleGeometry

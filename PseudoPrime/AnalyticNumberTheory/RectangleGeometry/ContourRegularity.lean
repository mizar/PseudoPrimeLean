/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Analysis.Complex.Basic

/-!
# Generic contour-segment regularity

These lemmas only express the geometric fact that a horizontal or vertical segment avoids a
complex singularity set when the corresponding imaginary or real coordinates are avoided. They
do not mention Dirichlet `L`-functions, Mellin kernels, or the fixed points `0` and `1`.
-/

namespace PseudoPrime.AnalyticNumberTheory.RectangleGeometry

/-- A horizontal segment is outside a set when its imaginary coordinate is avoided by that set. -/
theorem horizontal_segment_subset_compl_of_im_avoid {S : Set ℂ} {c a b : ℝ}
    (havoid : ∀ s ∈ S, s.im ≠ c) : ∀ t ∈ Set.uIcc a b, t + c * Complex.I ∉ S := by
  intro t ht hs
  exact
    havoid _ hs
      (by
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_re, mul_zero, Complex.I_im, mul_one, add_zero, zero_add])

/-- A vertical segment is outside a set when its real coordinate is avoided by that set. -/
theorem vertical_segment_subset_compl_of_re_avoid {S : Set ℂ} {c a b : ℝ}
    (havoid : ∀ s ∈ S, s.re ≠ c) : ∀ t ∈ Set.uIcc a b, c + t * Complex.I ∉ S := by
  intro t ht hs
  exact
    havoid _ hs
      (by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero])

end RectangleGeometry

end AnalyticNumberTheory

end PseudoPrime

/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Basic rectangular regions

This module contains the compact closed axis-aligned rectangle used by analytic zero-counting
arguments.  It is independent of contour integration and of a downstream-consumer-specific kernel.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Rectangle

/-- The closed axis-aligned box determined by complex corners `z` and `w`, using unordered
closed intervals in both coordinates. No ordering of the corners is required. This is the
compact region used to localize zeros in rectangular contour arguments. -/
def rectangleClosedBox (z w : ℂ) : Set ℂ :=
  Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im

/-- For any two complex corners, their closed rectangular box is compact. The proof combines
compactness of the two unordered real intervals via `reProdIm`; this supplies compactness for
finite-zero and contour-localization arguments. -/
theorem isCompact_rectangleClosedBox (z w : ℂ) : IsCompact (rectangleClosedBox z w) := by
  exact isCompact_uIcc.reProdIm isCompact_uIcc

/-- The closed rectangle is a neighborhood of a point exactly when that
point lies strictly between both pairs of corner coordinates. Compute the
interior of the product of closed real intervals. This characterizes whether
a rectangle encloses a pole for contour integration without external geometry. -/
theorem rectangleClosedBox_mem_nhds_iff {z w p : ℂ} :
    rectangleClosedBox z w ∈ nhds p ↔ p ∈ (Set.uIoo z.re w.re) ×ℂ (Set.uIoo z.im w.im) := by
  simp only [← mem_interior_iff_mem_nhds, rectangleClosedBox, Complex.interior_reProdIm, Set.uIoo,
    Set.uIcc, interior_Icc]

end PseudoPrime.AnalyticNumberTheory.Rectangle

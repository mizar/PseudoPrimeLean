/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Basic rectangular regions

This module contains the compact closed axis-aligned rectangle used by analytic zero-counting
arguments.  It is independent of contour integration and of a downstream-consumer-specific kernel.
-/

namespace PseudoPrime.AnalyticNumberTheory.Rectangle

/-- The closed axis-aligned box determined by two complex corners. -/
def rectangleClosedBox (z w : ℂ) : Set ℂ :=
  Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im

/-- A closed axis-aligned rectangle is compact. -/
theorem isCompact_rectangleClosedBox (z w : ℂ) :
    IsCompact (rectangleClosedBox z w) := by
  exact isCompact_uIcc.reProdIm isCompact_uIcc

end PseudoPrime.AnalyticNumberTheory.Rectangle

/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.MellinInversion

/-! # Inverse Mellin integration on a vertical line -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Inverse Mellin integral of `K` on the vertical line of real part `c`.
The parameterization `s = c + it` cancels the `i` in `ds/(2πi)`.
For an admissible kernel it agrees on all the allowed vertical lines. -/
noncomputable def inverseMellin (K : ℂ → ℂ) (c u : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    MeasureTheory.integral MeasureTheory.volume
      (fun t : ℝ ↦ K ((c : ℂ) + Complex.I * t) * (u : ℂ) ^ (-((c : ℂ) + Complex.I * t)))

end PseudoPrime.Analysis

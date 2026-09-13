/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Elementary limits for symmetric interval integrals

This file collects limit facts independent of any particular contour kernel or number-theoretic
construction.
-/

namespace PseudoPrime.Analysis

/-- The negative identity tends to `-∞` when its argument tends to `+∞`. -/
theorem tendsto_neg_atTop_atBot' : Filter.Tendsto (fun T : ℝ ↦ -T) Filter.atTop Filter.atBot := by
  rw [Filter.tendsto_atBot]
  intro b
  filter_upwards [Filter.eventually_ge_atTop (-b)] with T hT
  linarith

end PseudoPrime.Analysis

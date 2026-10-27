/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Tactic

/-! # Normalized weighted differences from positive Poisson endpoint comparisons -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For positive h and nonnegative z, an endpoint Poisson comparison between a,b
bounds the normalized signed weighted difference directly. Identify the residual as
z times the nonnegative comparison error over h*(1+2h). No differentiability or
independent norm estimate is required. This controls coupled real-axis differences. -/
theorem poisson_endpoint_weighted_gap_le {h : ℝ} (hh : 0 < h) (a b L z : ℝ) (hz : 0 ≤ z)
    (he : a + L / 2 ≤ (1 + 2 * h) * (b + L / 2)) :
    ((1 - z) * L + a - z * b) / h ≤
      ((1 - z) / h) * L / 2 + (((1 - z) / h + 2) / (1 + 2 * h)) * (a + L / 2) := by
  have hd : 0 < 1 + 2 * h := by linarith only [hh]
  have hid :
    (((1 - z) / h) * L / 2 + (((1 - z) / h + 2) / (1 + 2 * h)) * (a + L / 2)) -
        (((1 - z) * L + a - z * b) / h) =
      z * ((1 + 2 * h) * (b + L / 2) - (a + L / 2)) / (h * (1 + 2 * h)) := by
    field_simp [hh.ne', hd.ne']
    ring
  apply sub_nonneg.mp
  rw [hid]
  exact div_nonneg (mul_nonneg hz (sub_nonneg.mpr he)) (mul_pos hh hd).le

end PseudoPrime.Analysis

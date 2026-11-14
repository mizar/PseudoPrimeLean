/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.CriticalNormalizedSign
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PreciseRotatedBounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PreciseChecks.Node004

/-! # Margin at the fourth low-zero lower endpoint -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- At `t = 31155 / 1024`, the normalized critical-line zeta value exceeds `9/100000`.
The result is unconditional and uses the internally checked finite approximation together
with the explicit Euler–Maclaurin and phase errors. -/
theorem low_zero_fourth_lower_margin :
    (9 / 100000 : ℝ) < RiemannXi.normalizedZeta (31155 / 1024) := by
  have hc := endpoint004_precise_check
  have hraw : (913 / 10000000 : ℝ) < ((endpointPreciseRotated (31155 / 1024)).1 : ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hc.2
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
    exact h
  have herr :=
    abs_le.mp (abs_endpoint_precise_zeta (31155 / 1024) (by norm_num only) (by norm_num only) hc.1)
  linarith only [hraw, herr.1]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta

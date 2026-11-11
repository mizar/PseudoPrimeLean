/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.EulerLog
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaHalfStripBounds

/-! # Explicit bound for the zeta Euler logarithm -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- On `Re s ≥ 3/2`, the Euler logarithm has norm at most `log(14/5)`.
Combine its real-axis majorant with the explicit zeta bound in that half-plane. -/
theorem norm_backlundZetaLog_le_const {s : ℂ} (hs : (3 / 2 : ℝ) ≤ s.re) :
    ‖AnalyticNumberTheory.RiemannZeta.backlundZetaLog s‖ ≤ Real.log (14 / 5) := by
  have hs1 : 1 < s.re := by linarith only [hs]
  have hzpos : 0 < (riemannZeta (s.re : ℂ)).re :=
    (Complex.pos_iff.mp (riemannZeta_pos_of_one_lt hs1)).1
  have hz :=
    AnalyticNumberTheory.RiemannZeta.norm_zeta_lt_fourteen_fifths (s := (s.re : ℂ))
      (by simpa only [Complex.ofReal_re] using hs)
  have hle : (riemannZeta (s.re : ℂ)).re ≤ (14 / 5 : ℝ) := (Complex.re_le_norm _).trans hz.le
  exact
    (AnalyticNumberTheory.RiemannZeta.norm_backlundZetaLog_le hs1).trans (Real.log_le_log hzpos hle)

end PseudoPrime.PrimeTestBounds.MillerRabin

/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaFinitePrefix
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaMiddleSinc
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevThetaHighRH
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Global lower Lee–Nosal bound for theta -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

/-- Under RH, the lower Lee–Nosal estimate for theta holds for every real x at least 2657.
Join the finite prefix, the sinc middle band and the analytic high range. -/
theorem theta_lower_lee_nosal_of_RH (hRH : RiemannHypothesis) {x : ℝ} (hx : 2657 ≤ x) :
    (x - Chebyshev.theta x) / Real.sqrt x ≤
      Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) := by
  rcases le_total x 42488064 with h | h
  · exact theta_lower_2657_42488064 hx h
  have hp : 0 < x := lt_of_lt_of_le (by norm_num only) hx
  rcases le_total (53 / 2 : ℝ) (Real.log x) with hu | hu
  · exact Arithmetic.theta_lower_log_half53 hRH hp hu
  have hc :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 42488064 25 12 (35 / 2) 18 = true from by
        decide +kernel)
  have hl : 35 / 2 ≤ Real.log x := by
    apply le_trans _ (Real.log_le_log (by norm_num only : (0 : ℝ) < 42488064) h)
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hc.1
  simpa only [Real.exp_log hp] using middleTheta_le hRH hl hu

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

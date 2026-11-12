/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiLogScale265RH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiLogRemainder265

/-! # RH normalized Chebyshev bound from logarithmic height twenty-six and one half -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH and `L ≥ 53/2`, bound the normalized Chebyshev error by the
logarithmic main term plus `33/50`. The refined zero-sum constant and the
certified exponential remainder give the estimate. -/
theorem psi_error_main265_of_RH (hRH : RiemannHypothesis) {L : ℝ} (hL : (53 / 2 : ℝ) ≤ L) :
    |Chebyshev.psi (Real.exp L) - Real.exp L| / Real.exp (L / 2) ≤
      ((L / 2 - Real.log L) ^ 2 + 2 * (L / 2 - Real.log L) + 2 * Real.log (2 * Real.pi) + L) /
          (2 * Real.pi) +
        33 / 50 := by
  have h := psi_error_log_scale265_065 hRH hL
  have hr := scale265_remainder_le hL
  dsimp only at h hr
  have hm :
    |Chebyshev.psi (Real.exp L) - Real.exp L| / Real.exp (L / 2) ≤
      ((L / 2 - Real.log L) ^ 2 + 2 * (L / 2 - Real.log L) + 2 * Real.log (2 * Real.pi) + L) /
          (2 * Real.pi) +
        13 / 20 +
        ((L / (Real.pi * Real.exp (L / 2))) * (L / 2 - Real.log L) ^ 2 / (4 * Real.pi) +
          (13 / 40 : ℝ) * (L / (Real.pi * Real.exp (L / 2))) +
          (L / (Real.pi * Real.exp (L / 2))) * (L / 2 - Real.log L + Real.log (2 * Real.pi)) /
            Real.pi +
          3 / Real.exp (L / 2)) := by
    convert h using 1
    ring
  have hδ : 0 ≤ L / (Real.pi * Real.exp (L / 2)) :=
    div_nonneg (by linarith only [hL]) (mul_nonneg Real.pi_pos.le (Real.exp_pos _).le)
  linarith only [hm, hr, hδ]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta

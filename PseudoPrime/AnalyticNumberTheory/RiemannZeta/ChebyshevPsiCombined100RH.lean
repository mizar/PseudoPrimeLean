/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiCombinedGeneralRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCombinedBudget100RH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiCombinedScaleGeneralRH

/-! # Chebyshev error from a height-100 zero head -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, the height-100 count and reciprocal head bounds give the
combined-zero ψ error estimate with constant `1/25`. The geometric smoothing
bounds and the cutoff `T ≥ 100` remain explicit. -/
theorem psi_error_combined100 (hRH : RiemannHypothesis) (h100 : zeroCount 100 = 58)
    (hhead : zeroReciprocalSum 100 ≤ 11846 / 10000) {T x h A : ℝ} (hT : 100 ≤ T) (hh : 0 < h)
    (hx : 1 < x - h) (hA : 0 ≤ A) (hsqrt : Real.sqrt (x + h) ≤ A)
    (htail : ((x + h) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ)) / h ≤ A * T) :
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) +
        A *
          (((Real.log (T / (2 * Real.pi))) ^ 2 + 2 * Real.log (T / (2 * Real.pi)) + 2) /
                  (2 * Real.pi) +
                1 / 25 -
              (3 / 8 : ℝ) / T +
            1 / (15 * T ^ 2)) +
        1 / h := by
  exact
    psi_error_of_combined hRH (by linarith only [hT]) hh hx hA hsqrt htail
      (combined_zero_budget100 hRH h100 hhead hT)

/-- Under RH and the height-100 count and head bounds, a relative smoothing
width with cutoff at least 100 gives the normalized ψ error estimate with
combined-zero constant `1/25`. -/
theorem psi_error_combined100_scaled (hRH : RiemannHypothesis) (h100 : zeroCount 100 = 58)
    (hhead : zeroReciprocalSum 100 ≤ 11846 / 10000) {x δ : ℝ} (hx : 0 < x) (hd : 0 < δ)
    (hd2 : δ ≤ 1 / 2) (hleft : 1 < x - x * δ) (hcut : 100 ≤ 2 / δ) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤
      Real.sqrt x * δ / 2 + Real.log (2 * Real.pi) / Real.sqrt x +
        (1 + δ) *
          (((Real.log ((2 / δ) / (2 * Real.pi))) ^ 2 + 2 * Real.log ((2 / δ) / (2 * Real.pi)) + 2) /
                  (2 * Real.pi) +
                1 / 25 -
              (3 / 8 : ℝ) / (2 / δ) +
            1 / (15 * (2 / δ) ^ 2)) +
        1 / (x * δ * Real.sqrt x) := by
  exact psi_error_combined_scale hRH hx hd hd2 hleft (combined_zero_budget100 hRH h100 hhead hcut)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta

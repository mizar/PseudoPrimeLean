/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiIntegratedRH
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroReciprocalIntegratedRH

/-! # Improved integrated ψ envelopes -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, the integrated ψ envelope holds with the table-free
constant `33/100` for every admissible smoothing scale. -/
theorem psi_error_integrated_thirty_three (hRH : RiemannHypothesis) {x δ : ℝ} (hx : 0 < x)
    (hd : 0 < δ) (hd2 : δ ≤ 1 / 2) (hleft : 1 < x - x * δ) (hT : 100 ≤ 2 / δ) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤
      Real.sqrt x * δ / 2 + Real.log (2 * Real.pi) / Real.sqrt x +
        (1 + δ) *
          (((Real.log ((2 / δ) / (2 * Real.pi))) ^ 2 + 2 * Real.log ((2 / δ) / (2 * Real.pi)) + 2) /
              (2 * Real.pi) +
            33 / 100 +
            ((29 / 27 : ℝ) * (16 + (7 / 5 : ℝ) * Real.log (2 / δ)) +
                (7 / 5 : ℝ) * (37 / 162 + 2 * Real.log 3 / 27) +
                1 / 10) /
              (2 / δ) ^ 2) +
        1 / (x * δ * Real.sqrt x) := by
  exact
    psi_error_integrated_of_constant hRH hx hd hd2 hleft hT
      (zeroReciprocalConstant_le_thirty_three hRH)

/-- Under RH, the exact height-100 count and reciprocal-sum bound imply
the integrated ψ envelope with the target constant `-317/10000`.
The finite zero conditions are explicit hypotheses. -/
theorem psi_error_integrated_sharp_of_head (hRH : RiemannHypothesis) {x δ : ℝ} (hx : 0 < x)
    (hd : 0 < δ) (hd2 : δ ≤ 1 / 2) (hleft : 1 < x - x * δ) (hT : 100 ≤ 2 / δ)
    (hc : zeroCount 100 = 58) (hs : zeroReciprocalSum 100 ≤ (11846 / 10000 : ℝ)) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤
      Real.sqrt x * δ / 2 + Real.log (2 * Real.pi) / Real.sqrt x +
        (1 + δ) *
          (((Real.log ((2 / δ) / (2 * Real.pi))) ^ 2 + 2 * Real.log ((2 / δ) / (2 * Real.pi)) + 2) /
              (2 * Real.pi) +
            (-(317 / 10000 : ℝ)) +
            ((29 / 27 : ℝ) * (16 + (7 / 5 : ℝ) * Real.log (2 / δ)) +
                (7 / 5 : ℝ) * (37 / 162 + 2 * Real.log 3 / 27) +
                1 / 10) /
              (2 / δ) ^ 2) +
        1 / (x * δ * Real.sqrt x) := by
  exact
    psi_error_integrated_of_constant hRH hx hd hd2 hleft hT
      (zeroReciprocalConstant_le_sharp hRH hc hs)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta

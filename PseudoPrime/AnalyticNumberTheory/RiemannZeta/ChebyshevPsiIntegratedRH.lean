/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCombinedAbelRH
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiCombinedScaleGeneralRH

/-! # Chebyshev smoothing with the integrated zero-count remainder -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, if the smoothing scale has `0 < δ ≤ 1/2`, its lower endpoint
exceeds one, and its zero cutoff `2/δ` is at least 100, the normalized ψ
error is bounded using the exact reciprocal-sum limiting constant and the
integrated zero-count remainder. No external zero table is assumed. -/
theorem psi_error_integrated_scale (hRH : RiemannHypothesis) {x δ : ℝ} (hx : 0 < x) (hd : 0 < δ)
    (hd2 : δ ≤ 1 / 2) (hleft : 1 < x - x * δ) (hT : 100 ≤ 2 / δ) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤
      Real.sqrt x * δ / 2 + Real.log (2 * Real.pi) / Real.sqrt x +
        (1 + δ) *
          (((Real.log ((2 / δ) / (2 * Real.pi))) ^ 2 + 2 * Real.log ((2 / δ) / (2 * Real.pi)) + 2) /
              (2 * Real.pi) +
            zeroReciprocalConstant +
            ((29 / 27 : ℝ) * (16 + (7 / 5 : ℝ) * Real.log (2 / δ)) +
                (7 / 5 : ℝ) * (37 / 162 + 2 * Real.log 3 / 27) +
                1 / 10) /
              (2 / δ) ^ 2) +
        1 / (x * δ * Real.sqrt x) := by
  exact psi_error_combined_scale hRH hx hd hd2 hleft (combined_zero_integrated_bound hRH hT)

/-- Under RH, any upper bound `C` for the reciprocal-sum limiting constant
can be substituted into the integrated ψ envelope. The nonnegative
smoothing factor preserves the comparison. -/
theorem psi_error_integrated_of_constant (hRH : RiemannHypothesis) {x δ C : ℝ} (hx : 0 < x)
    (hd : 0 < δ) (hd2 : δ ≤ 1 / 2) (hleft : 1 < x - x * δ) (hT : 100 ≤ 2 / δ)
    (hC : zeroReciprocalConstant ≤ C) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤
      Real.sqrt x * δ / 2 + Real.log (2 * Real.pi) / Real.sqrt x +
        (1 + δ) *
          (((Real.log ((2 / δ) / (2 * Real.pi))) ^ 2 + 2 * Real.log ((2 / δ) / (2 * Real.pi)) + 2) /
              (2 * Real.pi) +
            C +
            ((29 / 27 : ℝ) * (16 + (7 / 5 : ℝ) * Real.log (2 / δ)) +
                (7 / 5 : ℝ) * (37 / 162 + 2 * Real.log 3 / 27) +
                1 / 10) /
              (2 / δ) ^ 2) +
        1 / (x * δ * Real.sqrt x) := by
  have h := psi_error_integrated_scale hRH hx hd hd2 hleft hT
  have hm := mul_le_mul_of_nonneg_left hC (show 0 ≤ 1 + δ by linarith only [hd])
  nlinarith only [h, hm]

/-- Under RH, the integrated ψ envelope holds with the table-free
constant `2 / 5` at every admissible smoothing scale with zero cutoff at
least 100. This specializes the limiting-constant bound proved internally. -/
theorem psi_error_integrated_table_free (hRH : RiemannHypothesis) {x δ : ℝ} (hx : 0 < x)
    (hd : 0 < δ) (hd2 : δ ≤ 1 / 2) (hleft : 1 < x - x * δ) (hT : 100 ≤ 2 / δ) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤
      Real.sqrt x * δ / 2 + Real.log (2 * Real.pi) / Real.sqrt x +
        (1 + δ) *
          (((Real.log ((2 / δ) / (2 * Real.pi))) ^ 2 + 2 * Real.log ((2 / δ) / (2 * Real.pi)) + 2) /
              (2 * Real.pi) +
            2 / 5 +
            ((29 / 27 : ℝ) * (16 + (7 / 5 : ℝ) * Real.log (2 / δ)) +
                (7 / 5 : ℝ) * (37 / 162 + 2 * Real.log 3 / 27) +
                1 / 10) /
              (2 / δ) ^ 2) +
        1 / (x * δ * Real.sqrt x) := by
  exact
    psi_error_integrated_of_constant hRH hx hd hd2 hleft hT
      (zeroReciprocalConstant_le_two_fifths hRH)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.OrdinateTail
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiZeroSplitRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.OrdinateTailBudgetRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroReciprocalBudgetRH

/-! # Chebyshev error with the sharp zero-count budget -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, a full inverse-square ordinate-tail bound and `T ≥ 2πe` give a
Chebyshev error estimate with reciprocal-sum constant `53/100`. The tail bound
is kept as a parameter so that sharper tail estimates can be substituted. -/
theorem psi_error_budget_tail (hRH : RiemannHypothesis) {T x h C : ℝ}
    (hT : 2 * Real.pi * Real.exp 1 ≤ T) (hh : 0 < h) (hx : 1 < x - h) (hTail : ordinateTail T ≤ C) :
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) +
        Real.sqrt (x + h) * (Real.log (T / (2 * Real.pi)) ^ 2 / (2 * Real.pi) + 53 / 100) +
        ((x + h) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ)) / h * C +
        1 / h := by
  have hT0 : 0 ≤ T :=
    (mul_pos (mul_pos (by norm_num only : (0 : ℝ) < 2) Real.pi_pos) (Real.exp_pos 1)).le.trans hT
  have hC :
    ∀ m : ℕ,
      (∑
          ρ ∈
            ((riemannZetaZerosInAnyRectangle (unifiedRectangleLower m)
                      (unifiedTauRectangleUpper 2 m)).filter
                  (fun ρ ↦ ¬ρ.re < 0)).filter
              (fun ρ ↦ ¬|ρ.im| ≤ T),
          (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) ≤
        C := by
    intro m
    let S :=
      ((riemannZetaZerosInAnyRectangle (unifiedRectangleLower m)
                (unifiedTauRectangleUpper 2 m)).filter
            (fun ρ ↦ ¬ρ.re < 0)).filter
        (fun ρ ↦ ¬|ρ.im| ≤ T)
    have hs :=
      finite_ordinate_tail_le hRH S T
        (fun ρ hρ ↦
          (mem_riemannZetaZerosInAnyRectangle_iff.mp
              (Finset.mem_filter.mp (Finset.mem_filter.mp hρ).1).1).2)
        (fun ρ hρ ↦ not_lt.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hρ).1).2)
        (fun ρ hρ ↦ lt_of_not_ge (Finset.mem_filter.mp hρ).2)
    exact hs.trans hTail
  have hlo := zeroReciprocal_bound053_of_RH hRH hT
  have hsplit := psi_error_of_zero_split hRH hT0 hh hx hC
  have hm := mul_le_mul_of_nonneg_left hlo (Real.sqrt_nonneg (x + h))
  linarith only [hsplit, hm]

/-- Under RH and `T ≥ 2 * π * exp 1`, the explicit zero-count budgets bound the
Chebyshev error with reciprocal constant `53/100` and the detailed ordinate
tail. This form is used before selecting the logarithmic smoothing scale. -/
theorem psi_error_budget_of_RH (hRH : RiemannHypothesis) {T x h : ℝ}
    (hT : 2 * Real.pi * Real.exp 1 ≤ T) (hh : 0 < h) (hx : 1 < x - h) :
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) +
        Real.sqrt (x + h) * (Real.log (T / (2 * Real.pi)) ^ 2 / (2 * Real.pi) + 53 / 100) +
        ((x + h) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ)) / h *
          ((Real.log (T / (2 * Real.pi)) + 1) / (Real.pi * T) +
            ((3 / 2 : ℝ) * Real.log T + 271 / 40) / T ^ 2 +
            2 / (3 * T ^ 3)) +
        1 / h := by
  exact psi_error_budget_tail hRH hT hh hx (ordinateTail_budget_of_RH hRH hT)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta

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
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroReciprocalFrom40

/-! # Chebyshev error with a height-40 reciprocal budget -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, `T ≥ 40` and an ordinate-tail bound `C` give a Chebyshev error
bound with reciprocal-sum constant `2/5`. The finite zero split and the
zero-mass-based reciprocal estimate supply its two zero contributions. -/
theorem psi_error_budget40_tail (hRH : RiemannHypothesis) {T x h C : ℝ} (hT : 40 ≤ T) (hh : 0 < h)
    (hx : 1 < x - h) (hTail : ordinateTail T ≤ C) :
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) +
        Real.sqrt (x + h) * (Real.log (T / (2 * Real.pi)) ^ 2 / (2 * Real.pi) + 2 / 5) +
        ((x + h) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ)) / h * C +
        1 / h := by
  have hT0 : 0 ≤ T := by linarith only [hT]
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
  have hlo := zeroReciprocal_bound_two_fifths hRH hT
  have hsplit := psi_error_of_zero_split hRH hT0 hh hx hC
  have hm := mul_le_mul_of_nonneg_left hlo (Real.sqrt_nonneg (x + h))
  linarith only [hsplit, hm]

/-- Under RH and `T ≥ 40`, the explicit ordinate-tail budget gives a
Chebyshev error bound with reciprocal-sum constant `2/5`. The smoothing
width remains a parameter for later scale selection. -/
theorem psi_error_budget40_of_RH (hRH : RiemannHypothesis) {T x h : ℝ} (hT : 40 ≤ T) (hh : 0 < h)
    (hx : 1 < x - h) :
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) +
        Real.sqrt (x + h) * (Real.log (T / (2 * Real.pi)) ^ 2 / (2 * Real.pi) + 2 / 5) +
        ((x + h) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ)) / h *
          ((Real.log (T / (2 * Real.pi)) + 1) / (Real.pi * T) +
            ((3 / 2 : ℝ) * Real.log T + 271 / 40) / T ^ 2 +
            2 / (3 * T ^ 3)) +
        1 / h := by
  have hbase : 2 * Real.pi * Real.exp 1 ≤ (40 : ℝ) := by
    have hp :=
      mul_le_mul Real.pi_lt_four.le Real.exp_one_lt_three.le (Real.exp_pos 1).le
        (by norm_num only : (0 : ℝ) ≤ 4)
    nlinarith only [hp]
  exact psi_error_budget40_tail hRH hT hh hx (ordinateTail_budget_of_RH hRH (hbase.trans hT))

end PseudoPrime.AnalyticNumberTheory.RiemannZeta

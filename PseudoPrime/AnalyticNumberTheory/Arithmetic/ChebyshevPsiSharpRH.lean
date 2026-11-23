/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.OrdinateTail
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiOrdinateTailRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.OrdinateTailRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroReciprocalBoundRH

/-! # Chebyshev error with a refined reciprocal zero sum -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Under RH, the explicit ordinate-tail hypothesis and `T ≥ 2πe` imply
a Chebyshev error bound with the refined reciprocal-zero entrance constant.
The proof combines the zero-split formula with the RH reciprocal-sum bound. -/
theorem psi_error_sharp_tail (hRH : RiemannHypothesis) {T x h : ℝ}
    (hT : 2 * Real.pi * Real.exp 1 ≤ T) (hh : 0 < h) (hx : 1 < x - h)
    (hTail : RiemannZeta.ordinateTail T ≤ Real.log T / (Real.pi * T)) :
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) +
        Real.sqrt (x + h) *
          ((Real.log (T / (2 * Real.pi))) ^ 2 / (2 * Real.pi) + 4 / 5 - 1 / (2 * Real.pi)) +
        ((x + h) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ)) / h * (Real.log T / (Real.pi * T)) +
        1 / h := by
  have hT0 : 0 ≤ T :=
    (mul_pos (mul_pos (by norm_num only : (0 : ℝ) < 2) Real.pi_pos) (Real.exp_pos 1)).le.trans hT
  have hC :
    ∀ m : ℕ,
      (∑
          ρ ∈
            ((RiemannZeta.riemannZetaZerosInAnyRectangle (RiemannZeta.unifiedRectangleLower m)
                      (RiemannZeta.unifiedTauRectangleUpper 2 m)).filter
                  (fun ρ ↦ ¬ρ.re < 0)).filter
              (fun ρ ↦ ¬|ρ.im| ≤ T),
          (RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) ≤
        Real.log T / (Real.pi * T) := by
    intro m
    let S :=
      ((RiemannZeta.riemannZetaZerosInAnyRectangle (RiemannZeta.unifiedRectangleLower m)
                (RiemannZeta.unifiedTauRectangleUpper 2 m)).filter
            (fun ρ ↦ ¬ρ.re < 0)).filter
        (fun ρ ↦ ¬|ρ.im| ≤ T)
    have hs :=
      RiemannZeta.finite_ordinate_tail_le hRH S T
        (fun ρ hρ ↦
          (RiemannZeta.mem_riemannZetaZerosInAnyRectangle_iff.mp
              (Finset.mem_filter.mp (Finset.mem_filter.mp hρ).1).1).2)
        (fun ρ hρ ↦ not_lt.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hρ).1).2)
        (fun ρ hρ ↦ lt_of_not_ge (Finset.mem_filter.mp hρ).2)
    exact hs.trans hTail
  have hlo := RiemannZeta.zeroReciprocal_bound_of_RH hRH hT
  have hh' := RiemannZeta.psi_error_of_zero_split hRH hT0 hh hx hC
  have hm := mul_le_mul_of_nonneg_left hlo (Real.sqrt_nonneg (x + h))
  linarith only [hh', hm]

/-- Under RH, the refined zero-split bound holds at every cutoff `T ≥ 1000`.
The RH ordinate-tail estimate supplies the tail hypothesis. -/
theorem psi_error_sharp_of_RH (hRH : RiemannHypothesis) {T x h : ℝ} (hT : 1000 ≤ T) (hh : 0 < h)
    (hx : 1 < x - h) :
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) +
        Real.sqrt (x + h) *
          ((Real.log (T / (2 * Real.pi))) ^ 2 / (2 * Real.pi) + 4 / 5 - 1 / (2 * Real.pi)) +
        ((x + h) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ)) / h * (Real.log T / (Real.pi * T)) +
        1 / h := by
  have hbase : 2 * Real.pi * Real.exp 1 ≤ T := by
    have hp :=
      mul_le_mul Real.pi_lt_four.le Real.exp_one_lt_three.le (Real.exp_pos 1).le
        (by norm_num only : (0 : ℝ) ≤ 4)
    nlinarith only [hp, hT]
  exact psi_error_sharp_tail hRH hbase hh hx (RiemannZeta.ordinateTail_coarse_of_RH hRH hT)

end PseudoPrime.AnalyticNumberTheory.Arithmetic

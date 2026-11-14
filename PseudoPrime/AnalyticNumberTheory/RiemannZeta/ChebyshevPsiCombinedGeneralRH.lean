/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.OrdinateTail
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeightCounting
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiZeroSplitRH

/-! # Chebyshev error from a general combined zero budget -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, common geometric bounds `A` and `A*T` for the low and high
zero terms transfer any combined zero budget `B` to the ψ error. This allows
different height-dependent zero estimates to share the same smoothing step. -/
theorem psi_error_of_combined (hRH : RiemannHypothesis) {T x h A B : ℝ} (hT : 0 ≤ T) (hh : 0 < h)
    (hx : 1 < x - h) (hA : 0 ≤ A) (hsqrt : Real.sqrt (x + h) ≤ A)
    (htail : ((x + h) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ)) / h ≤ A * T)
    (hbudget : zeroReciprocalSum T + T * ordinateTail T ≤ B) :
    |Chebyshev.psi x - x| ≤ h / 2 + Real.log (2 * Real.pi) + A * B + 1 / h := by
  have hC :
    ∀ m : ℕ,
      (∑
          ρ ∈
            ((riemannZetaZerosInAnyRectangle (unifiedRectangleLower m)
                      (unifiedTauRectangleUpper 2 m)).filter
                  (fun ρ ↦ ¬ρ.re < 0)).filter
              (fun ρ ↦ ¬|ρ.im| ≤ T),
          (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) ≤
        ordinateTail T := by
    intro m
    let S :=
      ((riemannZetaZerosInAnyRectangle (unifiedRectangleLower m)
                (unifiedTauRectangleUpper 2 m)).filter
            (fun ρ ↦ ¬ρ.re < 0)).filter
        (fun ρ ↦ ¬|ρ.im| ≤ T)
    exact
      finite_ordinate_tail_le hRH S T
        (fun ρ hρ ↦
          (mem_riemannZetaZerosInAnyRectangle_iff.mp
              (Finset.mem_filter.mp (Finset.mem_filter.mp hρ).1).1).2)
        (fun ρ hρ ↦ not_lt.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hρ).1).2)
        (fun ρ hρ ↦ lt_of_not_ge (Finset.mem_filter.mp hρ).2)
  have hS : 0 ≤ zeroReciprocalSum T := by
    rw [zeroReciprocalSum_eq]
    exact Finset.sum_nonneg (fun ρ _ ↦ div_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
  have hU : 0 ≤ ordinateTail T := by
    rw [ordinateTail_eq]
    exact tsum_nonneg (fun ρ ↦ (ordinateTailWeight_bound hRH T ρ).1)
  have hsplit := psi_error_of_zero_split hRH hT hh hx hC
  have hs := mul_le_mul_of_nonneg_right hsqrt hS
  have ht := mul_le_mul_of_nonneg_right htail hU
  have hc := mul_le_mul_of_nonneg_left hbudget hA
  nlinarith only [hsplit, hs, ht, hc]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta

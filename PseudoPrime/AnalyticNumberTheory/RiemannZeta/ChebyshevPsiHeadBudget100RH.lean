/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiHeadSplitRH
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.OrdinateTail
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCombinedAbove100RH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroReciprocalInterval

/-! # ψ error from a signed head and the height-100 combined budget -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH and the height-100 zero count, bounds on the signed head over
both smoothing intervals give the displayed ψ error estimate. The zeros
above 100 use the combined reciprocal and inverse-square budget. -/
theorem psi_error_head_budget100 (hRH : RiemannHypothesis) (h100 : zeroCount 100 = 58)
    {T x h D H : ℝ} (hT : 100 ≤ T) (hh : 0 < h) (hx : 1 < x - h) (hD : 0 ≤ D)
    (hsqrt : Real.sqrt (x + h) ≤ D) (htail : ((x + h) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ)) / h ≤ D * T)
    (hlo :
      |(∑ ρ ∈ zerosUpTo 100,
              (riemannZetaZeroMultiplicity ρ : ℂ) *
                  ((x : ℂ) ^ (ρ + 1) - ((x - h : ℝ) : ℂ) ^ (ρ + 1)) /
                (ρ * (ρ + 1))).re| ≤
        h * H)
    (hhi :
      |(∑ ρ ∈ zerosUpTo 100,
              (riemannZetaZeroMultiplicity ρ : ℂ) *
                  (((x + h : ℝ) : ℂ) ^ (ρ + 1) - (x : ℂ) ^ (ρ + 1)) /
                (ρ * (ρ + 1))).re| ≤
        h * H) :
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) + H +
        D *
          (((Real.log (T / (2 * Real.pi))) ^ 2 + 2 * Real.log (T / (2 * Real.pi)) + 2) /
                (2 * Real.pi) -
              143 / 125 -
              (3 / 8 : ℝ) / T +
            1 / (15 * T ^ 2)) +
        1 / h := by
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
  have hR : 0 ≤ zeroReciprocalSum T - zeroReciprocalSum 100 := by
    rw [← zeroReciprocal_interval (by norm_num only : (0 : ℝ) ≤ 100) hT]
    exact Finset.sum_nonneg (fun ρ _ ↦ div_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
  have hU : 0 ≤ ordinateTail T := by
    rw [ordinateTail_eq]
    exact tsum_nonneg (fun ρ ↦ (ordinateTailWeight_bound hRH T ρ).1)
  have hsplit := psi_error_retain_head hRH (by norm_num only : (0 : ℝ) ≤ 100) hT hh hx hC hlo hhi
  have hs := mul_le_mul_of_nonneg_right hsqrt hR
  have ht := mul_le_mul_of_nonneg_right htail hU
  have hc := mul_le_mul_of_nonneg_left (combined_zero_above100 hRH h100 hT) hD
  nlinarith only [hsplit, hs, ht, hc]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta

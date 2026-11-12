/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountTail
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountTailError
import PseudoPrime.Analysis.LogBudgetIntegral

/-! # Finite inverse-square tails from logarithmic zero-count budgets -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- A logarithmic zero-count main term with error `α log t + β + γ / t`
bounds the finite inverse-square zero tail on `1 < a ≤ b`. The estimate
retains the upper and lower endpoint terms for subsequent passage to infinity. -/
theorem finite_tail_of_log_budget {a b k c d α β γ : ℝ} (ha : 1 < a) (hab : a ≤ b)
    (hM : ContinuousOn (fun t ↦ k * t * (Real.log t - c - 1) + d) (Set.Icc a b))
    (hE : ContinuousOn (fun t ↦ α * Real.log t + β + γ / t) (Set.Icc a b))
    (hQ :
      ∀ t ∈ Set.Icc a b,
        |zeroCount t - (k * t * (Real.log t - c - 1) + d)| ≤ α * Real.log t + β + γ / t) :
    (∑ ρ ∈ (zerosUpTo b).filter (fun ρ ↦ a < |ρ.im|),
        (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) ≤
      k * (Real.log a - c + 1) / a + (2 * α * Real.log a + α / 2 + 2 * β) / a ^ 2 +
            5 * γ / (3 * a ^ 3) -
          k * (Real.log b - c + 1) / b -
          α / (2 * b ^ 2) +
        γ / (3 * b ^ 3) := by
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hb0 : 0 < b := ha0.trans_le hab
  have hk : ContinuousOn (fun t : ℝ ↦ 2 * t⁻¹ ^ 3) (Set.Icc a b) := by
    intro t ht
    exact
      (continuousAt_const.mul
          ((continuousAt_id.inv₀ (ne_of_gt (ha0.trans_le ht.1))).pow 3)).continuousWithinAt
  have hm :
    IntervalIntegrable (fun t ↦ (k * t * (Real.log t - c - 1) + d) * (2 * t⁻¹ ^ 3))
      MeasureTheory.volume a b :=
    (hM.mul hk).intervalIntegrable_of_Icc hab
  have he :
    IntervalIntegrable (fun t ↦ (α * Real.log t + β + γ / t) * (2 * t⁻¹ ^ 3)) MeasureTheory.volume a
      b :=
    (hE.mul hk).intervalIntegrable_of_Icc hab
  have h := finite_tail_of_count_error ha hab hM hE hQ
  have heq :
    (fun t : ℝ ↦
        (k * t * (Real.log t - c - 1) + d + (α * Real.log t + β + γ / t)) * (2 * t⁻¹ ^ 3)) =
      (fun t ↦
        (k * t * (Real.log t - c - 1) + d) * (2 * t⁻¹ ^ 3) +
          (α * Real.log t + β + γ / t) * (2 * t⁻¹ ^ 3)) := by
    funext t
    ring
  rw [heq, intervalIntegral.integral_add hm he, Analysis.integral_log_main_inv_cube ha0 hab,
    Analysis.integral_log_budget_inv_cube ha0 hab] at h
  have hai := congrArg (fun z : ℝ ↦ k * (Real.log a - c - 1) * a⁻¹ * z) (mul_inv_cancel₀ ha0.ne')
  have hbi := congrArg (fun z : ℝ ↦ k * (Real.log b - c - 1) * b⁻¹ * z) (mul_inv_cancel₀ hb0.ne')
  simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow] at h ⊢
  nlinarith only [h, hai, hbi]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountTail
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountTailError
import PseudoPrime.Analysis.LogBudgetIntegral

/-! # Inverse-square tail with the entrance count retained -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- On `1 < a ≤ b`, a continuous approximation and error bound for the zero
count bound the finite inverse-square tail while retaining the exact count at
`a`. This permits cancellation with the reciprocal-sum Abel boundary term. -/
theorem finite_tail_le_retain_count {a b : ℝ} {M E : ℝ → ℝ} (ha : 1 < a) (hab : a ≤ b)
    (hM : ContinuousOn M (Set.Icc a b)) (hE : ContinuousOn E (Set.Icc a b))
    (hQ : ∀ t ∈ Set.Icc a b, |zeroCount t - M t| ≤ E t) :
    (∑ ρ ∈ (zerosUpTo b).filter (fun ρ ↦ a < |ρ.im|),
        (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) ≤
      (M b + E b) / b ^ 2 - zeroCount a / a ^ 2 + ∫ t in a..b, (M t + E t) * (2 * t⁻¹ ^ 3) := by
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hc : ContinuousOn (fun t : ℝ ↦ 2 * t⁻¹ ^ 3) (Set.Icc a b) := by
    intro t ht
    exact
      (continuousAt_const.mul
          ((continuousAt_id.inv₀ (ne_of_gt (lt_of_lt_of_le ha0 ht.1))).pow 3)).continuousWithinAt
  have hm : IntervalIntegrable (fun t ↦ (M t + E t) * (2 * t⁻¹ ^ 3)) MeasureTheory.volume a b :=
    ((hM.add hE).mul hc).intervalIntegrable_of_Icc hab
  have hint :=
    intervalIntegral.integral_mono_on hab (zeroCount_invCube_integrable ha0 hab) hm
      (fun t ht ↦ by
        have h := (abs_le.mp (hQ t ht)).2
        have hk : 0 ≤ 2 * t⁻¹ ^ 3 :=
          mul_nonneg (by norm_num only) (pow_nonneg (inv_nonneg.mpr (lt_of_lt_of_le ha0 ht.1).le) 3)
        exact mul_le_mul_of_nonneg_right (show zeroCount t ≤ M t + E t by linarith only [h]) hk)
  have hQb := abs_le.mp (hQ b ⟨hab, le_rfl⟩)
  have hdb :=
    div_le_div_of_nonneg_right (show zeroCount b ≤ M b + E b by linarith only [hQb.2]) (sq_nonneg b)
  rw [finite_tail_abel ha hab]
  linarith only [hint, hdb]

/-- A logarithmic zero-count budget gives an explicit finite-tail estimate
that keeps the exact entrance count. The two logarithmic integrals are
evaluated before the upper endpoint is sent to infinity. -/
theorem finite_tail_log_retain_count {a b k c d α β γ : ℝ} (ha : 1 < a) (hab : a ≤ b)
    (hM : ContinuousOn (fun t ↦ k * t * (Real.log t - c - 1) + d) (Set.Icc a b))
    (hE : ContinuousOn (fun t ↦ α * Real.log t + β + γ / t) (Set.Icc a b))
    (hQ :
      ∀ t ∈ Set.Icc a b,
        |zeroCount t - (k * t * (Real.log t - c - 1) + d)| ≤ α * Real.log t + β + γ / t) :
    (∑ ρ ∈ (zerosUpTo b).filter (fun ρ ↦ a < |ρ.im|),
        (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) ≤
      -zeroCount a / a ^ 2 + 2 * k * (Real.log a - c) / a +
            (d + α * (Real.log a + 1 / 2) + β) / a ^ 2 +
            2 * γ / (3 * a ^ 3) -
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
  have h := finite_tail_le_retain_count ha hab hM hE hQ
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
  have hbi := congrArg (fun z : ℝ ↦ k * (Real.log b - c - 1) * b⁻¹ * z) (mul_inv_cancel₀ hb0.ne')
  simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow] at h ⊢
  nlinarith only [h, hbi]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LaplacePointEvaluation
public import PseudoPrime.Analysis.WeightedMeanSquareCauchySchwarz

/-! # Point evaluation from weighted mean squares and their derivatives -/

@[expose] public section

namespace PseudoPrime.Analysis.ExponentialMeanSquare

/-- The real derivative of a complex function's squared norm when its derivative is f'.
This expression connects real weighted integration by parts to the complex energy. -/
noncomputable def normSqDerivative (f f' : ℝ → ℂ) (v : ℝ) : ℝ :=
  2 * inner ℝ (f v) (f' v)

/-- The absolute squared-norm derivative is bounded by twice the two complex norms.
Use real inner-product Cauchy--Schwarz to control the weighted derivative. -/
theorem abs_normSqDerivative_le (f f' : ℝ → ℂ) (v : ℝ) :
    |normSqDerivative f f' v| ≤ 2 * (‖f v‖ * ‖f' v‖) := by
  rw [normSqDerivative, abs_mul, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num only)

/-- For continuous functions with integrable energy densities, the formal squared-norm
derivative is weighted integrable. Dominate it by the actual Holder-integrable norm product. -/
theorem integrable_normSqDerivative {f f' : ℝ → ℂ} (hf : Continuous f) (hf' : Continuous f')
    (hi : MeasureTheory.Integrable (fun v ↦ ‖f v‖ ^ 2 * weight v))
    (hj : MeasureTheory.Integrable (fun v ↦ ‖f' v‖ ^ 2 * weight v)) :
    MeasureTheory.Integrable (fun v ↦ normSqDerivative f f' v * weight v) := by
  have hB := (integrable_weighted_norm_mul hf hf' hi hj).const_mul 2
  have hcont : Continuous (fun v ↦ normSqDerivative f f' v * weight v) := by
    simpa only [normSqDerivative, Pi.mul_def] using
      ((hf.inner hf').const_mul 2).mul continuous_weight
  apply hB.mono' hcont.aestronglyMeasurable
  exact
    Filter.Eventually.of_forall
      (fun v ↦ by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (weight_pos v).le]
        nlinarith only [abs_normSqDerivative_le f f' v, weight_pos v])

/-- For a bounded continuously differentiable complex function with integrable weighted
squares of itself and its derivative, evaluation at zero is bounded by E plus sqrt(E E').
Apply the two-sided real weighted FTC to its squared norm and then weighted Holder. -/
theorem norm_zero_sq_le_energy {f f' : ℝ → ℂ} (hf : Continuous f) (hf' : Continuous f')
    (hd : ∀ v, HasDerivAt f (f' v) v) (hi : MeasureTheory.Integrable (fun v ↦ ‖f v‖ ^ 2 * weight v))
    (hj : MeasureTheory.Integrable (fun v ↦ ‖f' v‖ ^ 2 * weight v)) {C : ℝ} (hb : ∀ v, ‖f v‖ ≤ C) :
    ‖f 0‖ ^ 2 ≤ energy f + Real.sqrt (energy f) * Real.sqrt (energy f') := by
  have hC : 0 ≤ C := le_trans (norm_nonneg (f 0)) (hb 0)
  have hbound : ∀ v, |‖f v‖ ^ 2| ≤ C ^ 2 := by
    intro v
    rw [abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (norm_nonneg _) hC).mpr (hb v)
  have hp :=
    point_le_integrals (fun v ↦ (hd v).norm_sq) hi (integrable_normSqDerivative hf hf' hi hj)
      (integrable_weighted_norm_mul hf hf' hi hj) hbound (abs_normSqDerivative_le f f')
  exact hp.trans (add_le_add le_rfl (weighted_norm_mul_le_sqrt hf hf' hi hj))

end PseudoPrime.Analysis.ExponentialMeanSquare

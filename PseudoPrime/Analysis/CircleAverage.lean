/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.CircleApproximation
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-!
# Uniform average of continuous circle functions

Pull back to the additive circle of period one and integrate against probability Haar measure.
The resulting continuous linear functional has norm at most one and extracts the constant moment.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- A continuous complex circle function, pulled back through the period-one additive
circle map, is integrable for probability Haar measure. Continuity on the compact additive
circle gives integrability. This justifies linearity of the circle average. -/
theorem integrable_circlePullback (f : C(Circle, ℂ)) :
    MeasureTheory.Integrable (fun t : AddCircle (1 : ℝ) => f (AddCircle.toCircle t))
      AddCircle.haarAddCircle := by
  apply MeasureTheory.integrableOn_univ.mp
  exact
    ContinuousOn.integrableOn_compact isCompact_univ
      (f.continuous.comp AddCircle.continuous_toCircle).continuousOn

/-- The complex linear map averaging a continuous circle function over probability
Haar measure on the period-one additive circle. Its value is the integral of the pullback
through toCircle. Integrability gives additivity and the scalar integral rule gives linearity.
This is promoted to a continuous functional by the supremum-norm bound. -/
noncomputable def circleAverageLinearMap : C(Circle, ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∫ t : AddCircle (1 : ℝ), f (AddCircle.toCircle t) ∂AddCircle.haarAddCircle
  map_add' f g := by
    simp only [ContinuousMap.add_apply]
    exact MeasureTheory.integral_add (integrable_circlePullback f) (integrable_circlePullback g)
  map_smul' c f := by
    simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    exact MeasureTheory.integral_smul c _

/-- The probability circle average of a continuous function has norm at most its
supremum norm. Bound each value by that norm and use total probability mass one.
This supplies the norm estimate for continuous extension. -/
theorem norm_circleAverageLinearMap_le (f : C(Circle, ℂ)) : ‖circleAverageLinearMap f‖ ≤ ‖f‖ := by
  change ‖∫ t : AddCircle (1 : ℝ), f (AddCircle.toCircle t) ∂AddCircle.haarAddCircle‖ ≤ ‖f‖
  have h :=
    MeasureTheory.norm_integral_le_of_norm_le_const (μ := AddCircle.haarAddCircle (T := (1 : ℝ)))
      (MeasureTheory.ae_of_all _ (fun t => f.norm_coe_le_norm (AddCircle.toCircle t)))
  simpa only [MeasureTheory.probReal_univ, mul_one] using h

/-- The continuous complex linear functional giving the uniform probability average
of a continuous circle function. Pull back through the period-one additive circle and
integrate against Haar measure; the supremum norm bounds its value.
Half this functional is the limiting normalized completed-zero distribution. -/
noncomputable def circleAverage : C(Circle, ℂ) →L[ℂ] ℂ :=
  circleAverageLinearMap.mkContinuous 1
    (fun f => by simpa only [one_mul] using norm_circleAverageLinearMap_le f)

/-- The circle average is the probability Haar integral of the function pulled back
to the period-one additive circle. This is the defining formula after promotion to a
continuous linear map and connects monomial and integral calculations. -/
theorem circleAverage_apply (f : C(Circle, ℂ)) :
    circleAverage f = ∫ t : AddCircle (1 : ℝ), f (AddCircle.toCircle t) ∂AddCircle.haarAddCircle :=
  rfl

/-- The uniform circle average has operator norm at most one.
Apply the pointwise supremum-norm bound to the continuous linear map.
This controls the limit functional's uniform approximation error. -/
theorem norm_circleAverage_le_one : ‖circleAverage‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖circleAverageLinearMap f‖ ≤ 1 * ‖f‖
  simpa only [one_mul] using norm_circleAverageLinearMap_le f

/-- The uniform circle average sends the constant one function to one.
Use the probability mass of the additive circle. This is the constant Fourier moment. -/
theorem circleAverage_const_one : circleAverage (ContinuousMap.const Circle (1 : ℂ)) = 1 := by
  rw [circleAverage_apply]
  simp only [ContinuousMap.const_apply, MeasureTheory.integral_const, MeasureTheory.probReal_univ,
    one_smul]

/-- The uniform circle average of an integer monomial is one in degree zero and zero
in every other degree. The pullback is the additive-circle Fourier monomial.
For nonzero degree, translation by half its period negates it, so Haar invariance
forces its integral to vanish. This identifies the limiting zero-distribution moments. -/
theorem circleAverage_circleMonomial (k : ℤ) :
    circleAverage (circleMonomial k) = if k = 0 then 1 else 0 := by
  rw [circleAverage_apply]
  have he : (fun t : AddCircle (1 : ℝ) => circleMonomial k (AddCircle.toCircle t)) = fourier k := by
    funext t
    change (AddCircle.toCircle t : ℂ) ^ k = fourier k t
    rw [fourier_apply, AddCircle.toCircle_zsmul, Circle.coe_zpow]
  rw [he]
  by_cases hk : k = 0
  · rw [hk, ite_eq_left (show (0 : ℤ) = 0 from rfl)]
    rw [show (fourier (T := (1 : ℝ)) 0 : AddCircle (1 : ℝ) → ℂ) = (fun _ => 1) by
        funext t; exact fourier_zero]
    rw [MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul]
  · rw [ite_eq_right hk]
    exact
      MeasureTheory.integral_eq_zero_of_add_right_eq_neg
        (fourier_add_half_inv_index hk (show (0 : ℝ) < 1 from zero_lt_one))

end PseudoPrime.Analysis

/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialMeanSquareIntervals
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Point evaluation by real-line Laplace weighted integration -/

@[expose] public section

namespace PseudoPrime.Analysis.ExponentialMeanSquare

/-- For nonnegative displacement, the weight is the positive-half-line exponential.
Use the absolute-value branch to evaluate improper integrals. -/
theorem weight_of_nonneg {v : ℝ} (hv : 0 ≤ v) : weight v = Real.exp (-2 * v) := by
  rw [weight, abs_of_nonneg hv]

/-- For nonpositive displacement, the weight is the negative-half-line exponential.
Use the absolute-value branch to evaluate improper integrals. -/
theorem weight_of_nonpos {v : ℝ} (hv : v ≤ 0) : weight v = Real.exp (2 * v) := by
  rw [weight, abs_of_nonpos hv]
  congr 1
  ring

/-- A bounded real function times exp(-2v) tends to zero at positive infinity.
Use exponential decay and the bounded-product limit to remove the boundary term. -/
theorem tendsto_bounded_exp_neg {H : ℝ → ℝ} {C : ℝ} (hH : ∀ v, |H v| ≤ C) :
    Filter.Tendsto (fun v ↦ H v * Real.exp (-2 * v)) Filter.atTop (nhds 0) := by
  exact
    bdd_le_mul_tendsto_zero' C (Filter.Eventually.of_forall hH)
      (Real.tendsto_exp_atBot.comp
        (Filter.Tendsto.neg_mul_atTop (by norm_num only : (-2 : ℝ) < 0) tendsto_const_nhds
          Filter.tendsto_id))

/-- A bounded real function times exp(2v) tends to zero at negative infinity.
Use exponential decay and the bounded-product limit to remove the boundary term. -/
theorem tendsto_bounded_exp_pos {H : ℝ → ℝ} {C : ℝ} (hH : ∀ v, |H v| ≤ C) :
    Filter.Tendsto (fun v ↦ H v * Real.exp (2 * v)) Filter.atBot (nhds 0) := by
  exact
    bdd_le_mul_tendsto_zero' C (Filter.Eventually.of_forall hH)
      (Real.tendsto_exp_atBot.comp
        (Filter.Tendsto.const_mul_atBot (by norm_num only : (0 : ℝ) < 2) Filter.tendsto_id))

/-- For bounded differentiable H with integrable weighted H and derivative, the positive
half-line derivative integral equals the boundary value. Apply the improper FTC to H exp(-2v). -/
theorem integral_weighted_derivative_Ioi {H D : ℝ → ℝ} (hd : ∀ v, HasDerivAt H (D v) v)
    (hH : MeasureTheory.Integrable (fun v ↦ H v * weight v))
    (hD : MeasureTheory.Integrable (fun v ↦ D v * weight v)) {C : ℝ} (hb : ∀ v, |H v| ≤ C) :
    (∫ v : ℝ in Set.Ioi 0, D v * weight v) - 2 * (∫ v : ℝ in Set.Ioi 0, H v * weight v) = -H 0 := by
  have hi :
    MeasureTheory.IntegrableOn (fun v ↦ (D v - 2 * H v) * Real.exp (-2 * v)) (Set.Ioi 0) := by
    have h := (hD.sub' (hH.const_mul 2)).integrableOn (s := Set.Ioi 0)
    exact
      h.congr_fun
        (fun v hv ↦ by
          simp only [weight_of_nonneg hv.le]
          ring)
        measurableSet_Ioi
  have hd' :
    ∀ v, HasDerivAt (fun w ↦ H w * Real.exp (-2 * w)) ((D v - 2 * H v) * Real.exp (-2 * v)) v := by
    intro v
    convert (hd v).mul (((hasDerivAt_id v).const_mul (-2)).exp) using 1
    · simp only [Pi.mul_def, id_eq]
    · simp only [id_eq]
      ring
  have he :=
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (fun v hv ↦ hd' v) hi
      (tendsto_bounded_exp_neg hb)
  have heq :
    (∫ v : ℝ in Set.Ioi 0, (D v - 2 * H v) * Real.exp (-2 * v)) =
      ∫ v : ℝ in Set.Ioi 0, D v * weight v - 2 * (H v * weight v) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    simp only [weight_of_nonneg hv.le]
    ring
  rw [heq, MeasureTheory.integral_sub hD.integrableOn (hH.integrableOn.const_mul 2),
    MeasureTheory.integral_const_mul] at he
  simpa only [mul_zero, Real.exp_zero, mul_one, zero_sub] using he

/-- For bounded differentiable H with integrable weighted H and derivative, the negative
half-line derivative integral equals the boundary value. Apply the improper FTC to H exp(2v). -/
theorem integral_weighted_derivative_Iic {H D : ℝ → ℝ} (hd : ∀ v, HasDerivAt H (D v) v)
    (hH : MeasureTheory.Integrable (fun v ↦ H v * weight v))
    (hD : MeasureTheory.Integrable (fun v ↦ D v * weight v)) {C : ℝ} (hb : ∀ v, |H v| ≤ C) :
    (∫ v : ℝ in Set.Iic 0, D v * weight v) + 2 * (∫ v : ℝ in Set.Iic 0, H v * weight v) = H 0 := by
  have hi :
    MeasureTheory.IntegrableOn (fun v ↦ (D v + 2 * H v) * Real.exp (2 * v)) (Set.Iic 0) := by
    have h := (hD.add (hH.const_mul 2)).integrableOn (s := Set.Iic 0)
    exact
      h.congr_fun
        (fun v hv ↦ by
          simp only [Pi.add_apply, weight_of_nonpos hv]
          ring)
        measurableSet_Iic
  have hd' :
    ∀ v, HasDerivAt (fun w ↦ H w * Real.exp (2 * w)) ((D v + 2 * H v) * Real.exp (2 * v)) v := by
    intro v
    convert (hd v).mul (((hasDerivAt_id v).const_mul 2).exp) using 1
    · simp only [Pi.mul_def, id_eq]
    · simp only [id_eq]
      ring
  have he :=
    MeasureTheory.integral_Iic_of_hasDerivAt_of_tendsto' (fun v hv ↦ hd' v) hi
      (tendsto_bounded_exp_pos hb)
  have heq :
    (∫ v : ℝ in Set.Iic 0, (D v + 2 * H v) * Real.exp (2 * v)) =
      ∫ v : ℝ in Set.Iic 0, D v * weight v + 2 * (H v * weight v) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Iic
    intro v hv
    simp only [weight_of_nonpos hv]
    ring
  rw [heq, MeasureTheory.integral_add hD.integrableOn (hH.integrableOn.const_mul 2),
    MeasureTheory.integral_const_mul] at he
  simpa only [mul_zero, Real.exp_zero, mul_one, sub_zero] using he

/-- For bounded differentiable H with integrable weighted derivative and a nonnegative
absolute derivative bound 2B, evaluation at zero is controlled by the integrals of H and B.
Combine the two half-line FTC identities, retaining the derivative signs. -/
theorem point_le_integrals {H D B : ℝ → ℝ} (hd : ∀ v, HasDerivAt H (D v) v)
    (hH : MeasureTheory.Integrable (fun v ↦ H v * weight v))
    (hD : MeasureTheory.Integrable (fun v ↦ D v * weight v))
    (hB : MeasureTheory.Integrable (fun v ↦ B v * weight v)) {C : ℝ} (hb : ∀ v, |H v| ≤ C)
    (hDB : ∀ v, |D v| ≤ 2 * B v) : H 0 ≤ (∫ v : ℝ, H v * weight v) + ∫ v : ℝ, B v * weight v := by
  have hp := integral_weighted_derivative_Ioi hd hH hD hb
  have hn := integral_weighted_derivative_Iic hd hH hD hb
  have hmP :=
    MeasureTheory.integral_mono (μ := MeasureTheory.volume.restrict (Set.Ioi 0)) hD.integrableOn.neg
      (hB.integrableOn.const_mul 2)
      (fun v ↦ by
        dsimp only [Pi.neg_apply]
        nlinarith only [neg_le_abs (D v), hDB v, weight_pos v])
  have hmN :=
    MeasureTheory.integral_mono (μ := MeasureTheory.volume.restrict (Set.Iic 0)) hD.integrableOn
      (hB.integrableOn.const_mul 2)
      (fun v ↦ by nlinarith only [le_abs_self (D v), hDB v, weight_pos v])
  have hsumH := intervalIntegral.integral_Iic_add_Ioi hH.integrableOn hH.integrableOn (b := 0)
  have hsumB := intervalIntegral.integral_Iic_add_Ioi hB.integrableOn hB.integrableOn (b := 0)
  simp only [Pi.neg_def, MeasureTheory.integral_neg, MeasureTheory.integral_const_mul] at hmP hmN
  linarith only [hp, hn, hmP, hmN, hsumH, hsumB]

end PseudoPrime.Analysis.ExponentialMeanSquare

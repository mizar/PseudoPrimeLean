/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.MellinResolvent

/-! # Resolvent inversion at every positive argument -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- For an argument greater than one, the regularized resolvent weight vanishes.
All three defining indicators vanish outside their support.
This handles inverse scales below one. -/
theorem mellinResolventWeight_eq_zero_of_one_lt (α : ℂ) {t : ℝ} (ht : 1 < t) :
    mellinResolventWeight α t = 0 := by
  have hn : t ∉ Set.Ioc (0 : ℝ) 1 := fun h ↦ (not_le_of_gt ht) h.2
  simp only [mellinResolventWeight, mellinWeightZero, mellinWeightTwo, Set.indicator_of_notMem hn,
    mul_zero, sub_zero]

/-- For an argument greater than one, the resolvent weight is continuous.
It is locally zero. This supplies inversion outside the support. -/
theorem continuousAt_mellinResolventWeight_of_one_lt (α : ℂ) {t : ℝ} (ht : 1 < t) :
    ContinuousAt (mellinResolventWeight α) t := by
  apply (continuousAt_const : ContinuousAt (fun _ : ℝ ↦ (0 : ℂ)) t).congr_of_eventuallyEq
  exact (eventually_gt_nhds ht).mono (fun u hu ↦ mellinResolventWeight_eq_zero_of_one_lt α hu)

/-- The resolvent weight is continuous at one for every complex pole parameter.
The interior expression vanishes at one, so its piecewise extension by zero is continuous.
This removes the boundary exclusion from pointwise inversion. -/
theorem continuousAt_mellinResolventWeight_one (α : ℂ) :
    ContinuousAt (mellinResolventWeight α) (1 : ℝ) := by
  classical
  let f := fun u : ℝ ↦ (α ^ 2)⁻¹ * ((u : ℂ) ^ (-α) - 1 - α * (-(Real.log u : ℂ)))
  have hf : ContinuousAt f (1 : ℝ) :=
    continuousAt_const.mul
      (((Complex.continuous_ofReal.continuousAt.cpow continuousAt_const
                (Complex.ofReal_mem_slitPlane.mpr zero_lt_one)).sub
            continuousAt_const).sub
        (continuousAt_const.mul ((Real.continuousAt_log one_ne_zero).ofReal.neg)))
  have hf1 : f 1 = 0 := by
    simp only [f, Complex.ofReal_one, Complex.one_cpow, Real.log_one, Complex.ofReal_zero, neg_zero,
      mul_zero, sub_self]
  have ht : Filter.Tendsto f (nhds (1 : ℝ)) (nhds (0 : ℂ)) := by
    rw [← hf1]
    exact hf
  have hpiece : ContinuousAt ((Set.Iic (1 : ℝ)).piecewise f (fun _ ↦ (0 : ℂ))) 1 := by
    have h :=
      Filter.Tendsto.piecewise (s := Set.Iic (1 : ℝ)) (ht.mono_left inf_le_left)
        ((tendsto_const_nhds :
              Filter.Tendsto (fun _ : ℝ ↦ (0 : ℂ)) (nhds (1 : ℝ)) (nhds (0 : ℂ))).mono_left
          inf_le_left)
    change Filter.Tendsto _ (nhds (1 : ℝ)) (nhds _)
    have hmem : (1 : ℝ) ∈ Set.Iic 1 := Set.mem_Iic.mpr (le_refl (1 : ℝ))
    rw [Set.piecewise_eq_of_mem (Set.Iic (1 : ℝ)) f (fun _ ↦ (0 : ℂ)) hmem, hf1]
    exact h
  apply hpiece.congr_of_eventuallyEq
  apply (eventually_gt_nhds (zero_lt_one : (0 : ℝ) < 1)).mono
  intro u hu
  by_cases hu1 : u ≤ 1
  · have hi : u ∈ Set.Ioc (0 : ℝ) 1 := ⟨hu, hu1⟩
    rw [Set.piecewise_eq_of_mem (Set.Iic (1 : ℝ)) f (fun _ ↦ (0 : ℂ)) hu1]
    simp only [mellinResolventWeight, mellinWeightZero, mellinWeightTwo, Set.indicator_of_mem hi, f]
  · rw [Set.piecewise_eq_of_notMem (Set.Iic (1 : ℝ)) f (fun _ ↦ (0 : ℂ)) hu1]
    exact mellinResolventWeight_eq_zero_of_one_lt α (lt_of_not_ge hu1)

/-- For every positive argument, the resolvent weight is continuous.
Combine the interior, boundary and exterior continuity statements.
This permits inversion at every positive argument. -/
theorem continuousAt_mellinResolventWeight_of_pos (α : ℂ) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (mellinResolventWeight α) t := by
  rcases lt_trichotomy t 1 with h | h | h
  · exact continuousAt_mellinResolventWeight ht h
  · subst t
    exact continuousAt_mellinResolventWeight_one α
  · exact continuousAt_mellinResolventWeight_of_one_lt α h

/-- For a pole with negative real part, positive line and positive argument,
inverse Mellin transformation recovers the regularized resolvent weight.
Use global positive continuity with the existing Mellin transform and vertical integrability.
This extends the interior-only scalar inversion interface. -/
theorem mellinInv_resolventKernel_eq_of_pos {α : ℂ} (hα : α.re < 0) {τ t : ℝ} (hτ : 0 < τ)
    (ht : 0 < t) :
    mellinInv τ (fun s : ℂ ↦ 1 / (s ^ 2 * (s - α))) t = mellinResolventWeight α t := by
  have hp : ∀ y : ℝ, 0 < ((τ : ℂ) + y * Complex.I).re := by
    intro y
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_self, add_zero] using hτ
  have he :
    ∀ y : ℝ,
      mellin (mellinResolventWeight α) ((τ : ℂ) + y * Complex.I) =
        1 / (((τ : ℂ) + y * Complex.I) ^ 2 * ((τ : ℂ) + y * Complex.I - α)) :=
    fun y ↦ (hasMellin_resolventWeight hα (hp y)).2
  have hi : Complex.VerticalIntegrable (mellin (mellinResolventWeight α)) τ := by
    unfold Complex.VerticalIntegrable
    simp only [he]
    exact verticalIntegrable_resolventKernel hα hτ
  have hm :=
    mellinInv_mellin_eq τ (mellinResolventWeight α) ht
      (hasMellin_resolventWeight hα (by simpa only [Complex.ofReal_re] using hτ)).1 hi
      (continuousAt_mellinResolventWeight_of_pos α ht)
  rw [← hm]
  unfold mellinInv
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  rw [he]

/-- For a pole with negative real part and positive line and scale,
the normalized vertical resolvent integral equals its weight at inverse scale.
Apply positive-argument inversion and invert the real-base complex power.
This supports all three translated terms of a triangular kernel. -/
theorem integral_resolventKernel_eq_weight_of_pos {α : ℂ} (hα : α.re < 0) {τ x : ℝ} (hτ : 0 < τ)
    (hx : 0 < x) :
    (2 * Real.pi)⁻¹ •
        (∫ y : ℝ,
          (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
            (((τ : ℂ) + y * Complex.I) ^ 2 * ((τ : ℂ) + y * Complex.I - α))) =
      mellinResolventWeight α x⁻¹ := by
  have hm := mellinInv_resolventKernel_eq_of_pos hα hτ (inv_pos.mpr hx)
  rw [← hm]
  unfold mellinInv
  rw [one_div]
  congr 1
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  dsimp only
  rw [Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg hx.le, Complex.cpow_neg, inv_inv,
    smul_eq_mul, div_eq_mul_inv, one_div]

/-- For a pole with negative real part, positive line, and scale strictly between zero and one,
the normalized resolvent integral vanishes. Its inverse argument lies outside the support.
This identifies the zero terms among translated triangular resolvents. -/
theorem integral_resolventKernel_eq_zero_of_lt_one {α : ℂ} (hα : α.re < 0) {τ x : ℝ} (hτ : 0 < τ)
    (hx : 0 < x) (hx1 : x < 1) :
    (2 * Real.pi)⁻¹ •
        (∫ y : ℝ,
          (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
            (((τ : ℂ) + y * Complex.I) ^ 2 * ((τ : ℂ) + y * Complex.I - α))) =
      0 := by
  rw [integral_resolventKernel_eq_weight_of_pos hα hτ hx]
  exact mellinResolventWeight_eq_zero_of_one_lt α ((one_lt_inv₀ hx).mpr hx1)

end PseudoPrime.AnalyticNumberTheory.General

/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.MellinWeights

/-!
# Mellin inversion for regularized complex resolvents

The scalar kernel evaluation applies uniformly to left-half-plane zero and gamma poles.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- The function of real t obtained by subtracting the constant and logarithmic Mellin
weights from the power weight `t^(-α)` on (0,1], then multiplying by 1/α².
It is defined for every complex α, including α = 0 by totalized division, and vanishes
outside (0,1]. For Re α < 0 its Mellin transform is `1/(s²(s-α))` on Re s > 0.
This isolates the regularized scalar residue used before summing zero and gamma poles. -/
noncomputable def mellinResolventWeight (α : ℂ) (t : ℝ) : ℂ :=
  (α ^ 2)⁻¹ *
    ((Set.Ioc (0 : ℝ) 1).indicator (fun u ↦ (u : ℂ) ^ (-α)) t - mellinWeightZero t -
      α * mellinWeightTwo t)

/-- For Re α < 0 and Re s > 0, the resolvent weight has transform 1/(s²(s-α)).
Combine the power, constant and logarithmic transforms; all three converge absolutely.
This supplies the transform used to evaluate individual zero and gamma-pole terms. -/
theorem hasMellin_resolventWeight {α s : ℂ} (hα : α.re < 0) (hs : 0 < s.re) :
    HasMellin (mellinResolventWeight α) s (1 / (s ^ 2 * (s - α))) := by
  have hp :=
    hasMellin_cpow_Ioc (-α) (s := s)
      (by
        rw [Complex.neg_re]; linarith only [hα, hs])
  have hz := hasMellin_one_Ioc hs
  have ht := hasMellin_mellinWeightTwo hs
  have hfirst := hasMellin_sub hp.1 hz.1
  rw [hp.2, hz.2] at hfirst
  have hscaled := hasMellin_const_smul ht.1 α
  rw [ht.2] at hscaled
  have hsub := hasMellin_sub hfirst.1 hscaled.1
  rw [hfirst.2, hscaled.2] at hsub
  have hout := hasMellin_const_smul hsub.1 ((α ^ 2)⁻¹)
  rw [hsub.2] at hout
  have ha0 : α ≠ 0 := fun h ↦ by
    rw [h, Complex.zero_re] at hα; exact lt_irrefl _ hα
  have hs0 : s ≠ 0 := fun h ↦ by
    rw [h, Complex.zero_re] at hs; exact lt_irrefl _ hs
  have hd0 : s - α ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    rw [Complex.sub_re, Complex.zero_re] at hh
    linarith only [hh, hα, hs]
  convert hout using 1
  · rfl
  · simp only [smul_eq_mul, ← sub_eq_add_neg]
    field_simp [ha0, hs0, hd0]
    ring

/-- For a pole strictly left of zero and a positive vertical line, the resolvent kernel
is integrable. The pole distance is bounded below and the remaining inverse-square kernel
is integrable. This verifies the vertical-integrability hypothesis of Mellin inversion. -/
theorem verticalIntegrable_resolventKernel {α : ℂ} (hα : α.re < 0) {τ : ℝ} (hτ : 0 < τ) :
    Complex.VerticalIntegrable (fun z : ℂ ↦ 1 / (z ^ 2 * (z - α))) τ := by
  have hδ : 0 < τ - α.re := sub_pos.mpr (hα.trans hτ)
  have hz : ∀ y : ℝ, (τ : ℂ) + y * Complex.I ≠ 0 := fun y ↦ ne_zero_add_mul_I_of_re_ne_zero hτ.ne' y
  have hd : ∀ y : ℝ, τ - α.re ≤ ‖(τ : ℂ) + y * Complex.I - α‖ := by
    intro y
    have h := Complex.re_le_norm ((τ : ℂ) + y * Complex.I - α)
    simpa only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_self, add_zero] using h
  have hdne : ∀ y : ℝ, (τ : ℂ) + y * Complex.I - α ≠ 0 := fun y ↦
    norm_pos_iff.mp (hδ.trans_le (hd y))
  have hc :
    Continuous (fun y : ℝ ↦ 1 / (((τ : ℂ) + y * Complex.I) ^ 2 * ((τ : ℂ) + y * Complex.I - α))) :=
    continuous_const.div
      (((continuous_const.add (Complex.continuous_ofReal.mul_const Complex.I)).pow 2).mul
        ((continuous_const.add (Complex.continuous_ofReal.mul_const Complex.I)).sub
          continuous_const))
      (fun y ↦ mul_ne_zero (pow_ne_zero _ (hz y)) (hdne y))
  have hb := (verticalIntegrable_mellinLogKernel hτ.ne').norm.div_const (τ - α.re)
  apply hb.mono' hc.aestronglyMeasurable
  filter_upwards with y
  rw [norm_div, norm_one, norm_mul, norm_pow, norm_pow, norm_inv]
  have he :
    1 / (‖(τ : ℂ) + y * Complex.I‖ ^ 2 * ‖(τ : ℂ) + y * Complex.I - α‖) =
      (‖(τ : ℂ) + y * Complex.I‖⁻¹ ^ 2) / ‖(τ : ℂ) + y * Complex.I - α‖ := by
    rw [one_div, mul_inv, inv_pow, div_eq_mul_inv]
  rw [he]
  exact div_le_div_of_nonneg_left (sq_nonneg _) hδ (hd y)

/-- At 0 < t < 1 the resolvent weight is continuous.
The indicators are locally constant and the positive real power base lies in the slit plane.
This permits pointwise inversion at t = 1/x for x > 1. -/
theorem continuousAt_mellinResolventWeight {α : ℂ} {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ContinuousAt (mellinResolventWeight α) t := by
  have he : ∀ᶠ u in nhds t, u ∈ Set.Ioc (0 : ℝ) 1 :=
    Filter.Eventually.mono (isOpen_Ioo.mem_nhds ⟨ht, ht1⟩) (fun u hu ↦ ⟨hu.1, hu.2.le⟩)
  have hc : ContinuousAt (fun u : ℝ ↦ (α ^ 2)⁻¹ * ((u : ℂ) ^ (-α) - 1 - α * mellinWeightTwo u)) t :=
    continuousAt_const.mul
      (((Complex.continuous_ofReal.continuousAt.cpow continuousAt_const
                (Complex.ofReal_mem_slitPlane.mpr ht)).sub
            continuousAt_const).sub
        (continuousAt_const.mul (continuousAt_mellinWeightTwo ht)))
  apply hc.congr_of_eventuallyEq
  filter_upwards [he] with u hu
  rw [mellinResolventWeight, mellinWeightZero, Set.indicator_of_mem hu, Set.indicator_of_mem hu]

/-- For Re α < 0, τ > 0 and 0 < t < 1, inverse Mellin transformation recovers the
resolvent weight. Apply Mellin inversion using the computed transform, convergence,
vertical integrability and continuity. This is the scalar residue evaluation. -/
theorem mellinInv_resolventKernel_eq {α : ℂ} (hα : α.re < 0) {τ t : ℝ} (hτ : 0 < τ) (ht : 0 < t)
    (ht1 : t < 1) :
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
      (continuousAt_mellinResolventWeight ht ht1)
  rw [← hm]
  unfold mellinInv
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  rw [he]

/-- For x > 1, the resolvent weight at 1/x equals (x^α-1-α log x)/α².
Both indicators are active; the inverse-base complex power and real logarithm identities
identify the regularized residue expression used by the shifted formula. -/
theorem mellinResolventWeight_inv {α : ℂ} {x : ℝ} (hx : 1 < x) :
    mellinResolventWeight α x⁻¹ = ((x : ℂ) ^ α - 1 - α * (Real.log x : ℂ)) / α ^ 2 := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hi : x⁻¹ ∈ Set.Ioc (0 : ℝ) 1 := ⟨inv_pos.mpr hx0, (inv_lt_one₀ hx0).mpr hx |>.le⟩
  rw [mellinResolventWeight, mellinWeightZero, mellinWeightTwo, Set.indicator_of_mem hi,
    Set.indicator_of_mem hi, Set.indicator_of_mem hi, Complex.ofReal_inv,
    Complex.inv_cpow_ofReal_nonneg hx0.le, Complex.cpow_neg, inv_inv, Real.log_inv,
    Complex.ofReal_neg, neg_neg, div_eq_mul_inv]
  exact mul_comm _ _

/-- For Re α < 0, τ > 0 and x > 1, the normalized vertical resolvent integral equals
(x^α-1-α log x)/α². Invert the Mellin transform at 1/x and rewrite its power weight.
This evaluates each zero or gamma-pole contribution before exchanging sums and integrals. -/
theorem integral_resolventKernel_eq {α : ℂ} (hα : α.re < 0) {τ x : ℝ} (hτ : 0 < τ) (hx : 1 < x) :
    (2 * Real.pi)⁻¹ •
        (∫ y : ℝ,
          (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
            (((τ : ℂ) + y * Complex.I) ^ 2 * ((τ : ℂ) + y * Complex.I - α))) =
      ((x : ℂ) ^ α - 1 - α * (Real.log x : ℂ)) / α ^ 2 := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hm := mellinInv_resolventKernel_eq hα hτ (inv_pos.mpr hx0) ((inv_lt_one₀ hx0).mpr hx)
  rw [mellinResolventWeight_inv hx] at hm
  rw [← hm]
  unfold mellinInv
  rw [one_div]
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  rw [Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg hx0.le, Complex.cpow_neg, inv_inv,
    smul_eq_mul, div_eq_mul_inv, one_div]

end PseudoPrime.AnalyticNumberTheory.General

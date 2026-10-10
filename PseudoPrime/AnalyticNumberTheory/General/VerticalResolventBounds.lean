/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.MellinResolvent
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Integrable bounds for centered vertical resolvents

Inverse three-halves profiles control poles at arbitrary imaginary heights.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- For positive a,u,v with a ≤ u+v, the reciprocal product is bounded by two
integrable three-halves profiles times 2/(a sqrt a). Compare the smaller of u,v
with the larger and use the square-root bound. This controls centered resolvents. -/
theorem resolvent_norm_product_bound {a u v : ℝ} (ha : 0 < a) (hu : 0 < u) (hv : 0 < v)
    (ht : a ≤ u + v) :
    1 / (a * u * v) ≤ 2 / (a * Real.sqrt a) * (1 / (u * Real.sqrt u) + 1 / (v * Real.sqrt v)) := by
  have hsa := Real.sqrt_pos.mpr ha
  have hsu := Real.sqrt_pos.mpr hu
  have hsv := Real.sqrt_pos.mpr hv
  wlog huv : u ≤ v generalizing u v
  · have h := this hv hu (by linarith only [ht]) hsv hsu (le_of_not_ge huv)
    convert h using 1 <;> ring
  have hprod : Real.sqrt a * Real.sqrt u ≤ 2 * v := by
    rw [← Real.sqrt_mul ha.le, Real.sqrt_le_iff]
    constructor
    · exact mul_nonneg zero_le_two hv.le
    · have hav : a ≤ 2 * v := by linarith only [ht, huv]
      have hm := mul_le_mul hav huv hu.le (mul_nonneg zero_le_two hv.le)
      nlinarith only [hm, sq_nonneg v]
  have hfirst : 1 / (a * u * v) ≤ 2 / (a * Real.sqrt a) * (1 / (u * Real.sqrt u)) := by
    rw [div_mul_div_comm, mul_one,
      div_le_div_iff₀ (mul_pos (mul_pos ha hu) hv) (mul_pos (mul_pos ha hsa) (mul_pos hu hsu))]
    nlinarith only [mul_le_mul_of_nonneg_left hprod (mul_pos ha hu).le]
  exact
    hfirst.trans
      (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (div_nonneg zero_le_one (mul_pos hv hsv).le))
        (div_nonneg zero_le_two (mul_pos ha hsa).le))

/-- For a > 0, a^(3/2) equals a sqrt a.
Split the real exponent into one and one half. This relates the integral majorant
to the power-weighted zero mass. -/
theorem rpow_three_halves_eq {a : ℝ} (ha : 0 < a) : a ^ (3 / 2 : ℝ) = a * Real.sqrt a := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num only, Real.rpow_add ha, Real.rpow_one, ←
    Real.sqrt_eq_rpow]

/-- The inverse three-halves power of the norm on a vertical line.
For τ > 0 it is finite everywhere and integrable in y. Translations of this profile
bound poles at arbitrary imaginary heights in the explicit formula. -/
noncomputable def verticalResolventMajorant (τ y : ℝ) : ℝ :=
  1 / (‖(τ : ℂ) + y * Complex.I‖ * Real.sqrt ‖(τ : ℂ) + y * Complex.I‖)

/-- For τ > 0 the inverse three-halves vertical norm profile is integrable.
Compare 1+abs y with (1+1/τ) times the vertical norm and apply the integrable
one-plus-norm power bound. This permits integration of the resolvent majorant. -/
theorem integrable_verticalResolventMajorant {τ : ℝ} (hτ : 0 < τ) :
    MeasureTheory.Integrable (verticalResolventMajorant τ) := by
  have hn : ∀ y : ℝ, 0 < ‖(τ : ℂ) + y * Complex.I‖ := fun y ↦
    norm_pos_iff.mpr (ne_zero_add_mul_I_of_re_ne_zero hτ.ne' y)
  have hc : Continuous (verticalResolventMajorant τ) :=
    continuous_const.div
      ((continuous_const.add (Complex.continuous_ofReal.mul_const Complex.I)).norm.mul
        (Real.continuous_sqrt.comp
          (continuous_const.add (Complex.continuous_ofReal.mul_const Complex.I)).norm))
      (fun y ↦ mul_ne_zero (hn y).ne' (Real.sqrt_pos.mpr (hn y)).ne')
  have hg :
    MeasureTheory.Integrable (fun y : ℝ ↦ (1 + τ⁻¹) ^ (3 / 2 : ℝ) * (1 + ‖y‖) ^ (-(3 / 2 : ℝ))) :=
    (integrable_one_add_norm
          (show (Module.finrank ℝ ℝ : ℝ) < 3 / 2 by norm_num only [Module.finrank_self])).const_mul
      _
  apply hg.mono' hc.aestronglyMeasurable
  filter_upwards with y
  have hr : τ ≤ ‖(τ : ℂ) + y * Complex.I‖ := by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_self, add_zero] using
      Complex.re_le_norm ((τ : ℂ) + y * Complex.I)
  have him : ‖y‖ ≤ ‖(τ : ℂ) + y * Complex.I‖ := by
    simpa only [Real.norm_eq_abs, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, mul_one, mul_zero, add_zero, zero_add] using
      Complex.abs_im_le_norm ((τ : ℂ) + y * Complex.I)
  have hb : 1 + ‖y‖ ≤ (1 + τ⁻¹) * ‖(τ : ℂ) + y * Complex.I‖ := by
    have h := mul_le_mul_of_nonneg_left hr (inv_pos.mpr hτ).le
    rw [inv_mul_cancel₀ hτ.ne'] at h
    nlinarith only [h, him]
  have hp :=
    Real.rpow_le_rpow (by linarith only [norm_nonneg y]) hb (show (0 : ℝ) ≤ 3 / 2 by norm_num only)
  rw [Real.mul_rpow (by linarith only [inv_pos.mpr hτ]) (norm_nonneg _)] at hp
  rw [verticalResolventMajorant, Real.norm_eq_abs,
    abs_of_pos (div_pos zero_lt_one (mul_pos (hn y) (Real.sqrt_pos.mpr (hn y)))), ←
    rpow_three_halves_eq (hn y), Real.rpow_neg (by linarith only [norm_nonneg y]), ← div_eq_mul_inv,
    div_le_div_iff₀ (Real.rpow_pos_of_pos (hn y) _)
      (Real.rpow_pos_of_pos (by linarith only [norm_nonneg y]) _),
    one_mul]
  exact hp

end PseudoPrime.AnalyticNumberTheory.General

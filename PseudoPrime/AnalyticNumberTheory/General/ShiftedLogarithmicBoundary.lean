/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.ShiftedLogarithmicResidues
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import PseudoPrime.AnalyticNumberTheory.RectangleGeometry.VerticalLimits

/-!
# Horizontal bounds and limits for shifted logarithmic Perron kernels.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- For x>=1, a nonzero height T, and u<=b, a bound eta on the shifted logarithmic
derivative divided by T^2 gives a kernel bound x^b*eta. The imaginary part controls
the denominator and monotonicity of real powers controls the numerator. No character
or RH hypothesis is required; this supplies uniform horizontal-edge estimates. -/
theorem norm_shiftedLogarithmicKernel_horizontal_le {F : ℂ → ℂ} {x u b T η : ℝ} (σ : ℂ) (hx : 1 ≤ x)
    (hu : u ≤ b) (hT : T ≠ 0) (hD : ‖logDeriv F (σ + ((u : ℂ) + T * Complex.I))‖ / T ^ 2 ≤ η) :
    ‖shiftedLogarithmicKernel F x σ ((u : ℂ) + T * Complex.I)‖ ≤ x ^ b * η := by
  have hsIm : ((u : ℂ) + T * Complex.I).im = T := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
  have hsRe : ((u : ℂ) + T * Complex.I).re = u := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have hden : T ^ 2 ≤ ‖(u : ℂ) + T * Complex.I‖ ^ 2 := by
    rw [← sq_abs T]
    exact
      pow_le_pow_left₀ (abs_nonneg T)
        (by simpa only [hsIm] using Complex.abs_im_le_norm ((u : ℂ) + T * Complex.I)) 2
  have hTpos : 0 < T ^ 2 := sq_pos_of_ne_zero hT
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hxp := Real.rpow_le_rpow_of_exponent_le hx hu
  unfold shiftedLogarithmicKernel
  rw [norm_div, norm_mul, norm_neg, norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos hxpos, hsRe]
  calc
    _ ≤ ‖logDeriv F (σ + ((u : ℂ) + T * Complex.I))‖ * x ^ u / T ^ 2 :=
      div_le_div_of_nonneg_left (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hxpos.le _)) hTpos
        hden
    _ ≤ ‖logDeriv F (σ + ((u : ℂ) + T * Complex.I))‖ * x ^ b / T ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hxp (norm_nonneg _)) hTpos.le
    _ = x ^ b * (‖logDeriv F (σ + ((u : ℂ) + T * Complex.I))‖ / T ^ 2) := by ring
    _ ≤ x ^ b * η := mul_le_mul_of_nonneg_left hD (Real.rpow_nonneg hxpos.le _)

/-- For x >= 1, a <= b, nonzero height T and a common bound eta for the shifted
logarithmic derivative divided by T^2 on (a,b], the horizontal kernel integral has
norm at most x^b*eta*(b-a). Integrate the pointwise norm bound over the interval.
This supplies horizontal contour decay without a separate integrability premise. -/
theorem norm_integral_shiftedLogarithmicKernel_horizontal_le {F : ℂ → ℂ} {x a b T η : ℝ} (σ : ℂ)
    (hx : 1 ≤ x) (hab : a ≤ b) (hT : T ≠ 0)
    (hD : ∀ u ∈ Set.Ioc a b, ‖logDeriv F (σ + ((u : ℂ) + T * Complex.I))‖ / T ^ 2 ≤ η) :
    ‖∫ u in a..b, shiftedLogarithmicKernel F x σ ((u : ℂ) + T * Complex.I)‖ ≤
      x ^ b * η * (b - a) := by
  have hbound :
    ∀ u ∈ Set.uIoc a b, ‖shiftedLogarithmicKernel F x σ ((u : ℂ) + T * Complex.I)‖ ≤ x ^ b * η := by
    intro u hu
    have hu' : u ∈ Set.Ioc a b := by simpa only [Set.uIoc_of_le hab] using hu
    exact norm_shiftedLogarithmicKernel_horizontal_le σ hx hu'.2 hT (hD u hu')
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using hb

/-- For fixed endpoints a<=b, x>=1, and nonzero heights, a logarithmic-derivative
envelope eta tending to zero makes the shifted horizontal integral tend to zero.
Squeeze its norm by the preceding interval estimate. The choice of good heights
and the derivative envelope remain explicit inputs. -/
theorem tendsto_integral_shiftedLogarithmicKernel_horizontal {F : ℂ → ℂ} {x a b : ℝ} (σ : ℂ)
    (hx : 1 ≤ x) (hab : a ≤ b) (T η : ℕ → ℝ) (hT : ∀ k, T k ≠ 0)
    (hη : Filter.Tendsto η Filter.atTop (nhds 0))
    (hD :
      ∀ k, ∀ u ∈ Set.Ioc a b, ‖logDeriv F (σ + ((u : ℂ) + T k * Complex.I))‖ / (T k) ^ 2 ≤ η k) :
    Filter.Tendsto (fun k ↦ ∫ u in a..b, shiftedLogarithmicKernel F x σ ((u : ℂ) + T k * Complex.I))
      Filter.atTop (nhds 0) := by
  apply
    squeeze_zero_norm
      (fun k ↦ norm_integral_shiftedLogarithmicKernel_horizontal_le σ hx hab (hT k) (hD k))
  simpa only [mul_zero, zero_mul] using (hη.const_mul (x ^ b)).mul_const (b - a)

end PseudoPrime.AnalyticNumberTheory.General

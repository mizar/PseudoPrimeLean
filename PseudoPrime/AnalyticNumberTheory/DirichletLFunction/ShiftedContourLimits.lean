/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ShiftedLogMellinInversion
public import PseudoPrime.AnalyticNumberTheory.General.ShiftedLogarithmicBoundary
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Vertical integrability and height limits of shifted Dirichlet contours.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For any character, x > 0, sigma >= 1 and tau > 0, the shifted kernel is continuous
on Re s = tau. The translated line lies strictly right of one, where L is analytic
and nonzero and hence its logarithmic derivative is analytic. The Mellin denominator
also does not vanish. This gives measurability for the truncated-to-full right-edge limit. -/
theorem continuous_shiftedLogContourKernel_vertical {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {x σ τ : ℝ} (hx : 0 < x) (hσ : 1 ≤ σ) (hτ : 0 < τ) :
    Continuous (fun y : ℝ ↦ shiftedLogContourKernel χ x σ ((τ : ℂ) + y * Complex.I)) := by
  have hline : Continuous (fun y : ℝ ↦ (τ : ℂ) + y * Complex.I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hshift : Continuous (fun y : ℝ ↦ (σ : ℂ) + ((τ : ℂ) + y * Complex.I)) :=
    continuous_const.add hline
  apply continuous_iff_continuousAt.mpr
  intro y
  have hre : 1 < ((σ : ℂ) + ((τ : ℂ) + y * Complex.I)).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
      mul_zero, zero_mul, sub_zero, add_zero]
    linarith only [hσ, hτ]
  have hne : (σ : ℂ) + ((τ : ℂ) + y * Complex.I) ≠ 1 := by
    intro he
    rw [he, Complex.one_re] at hre
    exact (lt_irrefl 1) hre
  have hOn : DifferentiableOn ℂ χ.LFunction ({1}ᶜ : Set ℂ) := by
    intro z hz
    exact
      (χ.differentiableAt_LFunction z
          (Or.inl (Set.mem_compl_singleton_iff.mp hz))).differentiableWithinAt
  have hF : AnalyticAt ℂ χ.LFunction ((σ : ℂ) + ((τ : ℂ) + y * Complex.I)) :=
    hOn.analyticAt (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr hne))
  have hD : ContinuousAt (logDeriv χ.LFunction) ((σ : ℂ) + ((τ : ℂ) + y * Complex.I)) :=
    (hF.deriv.div hF (χ.LFunction_ne_zero_of_one_le_re (Or.inr hne) hre.le)).continuousAt
  have hkernel :=
    ((hD.comp (f := fun y : ℝ ↦ (σ : ℂ) + ((τ : ℂ) + y * Complex.I)) hshift.continuousAt).neg.mul
          ((hline.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))).continuousAt)).div
      (hline.continuousAt.pow 2)
      (pow_ne_zero 2
        (by
          intro he
          have hh := congrArg Complex.re he
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
            Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.zero_re] at hh
          exact hτ.ne' hh))
  change
    ContinuousAt
      (fun t : ℝ ↦
        -logDeriv χ.LFunction ((σ : ℂ) + ((τ : ℂ) + t * Complex.I)) *
            (x : ℂ) ^ ((τ : ℂ) + t * Complex.I) /
          ((τ : ℂ) + t * Complex.I) ^ 2)
      y at hkernel
  simpa only [shiftedLogContourKernel, logDeriv_apply, neg_div] using hkernel

/-- For any character, x>0, sigma>=1, and tau>0, the shifted right-edge kernel is
integrable over the real height. Absolute convergence bounds L'/L by the Mangoldt series,
while the inverse-square Mellin kernel is integrable. No primitivity or RH is required.
This removes the right-edge integrability assumption from shifted rectangle limits. -/
theorem integrable_shiftedLogContourKernel_vertical {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {x σ τ : ℝ} (hx : 0 < x) (hσ : 1 ≤ σ) (hτ : 0 < τ) :
    MeasureTheory.Integrable
      (fun y : ℝ ↦ shiftedLogContourKernel χ x σ ((τ : ℂ) + y * Complex.I)) := by
  let C : ℝ := ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (σ + τ)
  have hi := (General.verticalIntegrable_mellinLogKernel hτ.ne').norm.const_mul (C * x ^ τ)
  apply hi.mono' (continuous_shiftedLogContourKernel_vertical χ hx hσ hτ).aestronglyMeasurable
  filter_upwards with y
  have hbound :=
    norm_neg_deriv_div_dirichletLFunction_le_vonMangoldt_tsum χ
      (show 1 < σ + τ by linarith only [hσ, hτ]) y
  have heq : (σ : ℂ) + ((τ : ℂ) + y * Complex.I) = ((σ + τ : ℝ) : ℂ) + y * Complex.I := by
    rw [Complex.ofReal_add, add_assoc]
  have hre : ((τ : ℂ) + y * Complex.I).re = τ := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
      mul_zero, zero_mul, sub_zero, add_zero]
  change
    ‖shiftedLogContourKernel χ x σ ((τ : ℂ) + y * Complex.I)‖ ≤
      C * x ^ τ * ‖((τ : ℂ) + y * Complex.I)⁻¹ ^ 2‖
  unfold shiftedLogContourKernel
  rw [heq, norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, hre, norm_pow, norm_pow,
    norm_inv, inv_pow, div_eq_mul_inv]
  exact
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg hx.le _))
      (inv_nonneg.mpr (sq_nonneg _))

/-- Under positive scale and vertical abscissa with sigma>=1, the symmetric truncated
right-edge integral tends to the whole-line integral. Apply interval exhaustion to the
proved integrability. This supports the height limit before shifting the left edge. -/
theorem tendsto_intervalIntegral_shiftedLogContourKernel {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {x σ τ : ℝ} (hx : 0 < x) (hσ : 1 ≤ σ) (hτ : 0 < τ) :
    Filter.Tendsto
      (fun T : ℝ ↦ ∫ y in (-T)..T, shiftedLogContourKernel χ x σ ((τ : ℂ) + y * Complex.I))
      Filter.atTop (nhds (∫ y : ℝ, shiftedLogContourKernel χ x σ ((τ : ℂ) + y * Complex.I))) := by
  exact
    MeasureTheory.intervalIntegral_tendsto_integral
      (integrable_shiftedLogContourKernel_vertical χ hx hσ hτ) Analysis.tendsto_neg_atTop_atBot'
      Filter.tendsto_id

/-- For x>0, sigma>=1, and tau>0, assume heights tending to infinity, vanishing horizontal
integrals, and an integrable left edge. The normalized shifted rectangle boundary tends
to the shifted arithmetic logarithmic sum minus the normalized whole-line left integral.
Assemble the geometric limit and apply shifted Mellin inversion on the right. Horizontal
height selection and left-edge control remain explicit; no residue or RH assumption is hidden. -/
theorem tendsto_normalized_shiftedLogBoundary {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {x σ τ a : ℝ} (hx : 0 < x) (hσ : 1 ≤ σ) (hτ : 0 < τ) (T : ℕ → ℝ)
    (hT : Filter.Tendsto T Filter.atTop Filter.atTop)
    (hbottom :
      Filter.Tendsto
        (fun k ↦ ∫ u in a..τ, shiftedLogContourKernel χ x σ ((u : ℂ) - T k * Complex.I))
        Filter.atTop (nhds 0))
    (htop :
      Filter.Tendsto
        (fun k ↦ ∫ u in a..τ, shiftedLogContourKernel χ x σ ((u : ℂ) + T k * Complex.I))
        Filter.atTop (nhds 0))
    (hleft :
      MeasureTheory.Integrable
        (fun y : ℝ ↦ shiftedLogContourKernel χ x σ ((a : ℂ) + y * Complex.I))) :
    Filter.Tendsto
      (fun k ↦
        (-Complex.I / (2 * (Real.pi : ℂ))) *
          RectangleGeometry.rectangleBoundaryIntegral (shiftedLogContourKernel χ x σ)
            ((a : ℂ) - T k * Complex.I) ((τ : ℂ) + T k * Complex.I))
      Filter.atTop
      (nhds
        (General.logarithmicWeightedSum
            (General.shiftedLSeriesCoefficient
              (fun n ↦ χ (n : ZMod N) * (ArithmeticFunction.vonMangoldt n : ℂ)) σ)
            x -
          (2 * Real.pi : ℝ)⁻¹ •
            ∫ y : ℝ, shiftedLogContourKernel χ x σ ((a : ℂ) + y * Complex.I))) := by
  have hb :=
    (RectangleGeometry.tendsto_rectangleBoundaryIntegral_of_horizontal_limits T hT hbottom htop
          hleft (integrable_shiftedLogContourKernel_vertical χ hx hσ hτ)).const_mul
      (-Complex.I / (2 * (Real.pi : ℂ)))
  have hcoeff : (-Complex.I / (2 * (Real.pi : ℂ))) * Complex.I = ((2 * Real.pi : ℝ)⁻¹ : ℂ) := by
    rw [div_mul_eq_mul_div, neg_mul, Complex.I_mul_I, neg_neg, one_div]
    rw [Complex.ofReal_mul, Complex.ofReal_ofNat]
  have hsum := shifted_logarithmic_sum_eq_integral χ hx hσ hτ
  rw [← mul_assoc, hcoeff, mul_sub] at hb
  simpa only [hsum, Complex.real_smul, Complex.ofReal_inv] using hb

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction

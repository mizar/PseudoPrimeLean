/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.RationalPoleContour
public import PseudoPrime.Analysis.CauchyWeightedIntegrals
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.CompletedVariableGapBounds
public import PseudoPrime.LLS.PaperStatements.MellinKernelVerticalIntegrability

/-! Fourth-order gamma budget. -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- On the critical Mellin line, the actual fourth-order kernel norm is rho cubed
divided by (rho squared plus height squared) squared, with rho=25/26.
Normalize the existing exact norm formula. This exposes its scaled Cauchy moments. -/
theorem fourContour_central_norm (t : ℝ) :
    ‖fourContourKernel.function (Complex.I * t)‖ =
      (25 / 26 : ℝ) ^ 3 / ((25 / 26 : ℝ) ^ 2 + t ^ 2) ^ 2 := by
  change ‖Analysis.rationalPoleFunction 2 (13 / 25) (14 / 25) (Complex.I * t)‖ = _
  rw [Analysis.norm_rationalPoleFunction 2 (by norm_num only) t]
  have hp : (25 / 26 : ℝ) ^ 2 + t ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg (by norm_num only) (sq_nonneg t))
  have hq : 1 + (2 * (13 / 25 : ℝ) * t) ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg _))
  apply (div_eq_div_iff (pow_ne_zero 2 hq) (pow_ne_zero 2 hp)).mpr
  ring

/-- The exact normalized linear-height majorant integral is 11/4+rho/(2pi).
Use the scaled unweighted and absolute first Cauchy moments with rho=25/26.
This evaluates the uniform gamma budget for the actual fourth-order kernel. -/
theorem fourContour_gamma_budget :
    (∫ t : ℝ, ‖fourContourKernel.function (Complex.I * t)‖ * (11 + |t|)) / (2 * Real.pi) =
      11 / 4 + (25 / 26 : ℝ) / (2 * Real.pi) := by
  have he :
    (fun t : ℝ ↦ ‖fourContourKernel.function (Complex.I * t)‖ * (11 + |t|)) =
      (fun t : ℝ ↦ (25 / 26 : ℝ) ^ 3 * ((11 + 1 * |t|) / ((25 / 26 : ℝ) ^ 2 + t ^ 2) ^ 2)) := by
    funext t
    rw [fourContour_central_norm]
    ring
  rw [he, MeasureTheory.integral_const_mul,
    Analysis.integral_scaled_cauchy_linear (by norm_num only : (0 : ℝ) < 25 / 26) 11 1]
  apply (div_eq_iff (mul_ne_zero (by norm_num only) Real.pi_ne_zero)).mpr
  rw [add_mul, div_mul_cancel₀ _ (mul_ne_zero (by norm_num only) Real.pi_ne_zero)]
  ring

/-- The actual fourth-order kernel norm times 11+abs(t) is integrable.
Rewrite it as a constant multiple of the integrable scaled Cauchy moments.
This justifies the explicit majorant used to bound the central gamma integral. -/
theorem fourContour_gammaMajorant_int :
    MeasureTheory.Integrable
      (fun t : ℝ ↦ ‖fourContourKernel.function (Complex.I * t)‖ * (11 + |t|)) := by
  have hd : (0 : ℝ) < 25 / 26 := by norm_num only
  apply
    (((Analysis.integrable_scaled_cauchy_two hd).const_mul 11).add
            (Analysis.integrable_scaled_cauchy_abs hd)).const_mul
        ((25 / 26 : ℝ) ^ 3) |>.congr
  exact
    Filter.Eventually.of_forall fun t ↦ by
      dsimp only [Pi.add_apply, Pi.mul_apply]
      rw [fourContour_central_norm]
      ring

/-- For every character and positive scale, the normalized central gamma integral
for the actual extended fourth-order kernel has norm less than three.
The gamma logarithmic derivative is bounded by 11+abs(t), and the scale phase has norm one.
Integrate the explicit majorant and use pi>3. No RH or finite entrance is required. -/
theorem fourContour_gammaIntegral_lt_three {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
              (fourContourKernel.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)))‖ <
      3 := by
  let F := fun t : ℝ ↦
    logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
      (fourContourKernel.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t))
  have hb (t : ℝ) : ‖F t‖ ≤ ‖fourContourKernel.function (Complex.I * t)‖ * (11 + |t|) := by
    have hg :=
      AnalyticNumberTheory.DirichletLFunction.norm_logDeriv_gammaFactor_positive_strip_le_linear χ
        (s := Complex.I * t + 1 / 2)
        (by
          norm_num only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, zero_add,
            Complex.div_re, Complex.re_ofNat, Complex.im_ofNat, Complex.one_re, Complex.one_im,
            Complex.normSq_apply])
        (by
          norm_num only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, zero_add,
            Complex.div_re, Complex.re_ofNat, Complex.im_ofNat, Complex.one_re, Complex.one_im,
            Complex.normSq_apply])
    norm_num only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_mul, zero_add, one_mul, add_zero, Complex.div_im,
      Complex.re_ofNat, Complex.im_ofNat, Complex.one_re, Complex.one_im,
      Complex.normSq_apply] at hg
    dsimp only [F]
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, sub_zero, Real.rpow_zero, mul_one]
    exact (mul_le_mul_of_nonneg_right hg (norm_nonneg _)).trans_eq (mul_comm _ _)
  have hi :=
    MeasureTheory.norm_integral_le_of_norm_le fourContour_gammaMajorant_int
      (Filter.Eventually.of_forall hb)
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num only) Real.pi_pos
  have htail : (25 / 26 : ℝ) / (2 * Real.pi) < 1 / 4 :=
    (div_lt_iff₀ hp).mpr (by linarith only [Real.pi_gt_three])
  have he :
    (1 / (2 * Real.pi)) * (∫ t : ℝ, ‖fourContourKernel.function (Complex.I * t)‖ * (11 + |t|)) =
      11 / 4 + (25 / 26 : ℝ) / (2 * Real.pi) := by
    simpa only [one_div_mul_eq_div] using fourContour_gamma_budget
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hp)]
  exact
    ((mul_le_mul_of_nonneg_left hi (one_div_pos.mpr hp).le).trans_eq he).trans_lt
      (by linarith only [htail])

/-- For every character and positive scale, the actual central gamma integrand is integrable.
Apply the generic allowed-line theorem to the extended admissible kernel at real part zero.
This accompanies the explicit norm bound with genuine Bochner integrability. -/
theorem fourContour_gammaIntegral_int {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
          (fourContourKernel.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t))) := by
  have hc : (0 : ℝ) ≤ 1 / 2 + fourContourKernel.delta :=
    add_nonneg (by norm_num only) fourContourKernel.delta_pos.le
  simpa only [Complex.ofReal_zero, zero_add, mul_assoc] using
    MellinKernel.integrable_gammaFactor_power_line fourContourKernel χ (c := 0) (by norm_num only)
      hc (by norm_num only) hx

end PseudoPrime.LLS.PaperStatements

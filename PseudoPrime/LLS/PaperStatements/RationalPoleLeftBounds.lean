/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.RationalPoleGammaBounds

/-! Explicit completed-L left-contour budget for the actual fourth-order kernel. -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For every height, log(4+abs(t)) is at most 2+abs(t)/4.
Split off log four and apply log(1+u)<=u with u nonnegative.
This replaces logarithmic contour growth by the two explicit Cauchy moments. -/
private theorem log_four_add_abs_le (t : ℝ) : Real.log (4 + |t|) ≤ 2 + |t| / 4 := by
  have hpos : 0 < 1 + |t| / 4 :=
    add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg (abs_nonneg t) (by norm_num only))
  have h := Real.log_le_sub_one_of_pos hpos
  have h2 := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 2)
  have he : 4 + |t| = 2 * 2 * (1 + |t| / 4) := by ring
  rw [he, Real.log_mul (by norm_num only : (2 : ℝ) * 2 ≠ 0) hpos.ne',
    Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) (by norm_num only : (2 : ℝ) ≠ 0)]
  linarith only [h, h2]

/-- The actual fourth-order kernel norm on the left Mellin contour at -3/4.
Its distance from the pole is 11/52, and exponential modulation contributes exp(-21/25).
Normalize the shifted reciprocal-power formula. This exposes the exact Cauchy weight. -/
theorem fourContour_left_norm (t : ℝ) :
    ‖fourContourKernel.function ((-3 / 4 : ℂ) + Complex.I * t)‖ =
      (25 / 26 : ℝ) ^ 3 * Real.exp (-(21 / 25)) / ((11 / 52 : ℝ) ^ 2 + t ^ 2) ^ 2 := by
  have hn :
    ‖((-3 / 4 : ℂ) + Complex.I * t) + ((2 * (13 / 25 : ℝ))⁻¹ : ℝ)‖ ^ 2 =
      (11 / 52 : ℝ) ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    norm_num only [Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im, Complex.div_re,
      Complex.div_im, Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_apply, Complex.one_re,
      Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
    ring
  have he :
    ‖Complex.exp (2 * ((14 / 25 : ℝ) : ℂ) * ((-3 / 4 : ℂ) + Complex.I * t))‖ =
      Real.exp (-(21 / 25)) := by
    rw [Complex.norm_exp]
    congr 1
    norm_num only [Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im, Complex.div_re,
      Complex.div_im, Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_apply, Complex.one_re,
      Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
    ring
  change ‖Analysis.rationalPoleFunction 2 (13 / 25) (14 / 25) ((-3 / 4 : ℂ) + Complex.I * t)‖ = _
  rw [Analysis.rationalPole_eq_shifted_power 2 (by norm_num only) (14 / 25), norm_mul, norm_div,
    norm_pow, norm_div, norm_pow, he]
  simp only [pow_mul, hn]
  norm_num only [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  ring

/-- On the left contour, omit the exponential saving to obtain a simple Cauchy majorant.
The modulation factor exp(-21/25) is at most one. This safe bound has rational constants
and is sufficient for the advertised finite left-contour error budget. -/
theorem fourContour_left_norm_le (t : ℝ) :
    ‖fourContourKernel.function ((-3 / 4 : ℂ) + Complex.I * t)‖ ≤
      (25 / 26 : ℝ) ^ 3 / ((11 / 52 : ℝ) ^ 2 + t ^ 2) ^ 2 := by
  rw [fourContour_left_norm]
  have he : Real.exp (-(21 / 25 : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num only)
  simpa only [mul_one] using
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left he (by norm_num only : (0 : ℝ) ≤ (25 / 26 : ℝ) ^ 3)) (sq_nonneg _)

/-- The left-contour rational majorant is integrable for every real conductor parameter.
Split its constant and linear-height parts into the two proved Cauchy moments.
This supplies the integrable domination used for the actual completed-L integrand. -/
theorem fourContour_left_majorant_int (A : ℝ) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        (25 / 26 : ℝ) ^ 3 * ((A + 33 + (1 / 8 : ℝ) * |t|) / ((11 / 52 : ℝ) ^ 2 + t ^ 2) ^ 2)) := by
  have hd : (0 : ℝ) < 11 / 52 := by norm_num only
  apply
    (((Analysis.integrable_scaled_cauchy_two hd).const_mul (A + 33)).add
            ((Analysis.integrable_scaled_cauchy_abs hd).const_mul (1 / 8 : ℝ))).const_mul
        ((25 / 26 : ℝ) ^ 3) |>.congr
  exact
    Filter.Eventually.of_forall fun t ↦ by
      dsimp only [Pi.add_apply, Pi.mul_apply]
      ring

/-- For nonnegative A, the normalized integral of the left majorant is at most 24A+793.
Evaluate its two Cauchy moments; their normalized coefficients are at most 24 and one.
This is the explicit arithmetic budget later used with A=log q. -/
theorem fourContour_left_budget {A : ℝ} (hA : 0 ≤ A) :
    (∫ t : ℝ,
          (25 / 26 : ℝ) ^ 3 * ((A + 33 + (1 / 8 : ℝ) * |t|) / ((11 / 52 : ℝ) ^ 2 + t ^ 2) ^ 2)) /
        (2 * Real.pi) ≤
      24 * A + 793 := by
  rw [MeasureTheory.integral_const_mul,
    Analysis.integral_scaled_cauchy_linear (by norm_num only : (0 : ℝ) < 11 / 52) (A + 33) (1 / 8)]
  have hb : (25 / 26 : ℝ) ^ 3 / (16 * Real.pi * (11 / 52 : ℝ) ^ 2) ≤ 1 := by
    apply (div_le_one (mul_pos (mul_pos (by norm_num only) Real.pi_pos) (by norm_num only))).mpr
    nlinarith only [Real.pi_gt_three]
  calc
    _ =
        ((25 / 26 : ℝ) ^ 3 / (4 * (11 / 52 : ℝ) ^ 3)) * (A + 33) +
          (25 / 26 : ℝ) ^ 3 / (16 * Real.pi * (11 / 52 : ℝ) ^ 2) :=
      by
      calc
        _ =
            (Real.pi * Real.pi⁻¹) * (((25 / 26 : ℝ) ^ 3 / (4 * (11 / 52 : ℝ) ^ 3)) * (A + 33)) +
              (25 / 26 : ℝ) ^ 3 / (16 * Real.pi * (11 / 52 : ℝ) ^ 2) :=
          by ring
        _ = _ := by rw [mul_inv_cancel₀ Real.pi_ne_zero, one_mul]
    _ ≤ 24 * (A + 33) + 1 :=
      add_le_add
        (mul_le_mul_of_nonneg_right
          (by norm_num only : (25 / 26 : ℝ) ^ 3 / (4 * (11 / 52 : ℝ) ^ 3) ≤ 24)
          (by linarith only [hA]))
        hb
    _ = _ := by ring

/-- For a primitive nonprincipal character with nonprincipal inverse, the completed
logarithmic derivative at real part -1/4 is at most log q+33+abs(t)/8 in norm.
Use the functional-equation left-strip estimate, normalize log q and bound logarithmic
height growth linearly. The statement is unconditional and keeps both nonprincipal inputs. -/
theorem fourContour_left_logDeriv_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (t : ℝ) :
    ‖logDeriv χ.completedLFunction ((-1 / 4 : ℂ) + Complex.I * t)‖ ≤
      Real.log q + 33 + (1 / 8 : ℝ) * |t| := by
  have h :=
    AnalyticNumberTheory.DirichletLFunction.norm_logDeriv_completed_left_strip_le_gap_log hp hne
      hinv (e := (1 / 4 : ℝ)) (by norm_num only) (by norm_num only) t
  have hlog : ‖Complex.log (q : ℂ)‖ = Real.log q := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg q), Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_nonneg
        (Real.log_nonneg (Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))))]
  rw [hlog] at h
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at h
  linarith only [h, log_four_add_abs_le t]

/-- For a primitive nonprincipal character with nonprincipal inverse and positive x,
the actual completed-L Mellin integrand on the left contour is continuous in height.
Combine completed logarithmic-derivative continuity, kernel holomorphy on its enlarged
region, and continuity of the complex power. This supplies genuine Bochner measurability. -/
theorem fourContour_left_continuous {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    Continuous
      (fun t : ℝ ↦
        logDeriv χ.completedLFunction ((-1 / 4 : ℂ) + Complex.I * t) *
          (fourContourKernel.function ((-3 / 4 : ℂ) + Complex.I * t) *
            (x : ℂ) ^ ((-3 / 4 : ℂ) + Complex.I * t))) := by
  have hline : Continuous (fun t : ℝ ↦ (-3 / 4 : ℂ) + Complex.I * t) :=
    continuous_const.add (continuous_const.mul Complex.continuous_ofReal)
  have hk : Continuous (fun t : ℝ ↦ fourContourKernel.function ((-3 / 4 : ℂ) + Complex.I * t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact
      ContinuousAt.comp (g := fourContourKernel.function) (f := fun t : ℝ ↦
        (-3 / 4 : ℂ) + Complex.I * t)
        (fourContour_differentiableAt (fourContour_left_mem t)).continuousAt hline.continuousAt
  have hc :=
    AnalyticNumberTheory.DirichletLFunction.continuous_completed_logDeriv_vertical_left hp hne hinv
      (σ := (-1 / 4 : ℝ)) (by norm_num only)
  have hc' :
    Continuous (fun t : ℝ ↦ logDeriv χ.completedLFunction ((-1 / 4 : ℂ) + Complex.I * t)) := by
    simpa only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using hc
  exact hc'.mul (hk.mul (hline.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))))

/-- For a primitive nonprincipal character with nonprincipal inverse and positive x,
the actual completed-L Mellin integrand on real part -3/4 is absolutely integrable.
Its normalized integral has norm at most (24 log q+793)x^(-3/4).
Dominate it by the explicit Cauchy majorant times the exact power norm and integrate.
No RH is required; finite principal and local-cost terms remain separate. -/
theorem fourContour_left_integral_bound {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    let F := fun t : ℝ ↦
      logDeriv χ.completedLFunction ((-1 / 4 : ℂ) + Complex.I * t) *
        (fourContourKernel.function ((-3 / 4 : ℂ) + Complex.I * t) *
          (x : ℂ) ^ ((-3 / 4 : ℂ) + Complex.I * t))
    MeasureTheory.Integrable F ∧
      ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, F t)‖ ≤
        (24 * Real.log q + 793) * x ^ (-3 / 4 : ℝ) := by
  dsimp only
  let H := fun t : ℝ ↦
    (25 / 26 : ℝ) ^ 3 * ((Real.log q + 33 + (1 / 8 : ℝ) * |t|) / ((11 / 52 : ℝ) ^ 2 + t ^ 2) ^ 2)
  have hA : 0 ≤ Real.log q :=
    Real.log_nonneg (Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)))
  have hxpow : 0 ≤ x ^ (-3 / 4 : ℝ) := (Real.rpow_pos_of_pos hx _).le
  have hb (t : ℝ) :
    ‖logDeriv χ.completedLFunction ((-1 / 4 : ℂ) + Complex.I * t) *
          (fourContourKernel.function ((-3 / 4 : ℂ) + Complex.I * t) *
            (x : ℂ) ^ ((-3 / 4 : ℂ) + Complex.I * t))‖ ≤
      x ^ (-3 / 4 : ℝ) * H t := by
    have hr : ((-3 / 4 : ℂ) + Complex.I * t).re = (-3 / 4 : ℝ) := by
      norm_num only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.neg_re, Complex.div_re, Complex.re_ofNat, Complex.im_ofNat,
        Complex.normSq_apply, mul_zero, zero_mul, sub_zero, Complex.one_re, Complex.one_im,
        add_zero]
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, hr]
    have hm :=
      mul_le_mul (fourContour_left_logDeriv_le hp hne hinv t) (fourContour_left_norm_le t)
        (norm_nonneg _)
        (add_nonneg (add_nonneg hA (by norm_num only))
          (mul_nonneg (by norm_num only) (abs_nonneg t)))
    have hh := mul_le_mul_of_nonneg_right hm hxpow
    dsimp only [H]
    convert hh using 1 <;> ring
  have hiH := (fourContour_left_majorant_int (Real.log q)).const_mul (x ^ (-3 / 4 : ℝ))
  refine
    ⟨hiH.mono' (fourContour_left_continuous hp hne hinv hx).aestronglyMeasurable
        (Filter.Eventually.of_forall hb),
      ?_⟩
  have hi := MeasureTheory.norm_integral_le_of_norm_le hiH (Filter.Eventually.of_forall hb)
  have hπ : 0 < 2 * Real.pi := mul_pos (by norm_num only) Real.pi_pos
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hπ)]
  apply (mul_le_mul_of_nonneg_left hi (one_div_pos.mpr hπ).le).trans
  rw [MeasureTheory.integral_const_mul]
  have he := mul_le_mul_of_nonneg_right (fourContour_left_budget hA) hxpow
  convert he using 1
  ring

/-- The signed left integral in the completed Mellin contour convention obeys
the explicit (24 log q+793)x^(-3/4) bound for primitive nonprincipal characters
with nonprincipal inverse and positive x. Shift the completed argument by one half
and remove the global minus sign in norm. This matches the actual contour consumer. -/
theorem fourContour_left_signed_bound {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            -logDeriv χ.completedLFunction (((-3 / 4 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
              (fourContourKernel.function (((-3 / 4 : ℝ) : ℂ) + Complex.I * t) *
                (x : ℂ) ^ (((-3 / 4 : ℝ) : ℂ) + Complex.I * t)))‖ ≤
      (24 * Real.log q + 793) * x ^ (-3 / 4 : ℝ) := by
  have h := fourContour_left_integral_bound hp hne hinv hx
  dsimp only at h
  have he (t : ℝ) : (-3 / 4 : ℂ) + Complex.I * t + 1 / 2 = (-1 / 4 : ℂ) + Complex.I * t := by ring
  simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat, neg_mul,
    MeasureTheory.integral_neg, mul_neg, norm_neg, he]
  simpa only [Complex.ofReal_div] using h.2

end PseudoPrime.LLS.PaperStatements

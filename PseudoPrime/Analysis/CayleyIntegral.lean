/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.CircleAverage
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Real-line integral formula for the Cayley circle

The arctangent coordinate identifies real heights with the circle away from one.
Its Jacobian rewrites uniform circle averages as weighted real-line integrals.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The period-one parameter of the Cayley circle, equal to one half plus arctan(t)/pi.
Its range is the open unit interval and its derivative supplies the real-line Jacobian. -/
noncomputable def cayleyParameter (t : ℝ) : ℝ :=
  1 / 2 + Real.arctan t / Real.pi

/-- Every finite real height has Cayley parameter strictly between zero and one.
Divide the strict arctangent bounds by positive pi; the omitted endpoint represents infinity. -/
theorem cayleyParameter_mem_Ioo (t : ℝ) : cayleyParameter t ∈ Set.Ioo 0 1 := by
  have ht := Real.arctan_mem_Ioo t
  have hl : -(1 / 2 : ℝ) < Real.arctan t / Real.pi :=
    (lt_div_iff₀ Real.pi_pos).mpr (by linarith only [ht.1])
  have hu : Real.arctan t / Real.pi < (1 / 2 : ℝ) :=
    (div_lt_iff₀ Real.pi_pos).mpr (by linarith only [ht.2])
  constructor <;> dsimp only [cayleyParameter] <;> linarith only [hl, hu]

/-- The real-line Cayley parameter has range exactly the open unit interval.
Use the arctangent range and solve its affine rescaling to obtain surjectivity. -/
theorem range_cayleyParameter : Set.range cayleyParameter = Set.Ioo 0 1 := by
  apply Set.Subset.antisymm
  · rintro y ⟨t, rfl⟩
    exact cayleyParameter_mem_Ioo t
  · intro y hy
    have h0 := mul_pos Real.pi_pos hy.1
    have h1 := mul_pos Real.pi_pos (sub_pos.mpr hy.2)
    have ha : Real.pi * (y - 1 / 2) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> nlinarith only [h0, h1]
    rw [← Real.range_arctan] at ha
    obtain ⟨t, ht⟩ := ha
    refine ⟨t, ?_⟩
    dsimp only [cayleyParameter]
    rw [ht, mul_div_cancel_left₀ _ Real.pi_ne_zero]
    ring

/-- The Cayley parameter is strictly increasing in real height.
Strict monotonicity of arctangent and positive pi give injectivity for change of variables. -/
theorem cayleyParameter_strictMono : StrictMono cayleyParameter := by
  intro t u htu
  change (1 / 2 : ℝ) + Real.arctan t / Real.pi < (1 / 2 : ℝ) + Real.arctan u / Real.pi
  exact
    add_lt_add_of_le_of_lt le_rfl (div_lt_div_of_pos_right (Real.arctan_strictMono htu) Real.pi_pos)

/-- The Cayley parameter has derivative 1/(pi*(1+t^2)) at every real height.
Differentiate arctangent and simplify the constant denominator; this is the circle Jacobian. -/
theorem hasDerivAt_cayleyParameter (t : ℝ) :
    HasDerivAt cayleyParameter (1 / (Real.pi * (1 + t ^ 2))) t := by
  have h := ((Real.hasDerivAt_arctan t).div_const Real.pi).const_add (1 / 2)
  convert h using 1
  · rfl
  · rw [div_div]
    congr 1
    ring

/-- For any real normed-space-valued function, integration over the open unit interval
is real-line integration after the Cayley parameter substitution with its positive Jacobian.
The injective one-dimensional change-of-variables theorem needs no extra integrability premise. -/
theorem integral_cayleyParameter {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) :
    (∫ u in Set.Ioo (0 : ℝ) 1, f u) =
      ∫ t : ℝ, (1 / (Real.pi * (1 + t ^ 2))) • f (cayleyParameter t) := by
  have h :=
    MeasureTheory.integral_image_eq_integral_abs_deriv_smul (s := Set.univ) MeasurableSet.univ
      (fun t _ => (hasDerivAt_cayleyParameter t).hasDerivWithinAt)
      cayleyParameter_strictMono.injective.injOn f
  rw [Set.image_univ, range_cayleyParameter] at h
  simp only [MeasureTheory.setIntegral_univ] at h
  rw [h]
  apply MeasureTheory.integral_congr_ae
  exact
    Filter.Eventually.of_forall
      (fun t => by
        change
          |1 / (Real.pi * (1 + t ^ 2))| • f (cayleyParameter t) =
            (1 / (Real.pi * (1 + t ^ 2))) • f (cayleyParameter t)
        rw [abs_of_pos
            (div_pos zero_lt_one (mul_pos Real.pi_pos (by nlinarith only [sq_nonneg t])))])

/-- The probability circle average is the real-line integral of its Cayley-parameter
pullback against 1/(pi*(1+t^2)). Identify Haar integration with a unit interval integral
and apply the real-line substitution; this gives the limiting zero-distribution integral. -/
theorem circleAverage_cayleyParameter (f : C(Circle, ℂ)) :
    circleAverage f =
      ∫ t : ℝ,
        (1 / (Real.pi * (1 + t ^ 2))) •
          f (AddCircle.toCircle (cayleyParameter t : AddCircle (1 : ℝ))) := by
  rw [circleAverage_apply, AddCircle.integral_haarAddCircle]
  simp only [inv_one, one_smul]
  rw [← AddCircle.intervalIntegral_preimage (T := (1 : ℝ)) 0]
  simp only [zero_add]
  rw [intervalIntegral.integral_of_le zero_le_one, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  exact integral_cayleyParameter _

/-- The period-one angular coordinate of the Cayley parameter is 2*arctan(t)+pi.
Cancel nonzero pi in its affine definition to match the circle exponential. -/
theorem cayleyParameter_angle (t : ℝ) :
    2 * Real.pi * cayleyParameter t = 2 * Real.arctan t + Real.pi := by
  dsimp only [cayleyParameter]
  have hc := div_mul_cancel₀ (Real.arctan t) Real.pi_ne_zero
  nlinarith only [hc]

/-- The circle exponential at 2*arctan(t)+pi equals the Cayley quotient
(1-I*t-2)/(1-I*t). Double-angle identities and the arctangent sine and cosine formulas
identify the real and imaginary parts; this matches the completed-zero moment coordinate. -/
theorem cayley_circle_exp (t : ℝ) :
    (Circle.exp (2 * Real.arctan t + Real.pi) : ℂ) =
      ((1 : ℂ) - Complex.I * t - 2) / ((1 : ℂ) - Complex.I * t) := by
  have hp : 0 ≤ 1 + t ^ 2 := by nlinarith only [sq_nonneg t]
  have hn : Complex.normSq ((1 : ℂ) - Complex.I * t) = 1 + t ^ 2 := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, one_mul, sub_zero, zero_sub, zero_add]
    ring
  apply Complex.ext
  · rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_re, Real.cos_add_pi, Real.cos_two_mul,
      Real.cos_sq_arctan, Complex.div_re, hn]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.one_re,
      Complex.one_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      mul_zero, one_mul, sub_zero, zero_sub, mul_neg, zero_add, show (2 : ℂ).re = (2 : ℝ) from rfl,
      show (2 : ℂ).im = (0 : ℝ) from rfl]
    simp only [neg_mul, neg_neg, mul_one]
    norm_num only
    change -(2 * (1 / (1 + t ^ 2)) - 1) = -1 / (1 + t ^ 2) + t * t / (1 + t ^ 2)
    have hc :=
      div_mul_cancel₀ (1 : ℝ)
        (show (1 + t ^ 2 : ℝ) ≠ 0 from ne_of_gt (by nlinarith only [sq_nonneg t]))
    rw [← add_div]
    apply
      (eq_div_iff (show (1 + t ^ 2 : ℝ) ≠ 0 from ne_of_gt (by nlinarith only [sq_nonneg t]))).mpr
    nlinarith only [hc]
  · rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_im, Real.sin_add_pi, Real.sin_two_mul,
      Real.sin_arctan, Real.cos_arctan, Complex.div_im, hn]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.one_re,
      Complex.one_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      mul_zero, one_mul, sub_zero, zero_sub, mul_neg, zero_add, show (2 : ℂ).re = (2 : ℝ) from rfl,
      show (2 : ℂ).im = (0 : ℝ) from rfl]
    simp only [mul_one]
    norm_num only
    simp only [neg_one_mul, neg_neg]
    change
      -(2 * (t / Real.sqrt (1 + t ^ 2)) * (1 / Real.sqrt (1 + t ^ 2))) =
        -t / (1 + t ^ 2) - t / (1 + t ^ 2)
    rw [← mul_div_assoc, mul_one, ← mul_div_assoc, div_div, ← sq, Real.sq_sqrt hp]
    ring

/-- The Cayley point of real height t, oriented by the real-line parameter. -/
noncomputable def cayleyCircle (t : ℝ) : Circle :=
  Circle.exp (2 * Real.arctan t + Real.pi)

/-- The complex value of the real-height Cayley point is (1-I*t-2)/(1-I*t).
The explicit trigonometric identity connects the angular parametrization to zero moments. -/
theorem coe_cayleyCircle (t : ℝ) :
    (cayleyCircle t : ℂ) = ((1 : ℂ) - Complex.I * t - 2) / ((1 : ℂ) - Complex.I * t) :=
  cayley_circle_exp t

/-- The additive circle image of the real-height parameter equals its Cayley point.
Convert the period-one map to its circle exponential and simplify the angular coordinate. -/
theorem toCircle_cayleyParameter (t : ℝ) :
    AddCircle.toCircle (cayleyParameter t : AddCircle (1 : ℝ)) = cayleyCircle t := by
  rw [AddCircle.toCircle_apply_mk]
  simp only [div_one]
  rw [cayleyParameter_angle]
  rfl

/-- The uniform circle average equals real-line integration of the Cayley pullback
with weight 1/(pi*(1+t^2)). Substitute the explicit circle point in the parameter formula;
compactly supported tests use this identity to recover the kernel mass coefficient. -/
theorem circleAverage_cayleyCircle (f : C(Circle, ℂ)) :
    circleAverage f = ∫ t : ℝ, (1 / (Real.pi * (1 + t ^ 2))) • f (cayleyCircle t) := by
  rw [circleAverage_cayleyParameter]
  simp only [toCircle_cayleyParameter]

end PseudoPrime.Analysis

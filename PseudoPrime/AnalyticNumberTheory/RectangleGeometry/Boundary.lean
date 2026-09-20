/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import PseudoPrime.AnalyticNumberTheory.Rectangle.Basic
import PseudoPrime.AnalyticNumberTheory.General.PoleResidueCalculus

/-!
# Algebra of rectangular complex boundary integrals

This file isolates the geometric bookkeeping needed to subdivide rectangular contours.  Its
results are independent of the zeta kernels and can later support a finite rectangular grid whose
internal edges cancel.
-/

namespace PseudoPrime.AnalyticNumberTheory.RectangleGeometry

/-- The normalized arctangent integral needed for one edge of the unit centered square. -/
theorem integral_inv_one_add_sq_neg_one_one :
    (∫ x : ℝ in (-1)..1, (1 + x ^ 2)⁻¹) = Real.pi / 2 := by
  rw [integral_inv_one_add_sq, Real.arctan_neg, Real.arctan_one]
  ring

/-- The odd real part of the normalized simple-pole edge integral vanishes. -/
theorem integral_self_mul_inv_one_add_sq_neg_one_one :
    (∫ x : ℝ in (-1)..1, x * (1 + x ^ 2)⁻¹) = 0 := by
  let f : ℝ → ℝ := fun x ↦ x * (1 + x ^ 2)⁻¹
  have h := intervalIntegral.integral_comp_neg (f := f) (a := (-1 : ℝ)) (b := 1)
  have hodd : (fun x ↦ f (-x)) = fun x ↦ -f x := by
    funext x
    simp only [f, neg_mul, neg_sq]
  rw [hodd, intervalIntegral.integral_neg, neg_neg] at h
  change -(∫ x : ℝ in (-1)..1, x * (1 + x ^ 2)⁻¹) = ∫ x : ℝ in (-1)..1, x * (1 + x ^ 2)⁻¹ at h
  linarith

/-- The normalized lower-edge simple-pole integral is one quarter of `2πi`. -/
theorem integral_inv_sub_I_neg_one_one :
    (∫ x : ℝ in (-1)..1, ((x : ℂ) - Complex.I)⁻¹) = (Real.pi / 2 : ℂ) * Complex.I := by
  let g : ℝ → ℝ := fun x ↦ x * (1 + x ^ 2)⁻¹
  let h : ℝ → ℝ := fun x ↦ (1 + x ^ 2)⁻¹
  have hpoint (x : ℝ) : ((x : ℂ) - Complex.I)⁻¹ = (g x : ℂ) + (h x : ℂ) * Complex.I := by
    have hconj : (starRingEnd ℂ) ((x : ℂ) - Complex.I) = (x : ℂ) + Complex.I := by
      simp only [map_sub, Complex.conj_ofReal, Complex.conj_I, sub_neg_eq_add]
    have hnorm : Complex.normSq ((x : ℂ) - Complex.I) = 1 + x ^ 2 := by
      rw [Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.I_re, sub_zero, Complex.sub_im,
        Complex.ofReal_im, Complex.I_im, zero_sub, mul_neg, mul_one, neg_neg]
      ring
    rw [Complex.inv_def]
    rw [hconj, hnorm]
    dsimp only [g, h]
    push_cast
    ring
  rw [intervalIntegral.integral_congr fun x _ ↦ hpoint x]
  have hg : IntervalIntegrable (fun x : ℝ ↦ (g x : ℂ)) MeasureTheory.volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [g]
    exact
      RCLike.continuous_ofReal.comp
        (continuous_id.mul
          ((continuous_const.add (continuous_id.pow 2)).inv₀ fun x ↦ by
            change 1 + x ^ 2 ≠ 0
            nlinarith only [sq_nonneg x]))
  have hh : IntervalIntegrable (fun x : ℝ ↦ (h x : ℂ) * Complex.I) MeasureTheory.volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    dsimp only [h]
    exact
      (RCLike.continuous_ofReal.comp
            ((continuous_const.add (continuous_id.pow 2)).inv₀ fun x ↦ by
              change 1 + x ^ 2 ≠ 0
              nlinarith only [sq_nonneg x])).mul
        continuous_const
  rw [intervalIntegral.integral_add hg hh, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal]
  rw [show (∫ x : ℝ in (-1)..1, g x) = 0 by exact integral_self_mul_inv_one_add_sq_neg_one_one]
  rw [show (∫ x : ℝ in (-1)..1, h x) = Real.pi / 2 by exact integral_inv_one_add_sq_neg_one_one]
  simp only [Complex.ofReal_zero, Complex.ofReal_div, Complex.ofReal_ofNat, zero_add]

/-- The normalized upper-edge simple-pole integral is `-πi/2`. -/
theorem integral_inv_add_I_neg_one_one :
    (∫ x : ℝ in (-1)..1, ((x : ℂ) + Complex.I)⁻¹) = -((Real.pi / 2 : ℂ) * Complex.I) := by
  have hpoint (x : ℝ) : ((x : ℂ) + Complex.I)⁻¹ = -(((-x : ℝ) : ℂ) - Complex.I)⁻¹ := by
    rw [show (x : ℂ) + Complex.I = -(((-x : ℝ) : ℂ) - Complex.I)
        by
        push_cast
        ring]
    exact inv_neg
  rw [intervalIntegral.integral_congr fun x _ ↦ hpoint x]
  rw [intervalIntegral.integral_neg]
  change -(∫ x : ℝ in (-1)..1, (fun t : ℝ ↦ ((t : ℂ) - Complex.I)⁻¹) (-x)) = _
  have hcomp :
    (∫ x : ℝ in (-1)..1, (fun t : ℝ ↦ ((t : ℂ) - Complex.I)⁻¹) (-x)) =
      ∫ x : ℝ in (-1)..1, ((x : ℂ) - Complex.I)⁻¹ := by
    simpa only [neg_neg] using
      intervalIntegral.integral_comp_neg (f := fun t : ℝ ↦ ((t : ℂ) - Complex.I)⁻¹) (a := (-1 : ℝ))
        (b := 1)
  rw [hcomp]
  rw [integral_inv_sub_I_neg_one_one]

/-- The normalized right-edge integrand has integral `(-i)(πi/2)`. -/
theorem integral_inv_one_add_mul_I_neg_one_one :
    (∫ y : ℝ in (-1)..1, ((1 : ℂ) + y * Complex.I)⁻¹) =
      (-Complex.I) * ((Real.pi / 2 : ℂ) * Complex.I) := by
  have hpoint (y : ℝ) : ((1 : ℂ) + y * Complex.I)⁻¹ = (-Complex.I) * (((y : ℂ) - Complex.I)⁻¹) := by
    calc
      ((1 : ℂ) + y * Complex.I)⁻¹ = (Complex.I * ((y : ℂ) - Complex.I))⁻¹ := by
        congr 1
        rw [mul_sub, Complex.I_mul_I]
        ring
      _ = (((y : ℂ) - Complex.I)⁻¹) * Complex.I⁻¹ := by rw [mul_inv_rev]
      _ = (-Complex.I) * ((y : ℂ) - Complex.I)⁻¹ := by
        simp only [Complex.inv_I]
        ring
  rw [intervalIntegral.integral_congr fun y _ ↦ hpoint y]
  rw [intervalIntegral.integral_const_mul, integral_inv_sub_I_neg_one_one]

/-- The normalized left-edge integrand has integral `i(πi/2)`. -/
theorem integral_inv_neg_one_add_mul_I_neg_one_one :
    (∫ y : ℝ in (-1)..1, ((-1 : ℂ) + y * Complex.I)⁻¹) =
      Complex.I * ((Real.pi / 2 : ℂ) * Complex.I) := by
  have hpoint (y : ℝ) :
    ((-1 : ℂ) + y * Complex.I)⁻¹ = Complex.I * ((((-y : ℝ) : ℂ) - Complex.I)⁻¹) := by
    calc
      ((-1 : ℂ) + y * Complex.I)⁻¹ = ((-Complex.I) * (((-y : ℝ) : ℂ) - Complex.I))⁻¹ := by
        congr 1
        push_cast
        rw [neg_mul, mul_sub, Complex.I_mul_I]
        ring
      _ = ((((-y : ℝ) : ℂ) - Complex.I)⁻¹) * (-Complex.I)⁻¹ := by rw [mul_inv_rev]
      _ = Complex.I * ((((-y : ℝ) : ℂ) - Complex.I)⁻¹) := by
        simp only [inv_neg, Complex.inv_I, neg_neg]
        ring
  rw [intervalIntegral.integral_congr fun y _ ↦ hpoint y]
  rw [intervalIntegral.integral_const_mul]
  change Complex.I * (∫ y : ℝ in (-1)..1, (fun t : ℝ ↦ ((t : ℂ) - Complex.I)⁻¹) (-y)) = _
  have hcomp :
    (∫ y : ℝ in (-1)..1, (fun t : ℝ ↦ ((t : ℂ) - Complex.I)⁻¹) (-y)) =
      ∫ y : ℝ in (-1)..1, ((y : ℂ) - Complex.I)⁻¹ := by
    simpa only [neg_neg] using
      intervalIntegral.integral_comp_neg (f := fun t : ℝ ↦ ((t : ℂ) - Complex.I)⁻¹) (a := (-1 : ℝ))
        (b := 1)
  rw [hcomp]
  rw [integral_inv_sub_I_neg_one_one]

/-- Positive real scaling leaves the normalized lower-edge simple-pole integral unchanged. -/
theorem integral_inv_sub_mul_I_neg_radius_radius {r : ℝ} (hr : 0 < r) :
    (∫ x : ℝ in (-r)..r, ((x : ℂ) - r * Complex.I)⁻¹) = (Real.pi / 2 : ℂ) * Complex.I := by
  let edge : ℝ → ℂ := fun x ↦ ((x : ℂ) - Complex.I)⁻¹
  have hsubstitution :=
    intervalIntegral.smul_integral_comp_add_mul (f := fun x : ℝ ↦ ((x : ℂ) - r * Complex.I)⁻¹) (a :=
      (-1 : ℝ)) (b := 1) r 0
  simp only [zero_add, mul_neg, mul_one, sub_eq_add_neg] at hsubstitution
  simp only [← sub_eq_add_neg] at hsubstitution
  rw [← hsubstitution]
  simp only [Complex.ofReal_mul]
  have hpoint' (x : ℝ) : (↑r * (x : ℂ) - ↑r * Complex.I)⁻¹ = (r : ℂ)⁻¹ * edge x := by
    dsimp only [edge]
    rw [show (r : ℂ) * (x : ℂ) - (r : ℂ) * Complex.I = (r : ℂ) * ((x : ℂ) - Complex.I) by ring]
    rw [mul_inv_rev]
    ring
  rw [intervalIntegral.integral_congr fun x _ ↦ hpoint' x]
  rw [intervalIntegral.integral_const_mul, integral_inv_sub_I_neg_one_one]
  simp only [Complex.real_smul, ne_eq, Complex.ofReal_eq_zero, hr.ne', not_false_eq_true,
    mul_inv_cancel_left₀]

/-- Positive real scaling preserves the normalized upper-edge integral. -/
theorem integral_inv_add_mul_I_neg_radius_radius {r : ℝ} (hr : 0 < r) :
    (∫ x : ℝ in (-r)..r, ((x : ℂ) + r * Complex.I)⁻¹) = -((Real.pi / 2 : ℂ) * Complex.I) := by
  have hpoint (x : ℝ) : ((x : ℂ) + r * Complex.I)⁻¹ = -((((-x : ℝ) : ℂ) - r * Complex.I)⁻¹) := by
    rw [show (x : ℂ) + r * Complex.I = -((((-x : ℝ) : ℂ) - r * Complex.I)) by
        push_cast; ring]
    exact inv_neg
  rw [intervalIntegral.integral_congr fun x _ ↦ hpoint x]
  rw [intervalIntegral.integral_neg]
  have hcomp :
    (∫ x : ℝ in (-r)..r, (fun t : ℝ ↦ ((t : ℂ) - r * Complex.I)⁻¹) (-x)) =
      ∫ x : ℝ in (-r)..r, ((x : ℂ) - r * Complex.I)⁻¹ := by
    simpa only [neg_neg] using
      intervalIntegral.integral_comp_neg (f := fun t : ℝ ↦ ((t : ℂ) - r * Complex.I)⁻¹) (a := -r)
        (b := r)
  rw [hcomp, integral_inv_sub_mul_I_neg_radius_radius hr]

/-- Positive real scaling preserves the normalized right-edge integral. -/
theorem integral_inv_radius_add_mul_I_neg_radius_radius {r : ℝ} (hr : 0 < r) :
    (∫ y : ℝ in (-r)..r, ((r : ℂ) + y * Complex.I)⁻¹) =
      (-Complex.I) * ((Real.pi / 2 : ℂ) * Complex.I) := by
  have hpoint (y : ℝ) :
    ((r : ℂ) + y * Complex.I)⁻¹ = (-Complex.I) * (((y : ℂ) - r * Complex.I)⁻¹) := by
    calc
      ((r : ℂ) + y * Complex.I)⁻¹ = (Complex.I * ((y : ℂ) - r * Complex.I))⁻¹ := by
        congr 1
        ring_nf
        rw [Complex.I_sq]
        ring
      _ = (((y : ℂ) - r * Complex.I)⁻¹) * Complex.I⁻¹ := by rw [mul_inv_rev]
      _ = (-Complex.I) * ((y : ℂ) - r * Complex.I)⁻¹ := by
        simp only [Complex.inv_I]
        ring
  rw [intervalIntegral.integral_congr fun y _ ↦ hpoint y]
  rw [intervalIntegral.integral_const_mul, integral_inv_sub_mul_I_neg_radius_radius hr]

/-- Positive real scaling preserves the normalized left-edge integral. -/
theorem integral_inv_neg_radius_add_mul_I_neg_radius_radius {r : ℝ} (hr : 0 < r) :
    (∫ y : ℝ in (-r)..r, ((-r : ℝ) + y * Complex.I)⁻¹) =
      Complex.I * ((Real.pi / 2 : ℂ) * Complex.I) := by
  have hpoint (y : ℝ) :
    ((-r : ℝ) + y * Complex.I)⁻¹ = Complex.I * ((((-y : ℝ) : ℂ) - r * Complex.I)⁻¹) := by
    calc
      ((-r : ℝ) + y * Complex.I)⁻¹ = ((-Complex.I) * (((-y : ℝ) : ℂ) - r * Complex.I))⁻¹ := by
        congr 1
        push_cast
        ring_nf
        rw [Complex.I_sq]
        ring
      _ = ((((-y : ℝ) : ℂ) - r * Complex.I)⁻¹) * (-Complex.I)⁻¹ := by rw [mul_inv_rev]
      _ = Complex.I * ((((-y : ℝ) : ℂ) - r * Complex.I)⁻¹) := by
        simp only [inv_neg, Complex.inv_I, neg_neg]
        ring
  rw [intervalIntegral.integral_congr fun y _ ↦ hpoint y]
  rw [intervalIntegral.integral_const_mul]
  have hcomp :
    (∫ y : ℝ in (-r)..r, (fun t : ℝ ↦ ((t : ℂ) - r * Complex.I)⁻¹) (-y)) =
      ∫ y : ℝ in (-r)..r, ((y : ℂ) - r * Complex.I)⁻¹ := by
    simpa only [neg_neg] using
      intervalIntegral.integral_comp_neg (f := fun t : ℝ ↦ ((t : ℂ) - r * Complex.I)⁻¹) (a := -r)
        (b := r)
  rw [hcomp, integral_inv_sub_mul_I_neg_radius_radius hr]

/--
Integrating a shifted inverse square along a horizontal line gives its primitive's endpoint
difference, provided the line does not pass through the origin.
-/
theorem integral_inv_sq_add_mul_I (a b k : ℝ) (hk : k ≠ 0) :
    (∫ x : ℝ in a..b, (x + k * Complex.I)⁻¹ ^ 2) =
      -(b + k * Complex.I)⁻¹ - (-(a + k * Complex.I)⁻¹) := by
  have hne (x : ℝ) : (x : ℂ) + k * Complex.I ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    exact
      hk
        (by
          simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
            Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add,
            Complex.zero_im] using him)
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x _
    have hderiv := ((Complex.ofRealCLM.hasDerivAt.add_const (k * Complex.I)).inv (hne x)).neg
    convert hderiv using 1
    · funext y
      simp only [Complex.ofRealCLM_apply, Pi.neg_apply, Pi.inv_apply]
    · simp only [inv_pow, Complex.ofRealCLM_apply, Complex.ofReal_one, div_eq_mul_inv, neg_mul,
        one_mul, neg_neg]
  · exact ((Continuous.inv₀ (by fun_prop) hne).pow 2).intervalIntegrable a b

/--
The oriented vertical contribution of an inverse square is the same primitive endpoint difference.
The factor `I` is the derivative of the vertical parametrization.
-/
theorem I_smul_integral_inv_sq_add_mul_I (a b d : ℝ) (hd : d ≠ 0) :
    Complex.I • (∫ y : ℝ in a..b, (d + y * Complex.I)⁻¹ ^ 2) =
      -(d + b * Complex.I)⁻¹ - (-(d + a * Complex.I)⁻¹) := by
  have hne (y : ℝ) : (d : ℂ) + y * Complex.I ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    exact
      hd
        (by
          simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
            Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.zero_re] using
            hre)
  rw [smul_eq_mul, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro y _
    have hline := ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const Complex.I).const_add (d : ℂ)
    have hderiv := (hline.inv (hne y)).neg
    convert hderiv using 1
    · funext x
      simp only [Complex.ofRealCLM_apply, Pi.neg_apply, Pi.inv_apply]
    · simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, div_eq_mul_inv, inv_pow, neg_mul,
        one_mul, neg_neg]
  · exact (continuous_const.mul ((Continuous.inv₀ (by fun_prop) hne).pow 2)).intervalIntegrable a b

/--
Input/assumptions: a horizontal line avoiding the origin.
Conclusion: the inverse-cube integral is the endpoint difference of `-z⁻² / 2`.
Content: differentiate that elementary complex primitive along the real parametrization.
Role: evaluates horizontal triple-pole square edges without crossing the singular center.
-/
theorem integral_inv_cube_add_mul_I (a b k : ℝ) (hk : k ≠ 0) :
    (∫ x : ℝ in a..b, (x + k * Complex.I)⁻¹ ^ 3) =
      (-(b + k * Complex.I)⁻¹ ^ 2 / 2) - (-(a + k * Complex.I)⁻¹ ^ 2 / 2) := by
  have hne (x : ℝ) : (x : ℂ) + k * Complex.I ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    exact
      hk
        (by
          simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
            Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add,
            Complex.zero_im] using him)
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x _
    have hline := (Complex.ofRealCLM.hasDerivAt (x := x)).add_const (k * Complex.I)
    have hderiv :
      HasDerivAt (fun y : ℝ ↦ -(((y : ℂ) + k * Complex.I)⁻¹ ^ 2) / 2)
        (((x : ℂ) + k * Complex.I)⁻¹ ^ 3) x := by
      convert ((hline.inv (hne x)).pow 2).const_mul (-(1 / 2 : ℂ)) using 1
      · funext y
        simp only [Complex.ofRealCLM_apply, Pi.inv_apply, Pi.pow_apply, div_eq_mul_inv, pow_two]
        ring
      · change
          ((x : ℂ) + k * Complex.I)⁻¹ ^ 3 =
            -(1 / 2 : ℂ) *
              (2 * ((x : ℂ) + k * Complex.I)⁻¹ ^ (2 - 1) *
                (-(1 : ℂ) / ((x : ℂ) + k * Complex.I) ^ 2))
        norm_num only [Nat.reduceSub, pow_one]
        field_simp [hne x]
    exact hderiv
  · exact ((Continuous.inv₀ (by fun_prop) hne).pow 3).intervalIntegrable a b

/--
The oriented vertical contribution of an inverse cube is the endpoint difference of its primitive.
The factor `I` is the derivative of the vertical parametrization.
-/
theorem I_smul_integral_inv_cube_add_mul_I (a b d : ℝ) (hd : d ≠ 0) :
    Complex.I • (∫ y : ℝ in a..b, (d + y * Complex.I)⁻¹ ^ 3) =
      (-(d + b * Complex.I)⁻¹ ^ 2 / 2) - (-(d + a * Complex.I)⁻¹ ^ 2 / 2) := by
  have hne (y : ℝ) : (d : ℂ) + y * Complex.I ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    exact
      hd
        (by
          simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
            Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.zero_re] using
            hre)
  rw [smul_eq_mul, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro y _
    have hline := ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const Complex.I).const_add (d : ℂ)
    have hderiv :
      HasDerivAt (fun x : ℝ ↦ -((d + x * Complex.I)⁻¹ ^ 2) / 2)
        (Complex.I * ((d : ℂ) + y * Complex.I)⁻¹ ^ 3) y := by
      convert ((hline.inv (hne y)).pow 2).const_mul (-(1 / 2 : ℂ)) using 1
      · funext x
        simp only [Complex.ofRealCLM_apply, Pi.inv_apply, Pi.pow_apply, div_eq_mul_inv, pow_two]
        ring
      · simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, Pi.inv_apply, div_eq_mul_inv,
          inv_pow]
        norm_num only [Nat.reduceSub, pow_one]
        field_simp [hne y]
    exact hderiv
  · exact (continuous_const.mul ((Continuous.inv₀ (by fun_prop) hne).pow 3)).intervalIntegrable a b

/--
The open axis-aligned box strictly between the coordinates of two complex corners.

The real and imaginary coordinates use unordered endpoints, so the definition is independent of
corner orientation.  It represents cell interiors in the rectangular-grid separation layer.
-/
def rectangleOpenBox (z w : ℂ) : Set ℂ :=
  Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ Set.Ioo (min z.im w.im) (max z.im w.im)

/-- Every point of an open rectangle has a positive closed-ball neighborhood inside it. -/
theorem exists_closedBall_subset_rectangleOpenBox {z w s : ℂ} (hs : s ∈ rectangleOpenBox z w) :
    ∃ ε : ℝ, 0 < ε ∧ Metric.closedBall s ε ⊆ rectangleOpenBox z w := by
  have hopen : IsOpen (rectangleOpenBox z w) := isOpen_Ioo.reProdIm isOpen_Ioo
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hs)
  refine ⟨r / 2, half_pos hr, ?_⟩
  exact (Metric.closedBall_subset_ball (half_lt_self hr)).trans hball

/-- Finitely many positive closed-ball neighborhoods admit one common positive radius. -/
theorem Finset.exists_common_closedBall_subset {ι : Type*} (points : Finset ι) (center : ι → ℂ)
    (target : ι → Set ℂ)
    (hlocal : ∀ i ∈ points, ∃ ε : ℝ, 0 < ε ∧ Metric.closedBall (center i) ε ⊆ target i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ points, Metric.closedBall (center i) ε ⊆ target i := by
  classical
    induction points using Finset.induction with
  | empty =>
    exact
      ⟨1, by norm_num only, by simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true]⟩
  | @insert i points hi
    ih =>
    obtain ⟨εi, hεi, hballi⟩ := hlocal i (by simp only [Finset.mem_insert, true_or])
    obtain ⟨εs, hεs, hballs⟩ :=
      ih fun j hj ↦ hlocal j (by simp only [Finset.mem_insert, hj, or_true])
    refine ⟨min εi εs, lt_min hεi hεs, ?_⟩
    intro j hj y hy
    rcases Finset.mem_insert.mp hj with rfl | hj
    · apply hballi
      exact Metric.mem_closedBall.mpr ((Metric.mem_closedBall.mp hy).trans (min_le_left _ _))
    · apply hballs j hj
      exact Metric.mem_closedBall.mpr ((Metric.mem_closedBall.mp hy).trans (min_le_right _ _))

/-- Every open rectangular box is contained in its corresponding closed box. -/
theorem rectangleOpenBox_subset_rectangleClosedBox (z w : ℂ) :
    rectangleOpenBox z w ⊆ Rectangle.rectangleClosedBox z w := by
  intro s hs
  exact ⟨⟨le_of_lt hs.1.1, le_of_lt hs.1.2⟩, ⟨le_of_lt hs.2.1, le_of_lt hs.2.2⟩⟩

/--
A point of an ordered closed box lies in the open box when it avoids all four edge coordinates.

The endpoint order turns unordered intervals into ordinary closed intervals.  Endpoint avoidance
upgrades the two coordinatewise weak inequalities to strict ones.  This is the local bridge from
grid-line avoidance to open-cell membership.
-/
theorem mem_rectangleOpenBox_of_mem_closedBox_of_ne {a b s : ℂ} (hre : a.re < b.re)
    (him : a.im < b.im) (hs : s ∈ Rectangle.rectangleClosedBox a b) (hsare : s.re ≠ a.re)
    (hsbre : s.re ≠ b.re) (hsaim : s.im ≠ a.im) (hsbim : s.im ≠ b.im) :
    s ∈ rectangleOpenBox a b := by
  have hsre := hs.1
  have hsim := hs.2
  rw [Set.uIcc_of_lt hre] at hsre
  rw [Set.uIcc_of_lt him] at hsim
  change (min a.re b.re < s.re ∧ s.re < max a.re b.re) ∧ min a.im b.im < s.im ∧ s.im < max a.im b.im
  rw [min_eq_left (le_of_lt hre), max_eq_right (le_of_lt hre), min_eq_left (le_of_lt him),
    max_eq_right (le_of_lt him)]
  exact
    ⟨⟨lt_of_le_of_ne hsre.1 hsare.symm, lt_of_le_of_ne hsre.2 hsbre⟩,
      ⟨lt_of_le_of_ne hsim.1 hsaim.symm, lt_of_le_of_ne hsim.2 hsbim⟩⟩

/-- Real-coordinate separation makes two open rectangular boxes disjoint. -/
theorem rectangleOpenBox_disjoint_of_re_separated {a b c d : ℂ}
    (hsep : max a.re b.re ≤ min c.re d.re) :
    Disjoint (rectangleOpenBox a b) (rectangleOpenBox c d) := by
  apply Set.disjoint_left.mpr
  intro s hs ht
  have hcross : min c.re d.re < max a.re b.re := ht.1.1.trans hs.1.2
  exact (not_lt_of_ge hsep) hcross

/-- Imaginary-coordinate separation makes two open rectangular boxes disjoint. -/
theorem rectangleOpenBox_disjoint_of_im_separated {a b c d : ℂ}
    (hsep : max a.im b.im ≤ min c.im d.im) :
    Disjoint (rectangleOpenBox a b) (rectangleOpenBox c d) := by
  apply Set.disjoint_left.mpr
  intro s hs ht
  have hcross : min c.im d.im < max a.im b.im := ht.2.1.trans hs.2.2
  exact (not_lt_of_ge hsep) hcross

/-- Separation in either coordinate and either orientation makes open boxes disjoint. -/
theorem rectangleOpenBox_disjoint_of_coordinate_separated {a b c d : ℂ}
    (hsep :
      max a.re b.re ≤ min c.re d.re ∨
        max c.re d.re ≤ min a.re b.re ∨
        max a.im b.im ≤ min c.im d.im ∨ max c.im d.im ≤ min a.im b.im) :
    Disjoint (rectangleOpenBox a b) (rectangleOpenBox c d) := by
  rcases hsep with hre | hre | him | him
  · exact rectangleOpenBox_disjoint_of_re_separated hre
  · exact (rectangleOpenBox_disjoint_of_re_separated hre).symm
  · exact rectangleOpenBox_disjoint_of_im_separated him
  · exact (rectangleOpenBox_disjoint_of_im_separated him).symm

/-- A nonempty real open interval contains a point outside any prescribed finite set. -/
theorem exists_between_not_mem_finset (forbidden : Finset ℝ) {a b : ℝ} (hab : a < b) :
    ∃ x : ℝ, a < x ∧ x < b ∧ x ∉ forbidden := by
  have hinfinite : (Set.Ioo a b).Infinite := Set.Ioo_infinite hab
  by_contra hnot
  push Not at hnot
  have hsubset : Set.Ioo a b ⊆ (forbidden : Set ℝ) := fun x hx ↦ hnot x hx.1 hx.2
  exact (hinfinite.mono hsubset) forbidden.finite_toSet

/--
Choose a point strictly between two reals while avoiding a finite forbidden set.

When the endpoints are ordered,
`PseudoPrime.AnalyticNumberTheory.RectangleGeometry.avoidingCut_spec` proves the defining
inequalities and avoidance.
The unconstrained value for unordered endpoints is irrelevant to callers, which filter ordered
pairs before constructing finite cut candidates.
-/
noncomputable def avoidingCut (forbidden : Finset ℝ) (a b : ℝ) : ℝ :=
  Classical.epsilon fun x ↦ a < x ∧ x < b ∧ x ∉ forbidden

/-- An avoiding cut between ordered endpoints satisfies its inequalities and finite avoidance. -/
theorem avoidingCut_spec (forbidden : Finset ℝ) {a b : ℝ} (hab : a < b) :
    a < avoidingCut forbidden a b ∧
      avoidingCut forbidden a b < b ∧ avoidingCut forbidden a b ∉ forbidden := by
  exact Classical.epsilon_spec (exists_between_not_mem_finset forbidden hab)

/-- The first defining corner belongs to its closed rectangular box. -/
theorem left_mem_rectangleClosedBox (z w : ℂ) : z ∈ Rectangle.rectangleClosedBox z w := by
  exact ⟨Set.left_mem_uIcc, Set.left_mem_uIcc⟩

/-- The second defining corner belongs to its closed rectangular box. -/
theorem right_mem_rectangleClosedBox (z w : ℂ) : w ∈ Rectangle.rectangleClosedBox z w := by
  exact ⟨Set.right_mem_uIcc, Set.right_mem_uIcc⟩

/--
Endpoint containment in each coordinate implies containment of closed rectangular boxes.

This orientation-free formulation uses unordered intervals, so it applies equally to increasing
and decreasing contour coordinates.  It is the basic geometric lemma for proving that every grid
cell remains inside its outer rectangle.
-/
theorem rectangleClosedBox_subset_rectangleClosedBox {a b z w : ℂ}
    (hare : a.re ∈ Set.uIcc z.re w.re) (hbre : b.re ∈ Set.uIcc z.re w.re)
    (haim : a.im ∈ Set.uIcc z.im w.im) (hbim : b.im ∈ Set.uIcc z.im w.im) :
    Rectangle.rectangleClosedBox a b ⊆ Rectangle.rectangleClosedBox z w := by
  intro s hs
  exact ⟨Set.uIcc_subset_uIcc hare hbre hs.1, Set.uIcc_subset_uIcc haim hbim hs.2⟩

/-- The first component of a consecutive pair occurs in the original list. -/
theorem List.fst_mem_of_mem_consecutivePairs {A : Type*} {values : List A} {pair : A × A}
    (hpair : pair ∈ values.consecutivePairs) : pair.1 ∈ values := by
  induction values with
  | nil =>
    change pair ∈ [] at hpair
    simp only [List.not_mem_nil] at hpair
  | cons a values ih =>
    cases values with
    | nil =>
      change pair ∈ [] at hpair
      simp only [List.not_mem_nil] at hpair
    | cons b
      values =>
      simp only [List.consecutivePairs, List.tail_cons, List.zip_cons_cons, List.mem_cons] at hpair
      rcases hpair with rfl | hpair
      · simp only [List.mem_cons, eq_self, true_or]
      · exact List.mem_cons_of_mem a (ih hpair)

/-- The second component of a consecutive pair occurs in the original list. -/
theorem List.snd_mem_of_mem_consecutivePairs {A : Type*} {values : List A} {pair : A × A}
    (hpair : pair ∈ values.consecutivePairs) : pair.2 ∈ values := by
  induction values with
  | nil =>
    change pair ∈ [] at hpair
    simp only [List.not_mem_nil] at hpair
  | cons a values ih =>
    cases values with
    | nil =>
      change pair ∈ [] at hpair
      simp only [List.not_mem_nil] at hpair
    | cons b
      values =>
      simp only [List.consecutivePairs, List.tail_cons, List.zip_cons_cons, List.mem_cons] at hpair
      rcases hpair with rfl | hpair
      · simp only [List.mem_cons, eq_self, or_true, true_or]
      · exact List.mem_cons_of_mem a (ih hpair)

/-- A consecutive pair inherits the relation from a pairwise-related source list. -/
theorem List.rel_of_mem_consecutivePairs {A : Type*} {R : A → A → Prop} {values : List A}
    (hvalues : values.Pairwise R) {pair : A × A} (hpair : pair ∈ values.consecutivePairs) :
    R pair.1 pair.2 := by
  induction values with
  | nil =>
    change pair ∈ [] at hpair
    simp only [List.not_mem_nil] at hpair
  | cons a values ih =>
    cases values with
    | nil =>
      change pair ∈ [] at hpair
      simp only [List.not_mem_nil] at hpair
    | cons b
      values =>
      simp only [List.consecutivePairs, List.tail_cons, List.zip_cons_cons, List.mem_cons] at hpair
      rcases hpair with rfl | hpair
      · exact (List.pairwise_cons.mp hvalues).1 b (List.mem_cons_self)
      · exact ih (List.pairwise_cons.mp hvalues).2 hpair

/-- Two real coordinate intervals are separated when either one ends before the other starts. -/
def coordinateIntervalsSeparated (p q : ℝ × ℝ) : Prop :=
  p.2 ≤ q.1 ∨ q.2 ≤ p.1

/-- Coordinate-interval separation is symmetric. -/
instance : Std.Symm coordinateIntervalsSeparated :=
  ⟨fun _ _ h ↦ h.elim Or.inr Or.inl⟩

/-- Consecutive intervals of a strictly increasing list occur in nonoverlapping order. -/
theorem List.consecutivePairs_pairwise_separated {values : List ℝ}
    (hvalues : values.Pairwise (· < ·)) : values.consecutivePairs.Pairwise fun p q ↦ p.2 ≤ q.1 := by
  induction values with
  | nil => exact List.Pairwise.nil
  | cons a values ih =>
    cases values with
    | nil => exact List.Pairwise.nil
    | cons b values =>
      have htail := (List.pairwise_cons.mp hvalues).2
      simp only [List.consecutivePairs, List.tail_cons, List.zip_cons_cons, List.pairwise_cons]
      refine ⟨?_, ih htail⟩
      intro pair hpair
      rcases List.mem_cons.mp (List.fst_mem_of_mem_consecutivePairs hpair) with h | h
      · exact h ▸ le_rfl
      · exact le_of_lt ((List.pairwise_cons.mp htail).1 pair.1 h)

/-- Two distinct consecutive intervals of a strictly increasing list are separated. -/
theorem List.consecutivePairs_separated {values : List ℝ} (hvalues : values.Pairwise (· < ·))
    {p q : ℝ × ℝ} (hp : p ∈ values.consecutivePairs) (hq : q ∈ values.consecutivePairs)
    (hne : p ≠ q) : coordinateIntervalsSeparated p q := by
  have hpairs := List.consecutivePairs_pairwise_separated hvalues
  have hsymmetric : values.consecutivePairs.Pairwise coordinateIntervalsSeparated :=
    hpairs.imp fun hab ↦ Or.inl hab
  exact hsymmetric.forall hp hq hne

/-- No source-list coordinate lies strictly inside one of its consecutive intervals. -/
theorem List.not_between_of_mem_consecutivePairs {values : List ℝ}
    (hvalues : values.Pairwise (· < ·)) {pair : ℝ × ℝ} (hpair : pair ∈ values.consecutivePairs)
    {u : ℝ} (hu : u ∈ values) : ¬(pair.1 < u ∧ u < pair.2) := by
  induction values with
  | nil => simp only [List.not_mem_nil] at hu
  | cons a values ih =>
    cases values with
    | nil =>
      change pair ∈ [] at hpair
      simp only [List.not_mem_nil] at hpair
    | cons b values =>
      have htail := (List.pairwise_cons.mp hvalues).2
      simp only [List.consecutivePairs, List.tail_cons, List.zip_cons_cons, List.mem_cons] at hpair
      rcases hpair with rfl | hpair
      · intro hbetween
        rcases List.mem_cons.mp hu with rfl | hu
        · exact (lt_irrefl _) hbetween.1
        · rcases List.mem_cons.mp hu with rfl | hu
          · exact (lt_irrefl _) hbetween.2
          · exact (not_lt_of_ge (le_of_lt ((List.pairwise_cons.mp htail).1 u hu))) hbetween.2
      · rcases List.mem_cons.mp hu with rfl | hu
        · intro hbetween
          have hfirst := List.fst_mem_of_mem_consecutivePairs hpair
          exact
            (not_lt_of_ge (le_of_lt ((List.pairwise_cons.mp hvalues).1 pair.1 hfirst))) hbetween.1
        · exact ih htail hpair hu

/-- Consecutive pairs of a duplicate-free list are duplicate-free. -/
theorem List.Nodup.consecutivePairs {A : Type*} {values : List A} (hvalues : values.Nodup) :
    values.consecutivePairs.Nodup := by
  induction values with
  | nil =>
    change ([] : List (A × A)).Nodup
    exact List.nodup_nil
  | cons a values ih =>
    cases values with
    | nil =>
      change ([] : List (A × A)).Nodup
      exact List.nodup_nil
    | cons b values =>
      rw [List.nodup_cons] at hvalues
      simp only [List.consecutivePairs, List.tail_cons, List.zip_cons_cons]
      rw [List.nodup_cons]
      refine ⟨?_, ih hvalues.2⟩
      intro hpair
      exact hvalues.1 (List.fst_mem_of_mem_consecutivePairs hpair)

/--
The oriented boundary integral around an axis-aligned rectangle with opposite corners `z` and `w`.
It is counterclockwise when both coordinates increase from `z` to `w`.

The four interval integrals use the same orientation as mathlib's rectangular Cauchy--Goursat
theorem.  This definition is the generic geometric layer reused by downstream zeta kernels.
-/
noncomputable def rectangleBoundaryIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * Complex.I)) -
        (∫ x : ℝ in z.re..w.re, f (x + w.im * Complex.I)) +
      Complex.I • (∫ y : ℝ in z.im..w.im, f (w.re + y * Complex.I)) -
    Complex.I • (∫ y : ℝ in z.im..w.im, f (z.re + y * Complex.I))

/--
Integrability of a function along all four oriented edges used by
`PseudoPrime.AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral`.

The certificate is deliberately local to one rectangle.  It supplies exactly the hypotheses needed
for linearity of interval integrals, and will combine principal parts with regular remainders.
-/
structure RectangleBoundaryIntegrable (f : ℂ → ℂ) (z w : ℂ) : Prop where
  bottom : IntervalIntegrable (fun x : ℝ ↦ f (x + z.im * Complex.I)) MeasureTheory.volume z.re w.re
  top : IntervalIntegrable (fun x : ℝ ↦ f (x + w.im * Complex.I)) MeasureTheory.volume z.re w.re
  right : IntervalIntegrable (fun y : ℝ ↦ f (w.re + y * Complex.I)) MeasureTheory.volume z.im w.im
  left : IntervalIntegrable (fun y : ℝ ↦ f (z.re + y * Complex.I)) MeasureTheory.volume z.im w.im

/-- Edge integrability is preserved by pointwise addition. -/
theorem RectangleBoundaryIntegrable.add {f g : ℂ → ℂ} {z w : ℂ}
    (hf : RectangleBoundaryIntegrable f z w) (hg : RectangleBoundaryIntegrable g z w) :
    RectangleBoundaryIntegrable (fun s : ℂ ↦ f s + g s) z w :=
  ⟨hf.bottom.add hg.bottom, hf.top.add hg.top, hf.right.add hg.right, hf.left.add hg.left⟩

/-- Edge integrability is preserved by multiplication by a complex constant. -/
theorem RectangleBoundaryIntegrable.const_mul {f : ℂ → ℂ} {z w : ℂ}
    (hf : RectangleBoundaryIntegrable f z w) (a : ℂ) :
    RectangleBoundaryIntegrable (fun s : ℂ ↦ a * f s) z w :=
  ⟨hf.bottom.const_mul a, hf.top.const_mul a, hf.right.const_mul a, hf.left.const_mul a⟩

/-- Boundary integration is additive when both summands are integrable on all four edges. -/
theorem rectangleBoundaryIntegral_add {f g : ℂ → ℂ} {z w : ℂ}
    (hf : RectangleBoundaryIntegrable f z w) (hg : RectangleBoundaryIntegrable g z w) :
    rectangleBoundaryIntegral (fun s : ℂ ↦ f s + g s) z w =
      rectangleBoundaryIntegral f z w + rectangleBoundaryIntegral g z w := by
  unfold rectangleBoundaryIntegral
  rw [intervalIntegral.integral_add hf.bottom hg.bottom,
    intervalIntegral.integral_add hf.top hg.top, intervalIntegral.integral_add hf.right hg.right,
    intervalIntegral.integral_add hf.left hg.left]
  module

/-- A complex scalar can be pulled through a rectangle boundary integral. -/
theorem rectangleBoundaryIntegral_const_mul (a : ℂ) (f : ℂ → ℂ) (z w : ℂ) :
    rectangleBoundaryIntegral (fun s : ℂ ↦ a * f s) z w = a * rectangleBoundaryIntegral f z w := by
  unfold rectangleBoundaryIntegral
  simp only [intervalIntegral.integral_const_mul, smul_eq_mul]
  ring

/-- Functions agreeing on a closed rectangle have equal boundary integrals. -/
theorem rectangleBoundaryIntegral_congr_closedBox {f g : ℂ → ℂ} {z w : ℂ}
    (hfg : Set.EqOn f g (Rectangle.rectangleClosedBox z w)) :
    rectangleBoundaryIntegral f z w = rectangleBoundaryIntegral g z w := by
  unfold rectangleBoundaryIntegral
  have horizontal (c : ℝ) (hc : c ∈ Set.uIcc z.im w.im) :
    (∫ t : ℝ in z.re..w.re, f (t + c * Complex.I)) =
      ∫ t : ℝ in z.re..w.re, g (t + c * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro t ht
    apply hfg
    constructor
    · simpa only [Set.mem_preimage, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] using ht
    · simpa only [Set.mem_preimage, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] using
        hc
  have vertical (c : ℝ) (hc : c ∈ Set.uIcc z.re w.re) :
    (∫ t : ℝ in z.im..w.im, f (c + t * Complex.I)) =
      ∫ t : ℝ in z.im..w.im, g (c + t * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro t ht
    apply hfg
    constructor
    · simpa only [Set.mem_preimage, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] using hc
    · simpa only [Set.mem_preimage, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] using
        ht
  rw [horizontal z.im Set.left_mem_uIcc, horizontal w.im Set.right_mem_uIcc,
    vertical w.re Set.right_mem_uIcc, vertical z.re Set.left_mem_uIcc]

/-- An unordered pair's left endpoint never lies strictly inside its own min-max interval. -/
theorem not_mem_Ioo_min_max_self_left (a b : ℝ) : a ∉ Set.Ioo (min a b) (max a b) := by
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab]
    simp only [Set.mem_Ioo, lt_self_iff_false, lt_max_iff, false_or, false_and, not_false_eq_true]
  · rw [max_eq_left hab]
    simp only [Set.mem_Ioo, min_lt_iff, lt_self_iff_false, false_or, and_false, not_false_eq_true]

/-- An unordered pair's right endpoint never lies strictly inside its own min-max interval. -/
theorem not_mem_Ioo_min_max_self_right (a b : ℝ) : b ∉ Set.Ioo (min a b) (max a b) := by
  rcases le_total a b with hab | hab
  · rw [max_eq_right hab]
    simp only [Set.mem_Ioo, min_lt_iff, lt_self_iff_false, or_false, and_false, not_false_eq_true]
  · rw [min_eq_right hab]
    simp only [Set.mem_Ioo, lt_self_iff_false, lt_max_iff, or_false, false_and, not_false_eq_true]

/-- A point on a fixed-imaginary-part edge never lies in the open rectangle. -/
theorem not_mem_rectangleOpenBox_of_im_eq {z w : ℂ} {c : ℝ} (hedge : c = z.im ∨ c = w.im) (t : ℝ) :
    ((t : ℂ) + c * Complex.I) ∉ rectangleOpenBox z w := by
  rw [rectangleOpenBox, Complex.mem_reProdIm]
  rintro ⟨-, him⟩
  have him' : ((t : ℂ) + (c : ℂ) * Complex.I).im = c := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
  rw [him'] at him
  rcases hedge with rfl | rfl
  · exact not_mem_Ioo_min_max_self_left z.im w.im him
  · exact not_mem_Ioo_min_max_self_right z.im w.im him

/-- A point on a fixed-real-part edge never lies in the open rectangle. -/
theorem not_mem_rectangleOpenBox_of_re_eq {z w : ℂ} {c : ℝ} (hedge : c = z.re ∨ c = w.re) (t : ℝ) :
    ((c : ℂ) + t * Complex.I) ∉ rectangleOpenBox z w := by
  rw [rectangleOpenBox, Complex.mem_reProdIm]
  rintro ⟨hre, -⟩
  have hre' : ((c : ℂ) + (t : ℂ) * Complex.I).re = c := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  rw [hre'] at hre
  rcases hedge with rfl | rfl
  · exact not_mem_Ioo_min_max_self_left z.re w.re hre
  · exact not_mem_Ioo_min_max_self_right z.re w.re hre

/--
Functions agreeing on a rectangle's boundary have equal boundary integrals.

This is the minimal hypothesis the four edge integrals actually consume: the closed-box congruence
`PseudoPrime.AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral_congr_closedBox`
additionally demands agreement on the open interior,
which a Laurent decomposition centered at an interior singularity cannot supply at the center
itself under Lean's junk-value convention for `(z - c)⁻¹`.
-/
theorem rectangleBoundaryIntegral_congr_boundary {f g : ℂ → ℂ} {z w : ℂ}
    (hfg : Set.EqOn f g (Rectangle.rectangleClosedBox z w \ rectangleOpenBox z w)) :
    rectangleBoundaryIntegral f z w = rectangleBoundaryIntegral g z w := by
  unfold rectangleBoundaryIntegral
  have horizontal (c : ℝ) (hc : c ∈ Set.uIcc z.im w.im) (hedge : c = z.im ∨ c = w.im) :
    (∫ t : ℝ in z.re..w.re, f (t + c * Complex.I)) =
      ∫ t : ℝ in z.re..w.re, g (t + c * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro t ht
    apply hfg
    refine ⟨⟨?_, ?_⟩, not_mem_rectangleOpenBox_of_im_eq hedge t⟩
    · simpa only [Set.mem_preimage, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] using ht
    · simpa only [Set.mem_preimage, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] using
        hc
  have vertical (c : ℝ) (hc : c ∈ Set.uIcc z.re w.re) (hedge : c = z.re ∨ c = w.re) :
    (∫ t : ℝ in z.im..w.im, f (c + t * Complex.I)) =
      ∫ t : ℝ in z.im..w.im, g (c + t * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro t ht
    apply hfg
    refine ⟨⟨?_, ?_⟩, not_mem_rectangleOpenBox_of_re_eq hedge t⟩
    · simpa only [Set.mem_preimage, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] using hc
    · simpa only [Set.mem_preimage, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] using
        ht
  rw [horizontal z.im Set.left_mem_uIcc (Or.inl rfl),
    horizontal w.im Set.right_mem_uIcc (Or.inr rfl), vertical w.re Set.right_mem_uIcc (Or.inr rfl),
    vertical z.re Set.left_mem_uIcc (Or.inl rfl)]

/-- A function differentiable on the closed rectangle has zero rectangle boundary integral. -/
theorem rectangleBoundaryIntegral_eq_zero_of_differentiableOn (f : ℂ → ℂ) (z w : ℂ)
    (hf : DifferentiableOn ℂ f (Rectangle.rectangleClosedBox z w)) :
    rectangleBoundaryIntegral f z w = 0 := by
  unfold rectangleBoundaryIntegral Rectangle.rectangleClosedBox at *
  exact Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w hf

/--
Translating both corners and translating the integrand by the same complex number preserves the
rectangle boundary integral.

Each of the four real interval integrals is translated by the corresponding real or imaginary
coordinate of `c`.  This is the reusable bridge from origin-centered model kernels to local
principal parts at an arbitrary center.
-/
theorem rectangleBoundaryIntegral_comp_sub_translate (f : ℂ → ℂ) (c z w : ℂ) :
    rectangleBoundaryIntegral (fun s : ℂ ↦ f (s - c)) (c + z) (c + w) =
      rectangleBoundaryIntegral f z w := by
  unfold rectangleBoundaryIntegral
  simp only [Complex.add_re, Complex.add_im]
  push_cast
  have hedge (a b d : ℝ) :
    (∫ x : ℝ in c.re + a..c.re + b, f (x + (c.im + d) * Complex.I - c)) =
      ∫ x : ℝ in a..b, f (x + d * Complex.I) := by
    rw [← intervalIntegral.integral_comp_add_left]
    apply intervalIntegral.integral_congr
    intro x _
    apply congrArg f
    apply Complex.ext <;>
      simp only [Complex.ofReal_add, Complex.sub_re, Complex.sub_im, Complex.add_re,
        Complex.ofReal_re, Complex.mul_re, Complex.mul_im, Complex.I_re, mul_zero, Complex.add_im,
        Complex.ofReal_im, add_zero, Complex.I_im, mul_one, sub_self, add_sub_cancel_left]
    all_goals ring_nf
  have vedge (a b d : ℝ) :
    (∫ y : ℝ in c.im + a..c.im + b, f ((c.re + d) + y * Complex.I - c)) =
      ∫ y : ℝ in a..b, f (d + y * Complex.I) := by
    rw [← intervalIntegral.integral_comp_add_left]
    apply intervalIntegral.integral_congr
    intro y _
    apply congrArg f
    apply Complex.ext <;>
      simp only [Complex.ofReal_add, Complex.sub_im, Complex.sub_re, Complex.add_im,
        Complex.ofReal_im, add_zero, Complex.mul_im, Complex.mul_re, Complex.add_re,
        Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, zero_add,
        add_sub_cancel_left]
    all_goals ring_nf
  rw [hedge z.re w.re z.im, hedge z.re w.re w.im, vedge z.im w.im w.re, vedge z.im w.im z.re]

/-- The centered simple-pole square integral is radius-independent for every positive radius. -/
theorem rectangleBoundaryIntegral_inv_zero_centeredSquare {r : ℝ} (hr : 0 < r) :
    rectangleBoundaryIntegral (fun z : ℂ ↦ z⁻¹) ((-r : ℝ) - r * Complex.I) (r + r * Complex.I) =
      2 * Real.pi * Complex.I := by
  unfold rectangleBoundaryIntegral
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
    mul_one, sub_zero, zero_sub, add_zero, zero_add, smul_eq_mul]
  have hbottom :
    (∫ x : ℝ in (-r)..r, (↑x + ↑(-r) * Complex.I)⁻¹) = (Real.pi / 2 : ℂ) * Complex.I := by
    rw [intervalIntegral.integral_congr fun x _ ↦
        show (↑x + ↑(-r) * Complex.I)⁻¹ = (↑x - ↑r * Complex.I)⁻¹
          by
          congr 1
          push_cast
          ring]
    exact integral_inv_sub_mul_I_neg_radius_radius hr
  rw [hbottom, integral_inv_add_mul_I_neg_radius_radius hr,
    integral_inv_radius_add_mul_I_neg_radius_radius hr,
    integral_inv_neg_radius_add_mul_I_neg_radius_radius hr]
  ring_nf
  rw [Complex.I_pow_three]
  ring

/--
The inverse-square principal part has zero boundary integral on every positive-radius square
centered at the origin.

On each edge the integrand is the derivative of the restriction of `-z⁻¹`.  The four primitive
endpoint differences cancel at the corners, without invoking a residue theorem across the singular
center.
-/
theorem rectangleBoundaryIntegral_inv_sq_zero_centeredSquare {r : ℝ} (hr : 0 < r) :
    rectangleBoundaryIntegral (fun z : ℂ ↦ z⁻¹ ^ 2) ((-r : ℝ) - r * Complex.I) (r + r * Complex.I) =
      0 := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  unfold rectangleBoundaryIntegral
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
    mul_one, sub_zero, zero_sub, add_zero, zero_add]
  rw [integral_inv_sq_add_mul_I (-r) r (-r) (neg_ne_zero.mpr hr0),
    integral_inv_sq_add_mul_I (-r) r r hr0, I_smul_integral_inv_sq_add_mul_I (-r) r r hr0,
    I_smul_integral_inv_sq_add_mul_I (-r) r (-r) (neg_ne_zero.mpr hr0)]
  ring

/--
The inverse-cube principal part has zero boundary integral on every positive-radius square
centered at the origin.  The four values of the primitive `-z⁻² / 2` cancel at the corners.
-/
theorem rectangleBoundaryIntegral_inv_cube_zero_centeredSquare {r : ℝ} (hr : 0 < r) :
    rectangleBoundaryIntegral (fun z : ℂ ↦ z⁻¹ ^ 3) ((-r : ℝ) - r * Complex.I) (r + r * Complex.I) =
      0 := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  unfold rectangleBoundaryIntegral
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
    mul_one, sub_zero, zero_sub, add_zero, zero_add]
  rw [integral_inv_cube_add_mul_I (-r) r (-r) (neg_ne_zero.mpr hr0),
    integral_inv_cube_add_mul_I (-r) r r hr0, I_smul_integral_inv_cube_add_mul_I (-r) r r hr0,
    I_smul_integral_inv_cube_add_mul_I (-r) r (-r) (neg_ne_zero.mpr hr0)]
  ring

/--
Splitting a rectangle at a real coordinate adds the two boundary integrals.

The hypotheses provide interval integrability on the two pieces of the lower and upper horizontal
edges.  The new vertical edge occurs with opposite orientations and cancels algebraically.  This is
the first subdivision certificate used by the punctured-contour construction.
-/
theorem rectangleBoundaryIntegral_eq_add_vertical (f : ℂ → ℂ) (z w : ℂ) (m : ℝ)
    (hbottomLeft :
      IntervalIntegrable (fun x : ℝ ↦ f (x + z.im * Complex.I)) MeasureTheory.volume z.re m)
    (hbottomRight :
      IntervalIntegrable (fun x : ℝ ↦ f (x + z.im * Complex.I)) MeasureTheory.volume m w.re)
    (htopLeft :
      IntervalIntegrable (fun x : ℝ ↦ f (x + w.im * Complex.I)) MeasureTheory.volume z.re m)
    (htopRight :
      IntervalIntegrable (fun x : ℝ ↦ f (x + w.im * Complex.I)) MeasureTheory.volume m w.re) :
    rectangleBoundaryIntegral f z w =
      rectangleBoundaryIntegral f z (m + w.im * Complex.I) +
        rectangleBoundaryIntegral f (m + z.im * Complex.I) w := by
  unfold rectangleBoundaryIntegral
  rw [← intervalIntegral.integral_add_adjacent_intervals hbottomLeft hbottomRight]
  rw [← intervalIntegral.integral_add_adjacent_intervals htopLeft htopRight]
  have hmw_re : ((m : ℂ) + (w.im : ℂ) * Complex.I).re = m := by
    calc
      ((m : ℂ) + (w.im : ℂ) * Complex.I).re =
          (m : ℂ).re + ((w.im : ℂ).re * 0 - (w.im : ℂ).im * 1) :=
        by rw [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
      _ = m + (w.im * 0 - 0 * 1) := by
        rw [Complex.ofReal_re]
        rw [Complex.ofReal_re]
        rw [Complex.ofReal_im]
      _ = m := by ring
  have hmw_im : ((m : ℂ) + (w.im : ℂ) * Complex.I).im = w.im := by
    rw [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
      Complex.I_im]
    ring
  have hmz_re : ((m : ℂ) + (z.im : ℂ) * Complex.I).re = m := by
    rw [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
      Complex.I_im]
    ring
  have hmz_im : ((m : ℂ) + (z.im : ℂ) * Complex.I).im = z.im := by
    rw [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
      Complex.I_im]
    ring
  have hreal (a : ℝ) :
    (fun x : ℝ => f (x + (a : ℂ) * Complex.I)) = (fun x : ℝ => f ((a : ℂ) * Complex.I + x)) := by
    funext x
    congr 1
    rw [add_comm]
  have himag (a : ℝ) :
    (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * Complex.I)) =
      (fun y : ℝ => f ((a : ℂ) + Complex.I * (y : ℂ))) := by
    funext y
    congr 1
    rw [mul_comm]
  rw [hmw_re, hmw_im, hmz_re, hmz_im]
  rw [hreal z.im, hreal w.im, himag z.re, himag w.re]
  ring_nf

/--
Splitting a rectangle at an imaginary coordinate adds the two boundary integrals.

The hypotheses provide interval integrability on the two pieces of the left and right vertical
edges.  The new horizontal edge occurs with opposite orientations and cancels algebraically.  With
`PseudoPrime.AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral_eq_add_vertical`,
this supplies both generators of rectangular-grid subdivision.
-/
theorem rectangleBoundaryIntegral_eq_add_horizontal (f : ℂ → ℂ) (z w : ℂ) (m : ℝ)
    (hrightBottom :
      IntervalIntegrable (fun y : ℝ ↦ f (w.re + y * Complex.I)) MeasureTheory.volume z.im m)
    (hrightTop :
      IntervalIntegrable (fun y : ℝ ↦ f (w.re + y * Complex.I)) MeasureTheory.volume m w.im)
    (hleftBottom :
      IntervalIntegrable (fun y : ℝ ↦ f (z.re + y * Complex.I)) MeasureTheory.volume z.im m)
    (hleftTop :
      IntervalIntegrable (fun y : ℝ ↦ f (z.re + y * Complex.I)) MeasureTheory.volume m w.im) :
    rectangleBoundaryIntegral f z w =
      rectangleBoundaryIntegral f z (w.re + m * Complex.I) +
        rectangleBoundaryIntegral f (z.re + m * Complex.I) w := by
  unfold rectangleBoundaryIntegral
  rw [← intervalIntegral.integral_add_adjacent_intervals hrightBottom hrightTop]
  rw [← intervalIntegral.integral_add_adjacent_intervals hleftBottom hleftTop]
  have hwm_re : ((w.re : ℂ) + (m : ℂ) * Complex.I).re = w.re := by
    rw [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
      Complex.I_im]
    ring
  have hwm_im : ((w.re : ℂ) + (m : ℂ) * Complex.I).im = m := by
    rw [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
      Complex.I_im]
    ring
  have hzm_re : ((z.re : ℂ) + (m : ℂ) * Complex.I).re = z.re := by
    rw [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
      Complex.I_im]
    ring
  have hzm_im : ((z.re : ℂ) + (m : ℂ) * Complex.I).im = m := by
    rw [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
      Complex.I_im]
    ring
  have hreal (a : ℝ) :
    (fun x : ℝ => f (x + (a : ℂ) * Complex.I)) = (fun x : ℝ => f ((a : ℂ) * Complex.I + x)) := by
    funext x
    congr 1
    rw [add_comm]
  have himag (a : ℝ) :
    (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * Complex.I)) =
      (fun y : ℝ => f ((a : ℂ) + Complex.I * (y : ℂ))) := by
    funext y
    congr 1
    rw [mul_comm]
  rw [hwm_re, hwm_im, hzm_re, hzm_im]
  rw [hreal z.im, hreal w.im, himag z.re, himag w.re]
  ring_nf

/--
The sum of rectangular boundary integrals obtained by successively cutting at real coordinates.

The empty list leaves the original rectangle unchanged.  A nonempty list removes the leftmost
strip and recursively subdivides the remaining rectangle.  No ordering assumption is needed for
the algebraic identity; later geometric applications may impose monotonicity separately.
-/
noncomputable def rectangleVerticalSubdivision (f : ℂ → ℂ) (z w : ℂ) : List ℝ → ℂ
  | [] => rectangleBoundaryIntegral f z w
  | m :: ms =>
    rectangleBoundaryIntegral f z (m + w.im * Complex.I) +
      rectangleVerticalSubdivision f (m + z.im * Complex.I) w ms

/--
The interval-integrability certificate consumed by a successive vertical subdivision.

At every cut it records integrability on the new left strip and on the whole remaining horizontal
edge.  The recursive component then supplies the corresponding data for all later cuts.  This
strong recursive form is designed to feed
`PseudoPrime.AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral_eq_add_vertical`
directly.
-/
def RectangleVerticalSubdivisionIntegrable (f : ℂ → ℂ) (z w : ℂ) : List ℝ → Prop
  | [] => True
  | m :: ms =>
    IntervalIntegrable (fun x : ℝ ↦ f (x + z.im * Complex.I)) MeasureTheory.volume z.re m ∧
      IntervalIntegrable (fun x : ℝ ↦ f (x + z.im * Complex.I)) MeasureTheory.volume m w.re ∧
      IntervalIntegrable (fun x : ℝ ↦ f (x + w.im * Complex.I)) MeasureTheory.volume z.re m ∧
      IntervalIntegrable (fun x : ℝ ↦ f (x + w.im * Complex.I)) MeasureTheory.volume m w.re ∧
      RectangleVerticalSubdivisionIntegrable f (m + z.im * Complex.I) w ms

/--
The sum of rectangular boundary integrals obtained by successively cutting at imaginary
coordinates.

The empty list leaves the rectangle unchanged.  Each cut removes the bottom strip and recursively
subdivides the remainder, providing the horizontal counterpart of
`PseudoPrime.AnalyticNumberTheory.RectangleGeometry.rectangleVerticalSubdivision`.
-/
noncomputable def rectangleHorizontalSubdivision (f : ℂ → ℂ) (z w : ℂ) : List ℝ → ℂ
  | [] => rectangleBoundaryIntegral f z w
  | m :: ms =>
    rectangleBoundaryIntegral f z (w.re + m * Complex.I) +
      rectangleHorizontalSubdivision f (z.re + m * Complex.I) w ms

/--
The interval-integrability certificate consumed by a successive horizontal subdivision.

At every cut it records the two pieces of the right and left vertical edges.  Its recursive tail
contains the same data for the rectangle remaining above the current cut.
-/
def RectangleHorizontalSubdivisionIntegrable (f : ℂ → ℂ) (z w : ℂ) : List ℝ → Prop
  | [] => True
  | m :: ms =>
    IntervalIntegrable (fun y : ℝ ↦ f (w.re + y * Complex.I)) MeasureTheory.volume z.im m ∧
      IntervalIntegrable (fun y : ℝ ↦ f (w.re + y * Complex.I)) MeasureTheory.volume m w.im ∧
      IntervalIntegrable (fun y : ℝ ↦ f (z.re + y * Complex.I)) MeasureTheory.volume z.im m ∧
      IntervalIntegrable (fun y : ℝ ↦ f (z.re + y * Complex.I)) MeasureTheory.volume m w.im ∧
      RectangleHorizontalSubdivisionIntegrable f (z.re + m * Complex.I) w ms

/--
A finite sequence of certified horizontal cuts preserves the outer rectangular boundary integral.

Induction applies the binary horizontal subdivision theorem at each cut.  Together with the
vertical analogue, this supplies the two finite one-dimensional stages of rectangular-grid
subdivision.
-/
theorem rectangleBoundaryIntegral_eq_horizontalSubdivision (f : ℂ → ℂ) (z w : ℂ) (cuts : List ℝ)
    (hcuts : RectangleHorizontalSubdivisionIntegrable f z w cuts) :
    rectangleBoundaryIntegral f z w = rectangleHorizontalSubdivision f z w cuts := by
  induction cuts generalizing z with
  | nil => rfl
  | cons m ms
    ih =>
    rcases hcuts with ⟨hrightBottom, hrightTop, hleftBottom, hleftTop, hrest⟩
    rw [rectangleBoundaryIntegral_eq_add_horizontal f z w m hrightBottom hrightTop hleftBottom
        hleftTop]
    simp only [rectangleHorizontalSubdivision]
    rw [ih (z.re + m * Complex.I) hrest]

/--
The sum of all rectangular cell boundaries obtained from finite real and imaginary cut lists.

The construction first forms vertical strips recursively.  Each completed strip is then expanded
by `PseudoPrime.AnalyticNumberTheory.RectangleGeometry.rectangleHorizontalSubdivision` using
the common imaginary cut list.  Thus the resulting terms are precisely the cells of
the rectangular grid, ordered strip by strip.
-/
noncomputable def rectangleGridSubdivision (f : ℂ → ℂ) (z w : ℂ) : List ℝ → List ℝ → ℂ
  | [], ycuts => rectangleHorizontalSubdivision f z w ycuts
  | m :: ms, ycuts =>
    rectangleHorizontalSubdivision f z (m + w.im * Complex.I) ycuts +
      rectangleGridSubdivision f (m + z.im * Complex.I) w ms ycuts

/--
The recursive interval-integrability certificate for a finite rectangular grid.

For an empty real cut list it is the horizontal certificate for the whole rectangle.  At a real
cut it records the four hypotheses needed to split off the left strip, the horizontal certificate
inside that strip, and the complete grid certificate for the remaining strips.
-/
def RectangleGridSubdivisionIntegrable (f : ℂ → ℂ) (z w : ℂ) : List ℝ → List ℝ → Prop
  | [], ycuts => RectangleHorizontalSubdivisionIntegrable f z w ycuts
  | m :: ms, ycuts =>
    IntervalIntegrable (fun x : ℝ ↦ f (x + z.im * Complex.I)) MeasureTheory.volume z.re m ∧
      IntervalIntegrable (fun x : ℝ ↦ f (x + z.im * Complex.I)) MeasureTheory.volume m w.re ∧
      IntervalIntegrable (fun x : ℝ ↦ f (x + w.im * Complex.I)) MeasureTheory.volume z.re m ∧
      IntervalIntegrable (fun x : ℝ ↦ f (x + w.im * Complex.I)) MeasureTheory.volume m w.re ∧
      RectangleHorizontalSubdivisionIntegrable f z (m + w.im * Complex.I) ycuts ∧
      RectangleGridSubdivisionIntegrable f (m + z.im * Complex.I) w ms ycuts

/--
Uniform vertical interval integrability supplies every recursive horizontal-cut certificate.

The input permits arbitrary fixed real coordinates and arbitrary interval endpoints.  The proof
only specializes it to the finitely many vertical edges created by the cut list.  This lemma keeps
the recursive bookkeeping separate from later analytic regularity arguments.
-/
theorem rectangleHorizontalSubdivisionIntegrable_of_forall (f : ℂ → ℂ) (z w : ℂ) (cuts : List ℝ)
    (hvertical :
      ∀ c a b : ℝ,
        IntervalIntegrable (fun y : ℝ ↦ f (c + y * Complex.I)) MeasureTheory.volume a b) :
    RectangleHorizontalSubdivisionIntegrable f z w cuts := by
  induction cuts generalizing z with
  | nil => trivial
  | cons m ms ih =>
    exact
      ⟨hvertical w.re z.im m, hvertical w.re m w.im, hvertical z.re z.im m, hvertical z.re m w.im,
        ih (z.re + m * Complex.I)⟩

/-- Pointwise continuity along a horizontal segment implies interval integrability. -/
theorem intervalIntegrable_horizontal_of_continuousAt (f : ℂ → ℂ) (c a b : ℝ)
    (hcontinuous : ∀ t ∈ Set.uIcc a b, ContinuousAt f (t + c * Complex.I)) :
    IntervalIntegrable (fun t : ℝ ↦ f (t + c * Complex.I)) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have hmap : ContinuousAt (fun u : ℝ ↦ (u : ℂ) + c * Complex.I) t := by fun_prop
  change ContinuousWithinAt (f ∘ fun u : ℝ ↦ (u : ℂ) + c * Complex.I) (Set.uIcc a b) t
  exact (hcontinuous t ht).comp_continuousWithinAt_of_eq hmap.continuousWithinAt rfl

/-- Pointwise continuity along a vertical segment implies interval integrability. -/
theorem intervalIntegrable_vertical_of_continuousAt (f : ℂ → ℂ) (c a b : ℝ)
    (hcontinuous : ∀ t ∈ Set.uIcc a b, ContinuousAt f (c + t * Complex.I)) :
    IntervalIntegrable (fun t : ℝ ↦ f (c + t * Complex.I)) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have hmap : ContinuousAt (fun u : ℝ ↦ (c : ℂ) + u * Complex.I) t := by fun_prop
  change ContinuousWithinAt (f ∘ fun u : ℝ ↦ (c : ℂ) + u * Complex.I) (Set.uIcc a b) t
  exact (hcontinuous t ht).comp_continuousWithinAt_of_eq hmap.continuousWithinAt rfl

/--
Integrability of every horizontal and vertical subsegment of one outer rectangle.

Each field accepts a fixed grid coordinate and two endpoints, all certified to lie in the
corresponding unordered outer intervals.  The structure is the nonrecursive analytic input from
which finite horizontal and two-dimensional subdivision certificates are constructed.
-/
structure RectangleGridEdgeIntegrable (f : ℂ → ℂ) (z w : ℂ) : Prop where
  horizontal :
    ∀ c ∈ Set.uIcc z.im w.im,
      ∀ a ∈ Set.uIcc z.re w.re,
        ∀ b ∈ Set.uIcc z.re w.re,
          IntervalIntegrable (fun t : ℝ ↦ f (t + c * Complex.I)) MeasureTheory.volume a b
  vertical :
    ∀ c ∈ Set.uIcc z.re w.re,
      ∀ a ∈ Set.uIcc z.im w.im,
        ∀ b ∈ Set.uIcc z.im w.im,
          IntervalIntegrable (fun t : ℝ ↦ f (c + t * Complex.I)) MeasureTheory.volume a b

/-- A bounded edge certificate supplies every recursive horizontal-cut hypothesis. -/
theorem RectangleGridEdgeIntegrable.horizontalSubdivision {f : ℂ → ℂ} {outerLeft outerRight z w : ℂ}
    (edges : RectangleGridEdgeIntegrable f outerLeft outerRight)
    (hzre : z.re ∈ Set.uIcc outerLeft.re outerRight.re)
    (hwre : w.re ∈ Set.uIcc outerLeft.re outerRight.re)
    (hzim : z.im ∈ Set.uIcc outerLeft.im outerRight.im)
    (hwim : w.im ∈ Set.uIcc outerLeft.im outerRight.im) (cuts : List ℝ)
    (hcuts : ∀ c ∈ cuts, c ∈ Set.uIcc outerLeft.im outerRight.im) :
    RectangleHorizontalSubdivisionIntegrable f z w cuts := by
  induction cuts generalizing z with
  | nil => trivial
  | cons m ms ih =>
    have hm := hcuts m (by simp only [List.mem_cons, true_or])
    have htail : ∀ c ∈ ms, c ∈ Set.uIcc outerLeft.im outerRight.im := by
      intro c hc
      exact hcuts c (by simp only [List.mem_cons, hc, or_true])
    exact
      ⟨edges.vertical w.re hwre z.im hzim m hm, edges.vertical w.re hwre m hm w.im hwim,
        edges.vertical z.re hzre z.im hzim m hm, edges.vertical z.re hzre m hm w.im hwim,
        ih (z := z.re + m * Complex.I)
          (by
            simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
              Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] using hzre)
          (by
            simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
              Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] using hm)
          htail⟩

/-- A bounded edge certificate supplies the complete recursive finite-grid certificate. -/
theorem RectangleGridEdgeIntegrable.gridSubdivision {f : ℂ → ℂ} {outerLeft outerRight z w : ℂ}
    (edges : RectangleGridEdgeIntegrable f outerLeft outerRight)
    (hzre : z.re ∈ Set.uIcc outerLeft.re outerRight.re)
    (hwre : w.re ∈ Set.uIcc outerLeft.re outerRight.re)
    (hzim : z.im ∈ Set.uIcc outerLeft.im outerRight.im)
    (hwim : w.im ∈ Set.uIcc outerLeft.im outerRight.im) (xcuts ycuts : List ℝ)
    (hxcuts : ∀ c ∈ xcuts, c ∈ Set.uIcc outerLeft.re outerRight.re)
    (hycuts : ∀ c ∈ ycuts, c ∈ Set.uIcc outerLeft.im outerRight.im) :
    RectangleGridSubdivisionIntegrable f z w xcuts ycuts := by
  induction xcuts generalizing z with
  | nil => exact edges.horizontalSubdivision hzre hwre hzim hwim ycuts hycuts
  | cons m ms ih =>
    have hm := hxcuts m (by simp only [List.mem_cons, true_or])
    have htail : ∀ c ∈ ms, c ∈ Set.uIcc outerLeft.re outerRight.re := by
      intro c hc
      exact hxcuts c (by simp only [List.mem_cons, hc, or_true])
    exact
      ⟨edges.horizontal z.im hzim z.re hzre m hm, edges.horizontal z.im hzim m hm w.re hwre,
        edges.horizontal w.im hwim z.re hzre m hm, edges.horizontal w.im hwim m hm w.re hwre,
        edges.horizontalSubdivision (z := z) (w := m + w.im * Complex.I) hzre
          (by
            simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
              Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] using hm)
          hzim
          (by
            simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
              Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] using hwim)
          ycuts hycuts,
        ih (z := m + z.im * Complex.I)
          (by
            simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
              Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] using hm)
          (by
            simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
              Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] using hzim)
          htail⟩

/-- Integrability restricted to two finite lists of permitted grid coordinates. -/
structure RectangleGridCoordinateIntegrable (f : ℂ → ℂ) (xcoordinates ycoordinates : List ℝ) :
    Prop where
  horizontal :
    ∀ c ∈ ycoordinates,
      ∀ a ∈ xcoordinates,
        ∀ b ∈ xcoordinates,
          IntervalIntegrable (fun t : ℝ ↦ f (t + c * Complex.I)) MeasureTheory.volume a b
  vertical :
    ∀ c ∈ xcoordinates,
      ∀ a ∈ ycoordinates,
        ∀ b ∈ ycoordinates,
          IntervalIntegrable (fun t : ℝ ↦ f (c + t * Complex.I)) MeasureTheory.volume a b

/-- Finite coordinate-line integrability supplies a horizontal subdivision certificate. -/
theorem RectangleGridCoordinateIntegrable.horizontalSubdivision {f : ℂ → ℂ}
    {xcoordinates ycoordinates : List ℝ} {z w : ℂ}
    (edges : RectangleGridCoordinateIntegrable f xcoordinates ycoordinates)
    (hzre : z.re ∈ xcoordinates) (hwre : w.re ∈ xcoordinates) (hzim : z.im ∈ ycoordinates)
    (hwim : w.im ∈ ycoordinates) (cuts : List ℝ) (hcuts : ∀ c ∈ cuts, c ∈ ycoordinates) :
    RectangleHorizontalSubdivisionIntegrable f z w cuts := by
  induction cuts generalizing z with
  | nil => trivial
  | cons m ms ih =>
    have hm := hcuts m (by simp only [List.mem_cons, true_or])
    have htail : ∀ c ∈ ms, c ∈ ycoordinates := by
      intro c hc
      exact hcuts c (by simp only [List.mem_cons, hc, or_true])
    exact
      ⟨edges.vertical w.re hwre z.im hzim m hm, edges.vertical w.re hwre m hm w.im hwim,
        edges.vertical z.re hzre z.im hzim m hm, edges.vertical z.re hzre m hm w.im hwim,
        ih (z := z.re + m * Complex.I)
          (by
            simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
              Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] using hzre)
          (by
            simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
              Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] using hm)
          htail⟩

/-- Finite coordinate-line integrability supplies a complete grid subdivision certificate. -/
theorem RectangleGridCoordinateIntegrable.gridSubdivision {f : ℂ → ℂ}
    {xcoordinates ycoordinates : List ℝ} {z w : ℂ}
    (edges : RectangleGridCoordinateIntegrable f xcoordinates ycoordinates)
    (hzre : z.re ∈ xcoordinates) (hwre : w.re ∈ xcoordinates) (hzim : z.im ∈ ycoordinates)
    (hwim : w.im ∈ ycoordinates) (xcuts ycuts : List ℝ) (hxcuts : ∀ c ∈ xcuts, c ∈ xcoordinates)
    (hycuts : ∀ c ∈ ycuts, c ∈ ycoordinates) :
    RectangleGridSubdivisionIntegrable f z w xcuts ycuts := by
  induction xcuts generalizing z with
  | nil => exact edges.horizontalSubdivision hzre hwre hzim hwim ycuts hycuts
  | cons m ms ih =>
    have hm := hxcuts m (by simp only [List.mem_cons, true_or])
    have htail : ∀ c ∈ ms, c ∈ xcoordinates := by
      intro c hc
      exact hxcuts c (by simp only [List.mem_cons, hc, or_true])
    exact
      ⟨edges.horizontal z.im hzim z.re hzre m hm, edges.horizontal z.im hzim m hm w.re hwre,
        edges.horizontal w.im hwim z.re hzre m hm, edges.horizontal w.im hwim m hm w.re hwre,
        edges.horizontalSubdivision (z := z) (w := m + w.im * Complex.I) hzre
          (by
            simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
              Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] using hm)
          hzim
          (by
            simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
              Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] using hwim)
          ycuts hycuts,
        ih (z := m + z.im * Complex.I)
          (by
            simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
              Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] using hm)
          (by
            simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
              Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] using hzim)
          htail⟩

/--
The outer rectangular boundary integral equals the sum of all certified grid-cell boundaries.

The proof inducts over the real cut list.  It splits off one vertical strip, applies the finite
horizontal theorem to that strip, and applies the induction hypothesis to all remaining strips.
Consequently every internal grid edge is cancelled by kernel-checked interval-integral algebra.
-/
theorem rectangleBoundaryIntegral_eq_gridSubdivision (f : ℂ → ℂ) (z w : ℂ) (xcuts ycuts : List ℝ)
    (hgrid : RectangleGridSubdivisionIntegrable f z w xcuts ycuts) :
    rectangleBoundaryIntegral f z w = rectangleGridSubdivision f z w xcuts ycuts := by
  induction xcuts generalizing z with
  | nil => exact rectangleBoundaryIntegral_eq_horizontalSubdivision f z w ycuts hgrid
  | cons m ms
    ih =>
    rcases hgrid with ⟨hbottomLeft, hbottomRight, htopLeft, htopRight, hleftStrip, hrest⟩
    rw [rectangleBoundaryIntegral_eq_add_vertical f z w m hbottomLeft hbottomRight htopLeft
        htopRight]
    simp only [rectangleGridSubdivision]
    rw [rectangleBoundaryIntegral_eq_horizontalSubdivision f z (m + w.im * Complex.I) ycuts
        hleftStrip]
    rw [ih (m + z.im * Complex.I) hrest]

/--
The ordered list of cells produced by successive horizontal cuts of one rectangle.

Each entry stores the opposite corners of one cell.  The order agrees definitionally with
`PseudoPrime.AnalyticNumberTheory.RectangleGeometry.rectangleHorizontalSubdivision`,
including degenerate or repeated cells when the cut list itself contains repeated coordinates.
-/
def rectangleHorizontalCells (z w : ℂ) : List ℝ → List (ℂ × ℂ)
  | [] => [(z, w)]
  | m :: ms => (z, w.re + m * Complex.I) :: rectangleHorizontalCells (z.re + m * Complex.I) w ms

/-- Turn one adjacent pair of imaginary coordinates into a cell with fixed real endpoints. -/
def horizontalCellOfImagPair (left right : ℝ) (pair : ℝ × ℝ) : ℂ × ℂ :=
  (left + pair.1 * Complex.I, right + pair.2 * Complex.I)

/--
Horizontal cells are the image of consecutive pairs in the endpoint-augmented coordinate list.
-/
theorem rectangleHorizontalCells_eq_map_consecutivePairs (z w : ℂ) (cuts : List ℝ) :
    rectangleHorizontalCells z w cuts =
      ((z.im :: cuts ++ [w.im]).consecutivePairs).map (horizontalCellOfImagPair z.re w.re) := by
  induction cuts generalizing z with
  | nil =>
    simp only [rectangleHorizontalCells, List.nil_append, List.cons_append, List.consecutivePairs,
      List.tail_cons, List.zip_cons_cons, List.map_cons]
    congr 2 <;> apply Complex.ext <;>
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_self,
        add_zero, zero_add]
  | cons m ms
    ih =>
    simp only [rectangleHorizontalCells, List.cons_append, List.consecutivePairs, List.tail_cons,
      List.zip_cons_cons, List.map_cons]
    congr 1
    · apply Prod.ext <;> apply Complex.ext <;>
        simp only [horizontalCellOfImagPair, Complex.add_re, Complex.add_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
          mul_one, sub_self, add_zero, zero_add]
    · change
        rectangleHorizontalCells (z.re + m * Complex.I) w ms =
          ((m :: ms ++ [w.im]).consecutivePairs).map (horizontalCellOfImagPair z.re w.re)
      simpa only [horizontalCellOfImagPair, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
        mul_one, sub_self, add_zero, zero_add] using ih (z.re + m * Complex.I)

/-- The conversion from imaginary-coordinate pairs to horizontal cells is injective. -/
theorem horizontalCellOfImagPair_injective (left right : ℝ) :
    Function.Injective (horizontalCellOfImagPair left right) := by
  intro p q hpq
  apply Prod.ext
  · have him := congrArg (fun cell : ℂ × ℂ ↦ cell.1.im) hpq
    simpa only [horizontalCellOfImagPair, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add] using
      him
  · have him := congrArg (fun cell : ℂ × ℂ ↦ cell.2.im) hpq
    simpa only [horizontalCellOfImagPair, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add] using
      him

/-- The horizontal subdivision value is the boundary-integral sum over its ordered cell list. -/
theorem rectangleHorizontalSubdivision_eq_sum_cells (f : ℂ → ℂ) (z w : ℂ) (cuts : List ℝ) :
    rectangleHorizontalSubdivision f z w cuts =
      List.sum
        ((rectangleHorizontalCells z w cuts).map
          (fun cell : ℂ × ℂ ↦ rectangleBoundaryIntegral f cell.1 cell.2)) := by
  induction cuts generalizing z with
  | nil =>
    simp only [rectangleHorizontalSubdivision, rectangleHorizontalCells, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  | cons m ms
    ih =>
    simp only [rectangleHorizontalSubdivision, rectangleHorizontalCells, List.map_cons,
      List.sum_cons]
    rw [ih (z.re + m * Complex.I)]

/--
The ordered list of all cells in a rectangular grid.

Cells follow the supplied imaginary-cut order within strips, and strips follow the real-cut order.
For increasing coordinates this is bottom-to-top within left-to-right strips. A list retains
repeated cuts and their multiplicities even when no ordering hypothesis is imposed.
-/
def rectangleGridCells (z w : ℂ) : List ℝ → List ℝ → List (ℂ × ℂ)
  | [], ycuts => rectangleHorizontalCells z w ycuts
  | m :: ms, ycuts =>
    rectangleHorizontalCells z (m + w.im * Complex.I) ycuts ++
      rectangleGridCells (m + z.im * Complex.I) w ms ycuts

/-- Convert a pair of real-coordinate intervals into their rectangular complex cell. -/
def gridCellOfCoordinatePairs (pairs : (ℝ × ℝ) × (ℝ × ℝ)) : ℂ × ℂ :=
  (pairs.1.1 + pairs.2.1 * Complex.I, pairs.1.2 + pairs.2.2 * Complex.I)

/--
The grid-cell list is the image of the Cartesian product of real and imaginary consecutive pairs.
-/
theorem rectangleGridCells_eq_map_product_consecutivePairs (z w : ℂ) (xcuts ycuts : List ℝ) :
    rectangleGridCells z w xcuts ycuts =
      (((z.re :: xcuts ++ [w.re]).consecutivePairs) ×ˢ
            ((z.im :: ycuts ++ [w.im]).consecutivePairs)).map
        gridCellOfCoordinatePairs := by
  induction xcuts generalizing z with
  | nil =>
    simp only [rectangleGridCells]
    rw [rectangleHorizontalCells_eq_map_consecutivePairs]
    simp only [List.consecutivePairs, List.cons_append, List.tail_cons, List.nil_append,
      List.zip_cons_cons, List.zip_nil_right, List.product_cons, List.nil_product, List.append_nil,
      List.map_map, List.map_inj_left, horizontalCellOfImagPair, Function.comp_apply,
      gridCellOfCoordinatePairs, implies_true]
  | cons m ms
    ih =>
    simp only [rectangleGridCells, List.cons_append, List.consecutivePairs, List.tail_cons,
      List.zip_cons_cons, List.product_cons, List.map_append]
    rw [rectangleHorizontalCells_eq_map_consecutivePairs]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero,
      zero_add, List.map_map]
    have hprefix :
      ((z.im :: ycuts ++ [w.im]).consecutivePairs).map (horizontalCellOfImagPair z.re m) =
        ((z.im :: ycuts ++ [w.im]).consecutivePairs).map
          (gridCellOfCoordinatePairs ∘ fun pair ↦ ((z.re, m), pair)) := by
      apply List.map_congr_left
      intro pair hpair
      apply Prod.ext <;> apply Complex.ext <;>
        simp only [horizontalCellOfImagPair, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero,
          Complex.add_im, Complex.mul_im, zero_add, Function.comp_apply, gridCellOfCoordinatePairs]
    rw [hprefix]
    rw [ih (m + z.im * Complex.I)]
    simp only [List.consecutivePairs, List.cons_append, List.tail_cons, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
      mul_one, sub_self, add_zero, Complex.add_im, Complex.mul_im, zero_add]

/-- The coordinate-pair conversion to a complex grid cell is injective. -/
theorem gridCellOfCoordinatePairs_injective : Function.Injective gridCellOfCoordinatePairs := by
  intro p q hpq
  apply Prod.ext <;> apply Prod.ext
  · have hre := congrArg (fun cell : ℂ × ℂ ↦ cell.1.re) hpq
    simpa only [gridCellOfCoordinatePairs, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] using
      hre
  · have hre := congrArg (fun cell : ℂ × ℂ ↦ cell.2.re) hpq
    simpa only [gridCellOfCoordinatePairs, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] using
      hre
  · have him := congrArg (fun cell : ℂ × ℂ ↦ cell.1.im) hpq
    simpa only [gridCellOfCoordinatePairs, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] using
      him
  · have him := congrArg (fun cell : ℂ × ℂ ↦ cell.2.im) hpq
    simpa only [gridCellOfCoordinatePairs, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] using
      him

/-- Duplicate-free endpoint coordinate lists produce a duplicate-free rectangular grid. -/
theorem rectangleGridCells_nodup {z w : ℂ} {xcuts ycuts : List ℝ}
    (hxcoordinates : (z.re :: xcuts ++ [w.re]).Nodup)
    (hycoordinates : (z.im :: ycuts ++ [w.im]).Nodup) :
    (rectangleGridCells z w xcuts ycuts).Nodup := by
  rw [rectangleGridCells_eq_map_product_consecutivePairs]
  apply List.Nodup.map gridCellOfCoordinatePairs_injective
  exact
    (List.Nodup.consecutivePairs hxcoordinates).product (List.Nodup.consecutivePairs hycoordinates)

/-- Every cell of a strict rectangular grid is itself strictly ordered on both coordinates. -/
theorem mem_rectangleGridCells_re_lt_im_lt {z w : ℂ} {xcuts ycuts : List ℝ}
    (hxorder : (z.re :: xcuts ++ [w.re]).Pairwise (· < ·))
    (hyorder : (z.im :: ycuts ++ [w.im]).Pairwise (· < ·)) {cell : ℂ × ℂ}
    (hcell : cell ∈ rectangleGridCells z w xcuts ycuts) :
    cell.1.re < cell.2.re ∧ cell.1.im < cell.2.im := by
  rw [rectangleGridCells_eq_map_product_consecutivePairs] at hcell
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hcell
  have hpMem := List.mem_product.mp hp
  have hpReal := List.rel_of_mem_consecutivePairs hxorder hpMem.1
  have hpImag := List.rel_of_mem_consecutivePairs hyorder hpMem.2
  simpa only [gridCellOfCoordinatePairs, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero,
    Complex.add_im, Complex.mul_im, zero_add] using And.intro hpReal hpImag

/--
Distinct cells of a strictly ordered rectangular grid have disjoint open boxes.

The grid representation as a product of consecutive coordinate pairs reduces distinctness to a
different real or imaginary interval.  Strict coordinate ordering separates that interval pair,
and
`PseudoPrime.AnalyticNumberTheory.RectangleGeometry.`
`rectangleOpenBox_disjoint_of_coordinate_separated`
finishes the geometric argument.
-/
theorem rectangleGridCells_openBox_disjoint {z w : ℂ} {xcuts ycuts : List ℝ}
    (hxorder : (z.re :: xcuts ++ [w.re]).Pairwise (· < ·))
    (hyorder : (z.im :: ycuts ++ [w.im]).Pairwise (· < ·)) {cell other : ℂ × ℂ}
    (hcell : cell ∈ rectangleGridCells z w xcuts ycuts)
    (hother : other ∈ rectangleGridCells z w xcuts ycuts) (hne : cell ≠ other) :
    Disjoint (rectangleOpenBox cell.1 cell.2) (rectangleOpenBox other.1 other.2) := by
  rw [rectangleGridCells_eq_map_product_consecutivePairs] at hcell hother
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hcell
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hother
  have hpMem := List.mem_product.mp hp
  have hqMem := List.mem_product.mp hq
  have hpReal := List.rel_of_mem_consecutivePairs hxorder hpMem.1
  have hqReal := List.rel_of_mem_consecutivePairs hxorder hqMem.1
  have hpImag := List.rel_of_mem_consecutivePairs hyorder hpMem.2
  have hqImag := List.rel_of_mem_consecutivePairs hyorder hqMem.2
  apply rectangleOpenBox_disjoint_of_coordinate_separated
  simp only [gridCellOfCoordinatePairs, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    mul_one, add_zero, zero_add, zero_sub, neg_zero, max_eq_right (le_of_lt hpReal),
    min_eq_left (le_of_lt hpReal), max_eq_right (le_of_lt hqReal), min_eq_left (le_of_lt hqReal),
    max_eq_right (le_of_lt hpImag), min_eq_left (le_of_lt hpImag), max_eq_right (le_of_lt hqImag),
    min_eq_left (le_of_lt hqImag)]
  by_cases hreal : p.1 = q.1
  · have himag : p.2 ≠ q.2 := by
      intro himag
      exact hne (congrArg gridCellOfCoordinatePairs (Prod.ext hreal himag))
    rcases List.consecutivePairs_separated hyorder hpMem.2 hqMem.2 himag with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · rcases List.consecutivePairs_separated hxorder hpMem.1 hqMem.1 hreal with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

/--
A point in a strict grid cell lies in its open box when it avoids every grid coordinate.

The product-of-consecutive-pairs representation identifies the four cell-edge coordinates with
entries of the endpoint-augmented coordinate lists.  Global coordinate avoidance therefore
supplies the four local inequalities required by
`PseudoPrime.AnalyticNumberTheory.RectangleGeometry.mem_rectangleOpenBox_of_mem_closedBox_of_ne`.
-/
theorem mem_rectangleGridCell_openBox_of_avoids_coordinates {z w s : ℂ} {xcuts ycuts : List ℝ}
    (hxorder : (z.re :: xcuts ++ [w.re]).Pairwise (· < ·))
    (hyorder : (z.im :: ycuts ++ [w.im]).Pairwise (· < ·)) {cell : ℂ × ℂ}
    (hcell : cell ∈ rectangleGridCells z w xcuts ycuts)
    (hsclosed : s ∈ Rectangle.rectangleClosedBox cell.1 cell.2)
    (hxavoid : s.re ∉ z.re :: xcuts ++ [w.re]) (hyavoid : s.im ∉ z.im :: ycuts ++ [w.im]) :
    s ∈ rectangleOpenBox cell.1 cell.2 := by
  rw [rectangleGridCells_eq_map_product_consecutivePairs] at hcell
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hcell
  have hpMem := List.mem_product.mp hp
  have hpReal := List.rel_of_mem_consecutivePairs hxorder hpMem.1
  have hpImag := List.rel_of_mem_consecutivePairs hyorder hpMem.2
  apply mem_rectangleOpenBox_of_mem_closedBox_of_ne
  · simpa only [gridCellOfCoordinatePairs, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] using
      hpReal
  · simpa only [gridCellOfCoordinatePairs, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] using
      hpImag
  · exact hsclosed
  · intro heq
    apply hxavoid
    rw [heq]
    simpa only [gridCellOfCoordinatePairs, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] using
      List.fst_mem_of_mem_consecutivePairs hpMem.1
  · intro heq
    apply hxavoid
    rw [heq]
    simpa only [gridCellOfCoordinatePairs, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] using
      List.snd_mem_of_mem_consecutivePairs hpMem.1
  · intro heq
    apply hyavoid
    rw [heq]
    simpa only [gridCellOfCoordinatePairs, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] using
      List.fst_mem_of_mem_consecutivePairs hpMem.2
  · intro heq
    apply hyavoid
    rw [heq]
    simpa only [gridCellOfCoordinatePairs, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] using
      List.snd_mem_of_mem_consecutivePairs hpMem.2

/--
Two points separated by a grid coordinate cannot belong to the same open grid cell.

For the coordinate direction witnessing separation, both points lying in one open cell would put
the separating coordinate strictly inside a consecutive interval.  This contradicts
`PseudoPrime.AnalyticNumberTheory.RectangleGeometry.List.not_between_of_mem_consecutivePairs`.
-/
theorem eq_of_mem_same_gridCell_openBox_of_coordinateSeparated {z w s t : ℂ} {xcuts ycuts : List ℝ}
    (hxorder : (z.re :: xcuts ++ [w.re]).Pairwise (· < ·))
    (hyorder : (z.im :: ycuts ++ [w.im]).Pairwise (· < ·)) {cell : ℂ × ℂ}
    (hcell : cell ∈ rectangleGridCells z w xcuts ycuts)
    (hsopen : s ∈ rectangleOpenBox cell.1 cell.2) (htopen : t ∈ rectangleOpenBox cell.1 cell.2)
    (hsep :
      (∃ u ∈ z.re :: xcuts ++ [w.re], (s.re < u ∧ u < t.re) ∨ (t.re < u ∧ u < s.re)) ∨
        ∃ v ∈ z.im :: ycuts ++ [w.im], (s.im < v ∧ v < t.im) ∨ (t.im < v ∧ v < s.im)) :
    s = t := by
  rw [rectangleGridCells_eq_map_product_consecutivePairs] at hcell
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hcell
  have hpMem := List.mem_product.mp hp
  have hpReal := List.rel_of_mem_consecutivePairs hxorder hpMem.1
  have hpImag := List.rel_of_mem_consecutivePairs hyorder hpMem.2
  have hsre : p.1.1 < s.re ∧ s.re < p.1.2 := by
    simpa only [gridCellOfCoordinatePairs, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero,
      min_eq_left (le_of_lt hpReal), max_eq_right (le_of_lt hpReal), Set.mem_preimage,
      Set.mem_Ioo] using hsopen.1
  have hsim : p.2.1 < s.im ∧ s.im < p.2.2 := by
    simpa only [gridCellOfCoordinatePairs, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add,
      min_eq_left (le_of_lt hpImag), max_eq_right (le_of_lt hpImag), Set.mem_preimage,
      Set.mem_Ioo] using hsopen.2
  have htre : p.1.1 < t.re ∧ t.re < p.1.2 := by
    simpa only [gridCellOfCoordinatePairs, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero,
      min_eq_left (le_of_lt hpReal), max_eq_right (le_of_lt hpReal), Set.mem_preimage,
      Set.mem_Ioo] using htopen.1
  have htim : p.2.1 < t.im ∧ t.im < p.2.2 := by
    simpa only [gridCellOfCoordinatePairs, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add,
      min_eq_left (le_of_lt hpImag), max_eq_right (le_of_lt hpImag), Set.mem_preimage,
      Set.mem_Ioo] using htopen.2
  rcases hsep with ⟨u, hu, hstu | htsu⟩ | ⟨v, hv, hstv | htsv⟩
  · exact
      False.elim
        (List.not_between_of_mem_consecutivePairs hxorder hpMem.1 hu
          ⟨hsre.1.trans hstu.1, hstu.2.trans htre.2⟩)
  · exact
      False.elim
        (List.not_between_of_mem_consecutivePairs hxorder hpMem.1 hu
          ⟨htre.1.trans htsu.1, htsu.2.trans hsre.2⟩)
  · exact
      False.elim
        (List.not_between_of_mem_consecutivePairs hyorder hpMem.2 hv
          ⟨hsim.1.trans hstv.1, hstv.2.trans htim.2⟩)
  · exact
      False.elim
        (List.not_between_of_mem_consecutivePairs hyorder hpMem.2 hv
          ⟨htim.1.trans htsv.1, htsv.2.trans hsim.2⟩)

/--
Strictly increasing interior coordinates remain strictly ordered after adjoining both endpoints.

The endpoint inequalities place the new coordinates before and after every cut, while the input
pairwise relation orders the cuts themselves.  This is the order-theoretic input for both grid-cell
`Nodup` and open-cell separation.
-/
theorem endpointAugmentedCoordinates_pairwise {a b : ℝ} {cuts : List ℝ} (hab : a < b)
    (hcuts : cuts.Pairwise (· < ·)) (hinside : ∀ u ∈ cuts, a < u ∧ u < b) :
    (a :: cuts ++ [b]).Pairwise (· < ·) := by
  rw [List.pairwise_append]
  refine ⟨?_, List.pairwise_singleton (R := fun x y : ℝ ↦ x < y) b, ?_⟩
  · rw [List.pairwise_cons]
    exact ⟨fun u hu ↦ (hinside u hu).1, hcuts⟩
  · intro u hu v hv
    rw [List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact List.mem_singleton.mp hv ▸ hab
    · exact List.mem_singleton.mp hv ▸ (hinside u hu).2

/--
Strictly increasing interior coordinates remain duplicate-free after adjoining both endpoints.

This is the duplicate-free consequence of
`PseudoPrime.AnalyticNumberTheory.RectangleGeometry.endpointAugmentedCoordinates_pairwise`,
retained as the direct input expected by the grid-cell list API.
-/
theorem endpointAugmentedCoordinates_nodup {a b : ℝ} {cuts : List ℝ} (hab : a < b)
    (hcuts : cuts.Pairwise (· < ·)) (hinside : ∀ u ∈ cuts, a < u ∧ u < b) :
    (a :: cuts ++ [b]).Nodup := by
  exact (endpointAugmentedCoordinates_pairwise hab hcuts hinside).nodup

/--
Consecutive intervals of ordered interior cuts cover the entire outer closed interval.

The proof removes the first interval at each cut.  A point at or left of the cut belongs to that
interval; a point to its right is covered recursively.  This supplies the one-dimensional coverage
component used to place every outer-rectangle point in a finite grid cell.
-/
theorem exists_mem_consecutivePair_of_mem_uIcc {a b x : ℝ} {cuts : List ℝ} (hab : a < b)
    (hcuts : cuts.Pairwise (· < ·)) (hinside : ∀ u ∈ cuts, a < u ∧ u < b) (hx : x ∈ Set.uIcc a b) :
    ∃ pair ∈ (a :: cuts ++ [b]).consecutivePairs, x ∈ Set.Icc pair.1 pair.2 := by
  rw [Set.uIcc_of_lt hab] at hx
  induction cuts generalizing a with
  | nil =>
    refine ⟨(a, b), ?_, hx⟩
    simp only [List.consecutivePairs, List.cons_append, List.nil_append, List.tail_cons,
      List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil, or_false]
  | cons m cuts ih =>
    have hm := hinside m (List.mem_cons_self)
    have htail := (List.pairwise_cons.mp hcuts).2
    by_cases hxm : x ≤ m
    · refine ⟨(a, m), ?_, ⟨hx.1, hxm⟩⟩
      simp only [List.consecutivePairs, List.cons_append, List.tail_cons, List.zip_cons_cons,
        List.mem_cons, true_or]
    · have hrest : ∀ u ∈ cuts, m < u ∧ u < b := by
        intro u hu
        exact
          ⟨(List.pairwise_cons.mp hcuts).1 u hu,
            (hinside u (by simp only [List.mem_cons, hu, or_true])).2⟩
      have hxrest : x ∈ Set.Icc m b := ⟨le_of_not_ge hxm, hx.2⟩
      obtain ⟨pair, hpair, hxpair⟩ := ih hm.2 htail hrest hxrest
      refine ⟨pair, ?_, hxpair⟩
      simp only [List.cons_append, List.consecutivePairs, List.tail_cons, List.zip_cons_cons,
        List.mem_cons]
      exact Or.inr hpair

/--
Every point of an ordered outer closed box belongs to a cell of its strict rectangular grid.

One-dimensional consecutive-interval coverage selects real and imaginary coordinate pairs.  Their
Cartesian product is a listed grid cell, and the two interval memberships give closed-box
membership.  This is the finite-grid coverage theorem used by the singularity ledger.
-/
theorem exists_mem_rectangleGridCell_closedBox {z w s : ℂ} {xcuts ycuts : List ℝ}
    (hre : z.re < w.re) (him : z.im < w.im) (hxorder : xcuts.Pairwise (· < ·))
    (hyorder : ycuts.Pairwise (· < ·)) (hxcuts : ∀ u ∈ xcuts, z.re < u ∧ u < w.re)
    (hycuts : ∀ v ∈ ycuts, z.im < v ∧ v < w.im) (hs : s ∈ Rectangle.rectangleClosedBox z w) :
    ∃ cell ∈ rectangleGridCells z w xcuts ycuts,
      s ∈ Rectangle.rectangleClosedBox cell.1 cell.2 := by
  obtain ⟨xp, hxp, hsx⟩ := exists_mem_consecutivePair_of_mem_uIcc hre hxorder hxcuts hs.1
  obtain ⟨yp, hyp, hsy⟩ := exists_mem_consecutivePair_of_mem_uIcc him hyorder hycuts hs.2
  refine ⟨gridCellOfCoordinatePairs (xp, yp), ?_, ?_⟩
  · rw [rectangleGridCells_eq_map_product_consecutivePairs]
    exact List.mem_map.mpr ⟨(xp, yp), List.mem_product.mpr ⟨hxp, hyp⟩, rfl⟩
  · simp only [Rectangle.rectangleClosedBox, gridCellOfCoordinatePairs, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
      mul_one, zero_sub, neg_zero, add_zero, Complex.add_im, Complex.mul_im, zero_add]
    exact ⟨Set.Icc_subset_uIcc hsx, Set.Icc_subset_uIcc hsy⟩

/--
Horizontal cells stay in an outer rectangle when their endpoints and all imaginary cuts do.

The outer rectangle is independent of the rectangle being subdivided.  This stronger induction
statement allows it to be reused for every vertical strip of a two-dimensional grid.
-/
theorem rectangleHorizontalCells_closedBox_subset {a b z w : ℂ} {cuts : List ℝ}
    (hare : a.re ∈ Set.uIcc z.re w.re) (hbre : b.re ∈ Set.uIcc z.re w.re)
    (haim : a.im ∈ Set.uIcc z.im w.im) (hbim : b.im ∈ Set.uIcc z.im w.im)
    (hcuts : ∀ y ∈ cuts, y ∈ Set.uIcc z.im w.im) :
    ∀ cell ∈ rectangleHorizontalCells a b cuts,
      Rectangle.rectangleClosedBox cell.1 cell.2 ⊆ Rectangle.rectangleClosedBox z w := by
  induction cuts generalizing a with
  | nil =>
    intro cell hcell
    simp only [rectangleHorizontalCells, List.mem_singleton] at hcell
    rw [hcell]
    exact rectangleClosedBox_subset_rectangleClosedBox hare hbre haim hbim
  | cons m ms ih =>
    intro cell hcell
    simp only [rectangleHorizontalCells, List.mem_cons] at hcell
    rcases hcell with rfl | hcell
    · change
        Rectangle.rectangleClosedBox a (b.re + m * Complex.I) ⊆ Rectangle.rectangleClosedBox z w
      have hm : m ∈ Set.uIcc z.im w.im := hcuts m (by simp only [List.mem_cons, true_or])
      have hnewre : (b.re + m * Complex.I).re ∈ Set.uIcc z.re w.re := by
        simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] using hbre
      have hnewim : (b.re + m * Complex.I).im ∈ Set.uIcc z.im w.im := by
        simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] using hm
      exact rectangleClosedBox_subset_rectangleClosedBox hare hnewre haim hnewim
    · have hm : m ∈ Set.uIcc z.im w.im := hcuts m (by simp only [List.mem_cons, true_or])
      have hnewre : (a.re + m * Complex.I).re ∈ Set.uIcc z.re w.re := by
        simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] using hare
      have hnewim : (a.re + m * Complex.I).im ∈ Set.uIcc z.im w.im := by
        simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] using hm
      exact
        ih hnewre hnewim (fun y hy ↦ hcuts y (by simp only [List.mem_cons, hy, or_true])) cell hcell

/-- Grid cells stay in an outer rectangle when all endpoints and cuts stay in its intervals. -/
theorem rectangleGridCells_closedBox_subset_of_endpoints {a b z w : ℂ} {xcuts ycuts : List ℝ}
    (hare : a.re ∈ Set.uIcc z.re w.re) (hbre : b.re ∈ Set.uIcc z.re w.re)
    (haim : a.im ∈ Set.uIcc z.im w.im) (hbim : b.im ∈ Set.uIcc z.im w.im)
    (hxcuts : ∀ x ∈ xcuts, x ∈ Set.uIcc z.re w.re) (hycuts : ∀ y ∈ ycuts, y ∈ Set.uIcc z.im w.im) :
    ∀ cell ∈ rectangleGridCells a b xcuts ycuts,
      Rectangle.rectangleClosedBox cell.1 cell.2 ⊆ Rectangle.rectangleClosedBox z w := by
  induction xcuts generalizing a with
  | nil => exact rectangleHorizontalCells_closedBox_subset hare hbre haim hbim hycuts
  | cons m ms ih =>
    intro cell hcell
    simp only [rectangleGridCells, List.mem_append] at hcell
    rcases hcell with hcell | hcell
    · apply
        rectangleHorizontalCells_closedBox_subset hare
          (by
            simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
              Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] using
              hxcuts m (by simp only [List.mem_cons, true_or]))
          haim
          (by
            simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
              Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] using hbim)
          hycuts cell hcell
    · have hm : m ∈ Set.uIcc z.re w.re := hxcuts m (by simp only [List.mem_cons, true_or])
      have hnewre : (m + a.im * Complex.I).re ∈ Set.uIcc z.re w.re := by
        simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] using hm
      have hnewim : (m + a.im * Complex.I).im ∈ Set.uIcc z.im w.im := by
        simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] using haim
      exact
        ih hnewre hnewim (fun x hx ↦ hxcuts x (by simp only [List.mem_cons, hx, or_true])) cell
          hcell

/-- Every enumerated grid cell stays in its outer box when all cuts stay in its intervals. -/
theorem rectangleGridCells_closedBox_subset {z w : ℂ} {xcuts ycuts : List ℝ}
    (hxcuts : ∀ x ∈ xcuts, x ∈ Set.uIcc z.re w.re) (hycuts : ∀ y ∈ ycuts, y ∈ Set.uIcc z.im w.im) :
    ∀ cell ∈ rectangleGridCells z w xcuts ycuts,
      Rectangle.rectangleClosedBox cell.1 cell.2 ⊆ Rectangle.rectangleClosedBox z w := by
  exact
    rectangleGridCells_closedBox_subset_of_endpoints Set.left_mem_uIcc Set.right_mem_uIcc
      Set.left_mem_uIcc Set.right_mem_uIcc hxcuts hycuts

/-- The grid subdivision value is the boundary-integral sum over its ordered cell list. -/
theorem rectangleGridSubdivision_eq_sum_cells (f : ℂ → ℂ) (z w : ℂ) (xcuts ycuts : List ℝ) :
    rectangleGridSubdivision f z w xcuts ycuts =
      List.sum
        ((rectangleGridCells z w xcuts ycuts).map
          (fun cell : ℂ × ℂ ↦ rectangleBoundaryIntegral f cell.1 cell.2)) := by
  induction xcuts generalizing z with
  | nil => exact rectangleHorizontalSubdivision_eq_sum_cells f z w ycuts
  | cons m ms
    ih =>
    simp only [rectangleGridSubdivision, rectangleGridCells, List.map_append, List.sum_append]
    rw [rectangleHorizontalSubdivision_eq_sum_cells f z (m + w.im * Complex.I) ycuts]
    rw [ih (m + z.im * Complex.I)]

/--
With no repeated cells, the grid subdivision is also the sum over the cell `Finset`.

The explicit `Nodup` hypothesis is essential: arbitrary cut lists may repeat coordinates and hence
produce repeated or degenerate cells whose multiplicity is retained by the ordered-list theorem
but intentionally erased by `List.toFinset`.
-/
theorem rectangleGridSubdivision_eq_sum_toFinset (f : ℂ → ℂ) (z w : ℂ) (xcuts ycuts : List ℝ)
    (hnodup : (rectangleGridCells z w xcuts ycuts).Nodup) :
    rectangleGridSubdivision f z w xcuts ycuts =
      ∑ cell ∈ (rectangleGridCells z w xcuts ycuts).toFinset,
        rectangleBoundaryIntegral f cell.1 cell.2 := by
  rw [rectangleGridSubdivision_eq_sum_cells]
  let cells := rectangleGridCells z w xcuts ycuts
  change cells.Nodup at hnodup
  change
    List.sum (cells.map (fun cell : ℂ × ℂ ↦ rectangleBoundaryIntegral f cell.1 cell.2)) =
      ∑ cell ∈ cells.toFinset, rectangleBoundaryIntegral f cell.1 cell.2
  revert hnodup
  induction cells with
  | nil =>
    intro; simp only [List.map_nil, List.sum_nil, List.toFinset_nil, Finset.sum_empty]
  | cons cell cells ih =>
    intro hnodup
    rw [List.nodup_cons] at hnodup
    simp only [List.map_cons, List.sum_cons, List.toFinset_cons]
    rw [Finset.sum_insert (by simpa only [List.mem_toFinset] using hnodup.1), ih hnodup.2]

/--
A finite rectangular ring collapses to its unique possibly nonzero center-cell boundary.

The subdivision certificate identifies the outer boundary with the sum of all cell boundaries.
Duplicate-freeness converts the ordered cell list to a finite set.  If a distinguished cell occurs
and every other cell integral vanishes, the finite sum reduces to that cell.  This is the algebraic
cancellation layer used before proving analytic regularity of the cells surrounding a puncture.
-/
theorem rectangleBoundaryIntegral_eq_cell_of_grid (f : ℂ → ℂ) (z w : ℂ) (xcuts ycuts : List ℝ)
    (center : ℂ × ℂ) (hgrid : RectangleGridSubdivisionIntegrable f z w xcuts ycuts)
    (hnodup : (rectangleGridCells z w xcuts ycuts).Nodup)
    (hcenter : center ∈ (rectangleGridCells z w xcuts ycuts).toFinset)
    (hzero :
      ∀ cell ∈ (rectangleGridCells z w xcuts ycuts).toFinset,
        cell ≠ center → rectangleBoundaryIntegral f cell.1 cell.2 = 0) :
    rectangleBoundaryIntegral f z w = rectangleBoundaryIntegral f center.1 center.2 := by
  rw [rectangleBoundaryIntegral_eq_gridSubdivision f z w xcuts ycuts hgrid]
  rw [rectangleGridSubdivision_eq_sum_toFinset f z w xcuts ycuts hnodup]
  apply Finset.sum_eq_single center
  · intro cell hcell hne
    exact hzero cell hcell hne
  · intro hnot
    exact (hnot hcenter).elim

/-- The rectangle determined by the two internal cuts is the middle cell of the `3 × 3` grid. -/
theorem innerRectangle_mem_threeByThreeGrid (z w a b : ℂ) :
    (a, b) ∈ rectangleGridCells z w [a.re, b.re] [a.im, b.im] := by
  simp only [rectangleGridCells, rectangleHorizontalCells, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false]
  right
  left
  right
  left
  apply Prod.ext <;> apply Complex.ext <;>
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.re_add_im]

/--
In a `3 × 3` subdivision, vanishing of the eight noncentral cells identifies both boundaries.
-/
theorem rectangleBoundaryIntegral_eq_innerRectangle (f : ℂ → ℂ) (z w a b : ℂ)
    (hgrid : RectangleGridSubdivisionIntegrable f z w [a.re, b.re] [a.im, b.im])
    (hnodup : (rectangleGridCells z w [a.re, b.re] [a.im, b.im]).Nodup)
    (hzero :
      ∀ cell ∈ (rectangleGridCells z w [a.re, b.re] [a.im, b.im]).toFinset,
        cell ≠ (a, b) → rectangleBoundaryIntegral f cell.1 cell.2 = 0) :
    rectangleBoundaryIntegral f z w = rectangleBoundaryIntegral f a b := by
  apply
    rectangleBoundaryIntegral_eq_cell_of_grid f z w [a.re, b.re] [a.im, b.im] (a, b) hgrid hnodup
  · simpa only [List.mem_toFinset] using innerRectangle_mem_threeByThreeGrid z w a b
  · exact hzero

/-- The lower-left corner of the axis-aligned square of coordinate radius `r` around `c`. -/
def centeredSquareLower (c : ℂ) (r : ℝ) : ℂ :=
  (c.re - r) + (c.im - r) * Complex.I

/-- The upper-right corner of the axis-aligned square of coordinate radius `r` around `c`. -/
def centeredSquareUpper (c : ℂ) (r : ℝ) : ℂ :=
  (c.re + r) + (c.im + r) * Complex.I

/-- The simple principal part is integrable on all four edges of a positive centered square. -/
theorem rectangleBoundaryIntegrable_sub_center_inv_centeredSquare (c : ℂ) {r : ℝ} (hr : 0 < r) :
    RectangleBoundaryIntegrable (fun z : ℂ ↦ (z - c)⁻¹) (centeredSquareLower c r)
      (centeredSquareUpper c r) := by
  have horizontal (k : ℝ) (hk : k ≠ 0) :
    Continuous (fun t : ℝ ↦ (t + (c.im + k) * Complex.I - c)⁻¹) := by
    apply Continuous.inv₀ (by fun_prop)
    intro t hzero
    have him := congrArg Complex.im hzero
    exact
      hk
        (by
          simpa only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
            Complex.add_re, Complex.ofReal_re, Complex.I_im, mul_one, add_zero, Complex.I_re,
            mul_zero, zero_add, add_sub_cancel_left, Complex.zero_im] using him)
  have vertical (k : ℝ) (hk : k ≠ 0) :
    Continuous (fun t : ℝ ↦ ((c.re + k) + t * Complex.I - c)⁻¹) := by
    apply Continuous.inv₀ (by fun_prop)
    intro t hzero
    have hre := congrArg Complex.re hzero
    exact
      hk
        (by
          simpa only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
            Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero,
            add_sub_cancel_left, Complex.zero_re] using hre)
  constructor
  · simpa only [centeredSquareLower, sub_eq_add_neg, Complex.add_im, Complex.ofReal_im,
      Complex.neg_im, neg_zero, add_zero, Complex.mul_im, Complex.add_re, Complex.ofReal_re,
      Complex.neg_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, zero_add, Complex.ofReal_add,
      Complex.ofReal_neg, Complex.mul_re, centeredSquareUpper] using
      (horizontal (-r) (neg_ne_zero.mpr hr.ne')).intervalIntegrable (c.re - r) (c.re + r)
  · simpa only [centeredSquareUpper, Complex.add_im, Complex.ofReal_im, add_zero, Complex.mul_im,
      Complex.add_re, Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, zero_add,
      Complex.ofReal_add, centeredSquareLower, Complex.sub_re, Complex.mul_re, Complex.sub_im,
      sub_self] using (horizontal r hr.ne').intervalIntegrable (c.re - r) (c.re + r)
  · simpa only [centeredSquareUpper, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, mul_zero, Complex.add_im, Complex.ofReal_im, add_zero, Complex.I_im, mul_one,
      sub_self, Complex.ofReal_add, centeredSquareLower, Complex.sub_im, Complex.mul_im,
      Complex.sub_re, zero_add] using (vertical r hr.ne').intervalIntegrable (c.im - r) (c.im + r)
  · simpa only [centeredSquareLower, sub_eq_add_neg, Complex.add_re, Complex.ofReal_re,
      Complex.neg_re, Complex.mul_re, Complex.I_re, mul_zero, Complex.add_im, Complex.ofReal_im,
      Complex.neg_im, neg_zero, add_zero, Complex.I_im, mul_one, Complex.ofReal_add,
      Complex.ofReal_neg, Complex.mul_im, zero_add, centeredSquareUpper] using
      (vertical (-r) (neg_ne_zero.mpr hr.ne')).intervalIntegrable (c.im - r) (c.im + r)

/-- The double principal part is integrable on all four edges of a positive centered square. -/
theorem rectangleBoundaryIntegrable_sub_center_inv_sq_centeredSquare (c : ℂ) {r : ℝ} (hr : 0 < r) :
    RectangleBoundaryIntegrable (fun z : ℂ ↦ (z - c)⁻¹ ^ 2) (centeredSquareLower c r)
      (centeredSquareUpper c r) := by
  have horizontal (k : ℝ) (hk : k ≠ 0) :
    Continuous (fun t : ℝ ↦ (t + (c.im + k) * Complex.I - c)⁻¹ ^ 2) := by
    apply (Continuous.inv₀ (by fun_prop) fun t hzero ↦ ?_).pow 2
    have him := congrArg Complex.im hzero
    exact
      hk
        (by
          simpa only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
            Complex.add_re, Complex.ofReal_re, Complex.I_im, mul_one, add_zero, Complex.I_re,
            mul_zero, zero_add, add_sub_cancel_left, Complex.zero_im] using him)
  have vertical (k : ℝ) (hk : k ≠ 0) :
    Continuous (fun t : ℝ ↦ ((c.re + k) + t * Complex.I - c)⁻¹ ^ 2) := by
    apply (Continuous.inv₀ (by fun_prop) fun t hzero ↦ ?_).pow 2
    have hre := congrArg Complex.re hzero
    exact
      hk
        (by
          simpa only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
            Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero,
            add_sub_cancel_left, Complex.zero_re] using hre)
  constructor
  · simpa only [centeredSquareLower, sub_eq_add_neg, Complex.add_im, Complex.ofReal_im,
      Complex.neg_im, neg_zero, add_zero, Complex.mul_im, Complex.add_re, Complex.ofReal_re,
      Complex.neg_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, zero_add, Complex.ofReal_add,
      Complex.ofReal_neg, inv_pow, Complex.mul_re, centeredSquareUpper] using
      (horizontal (-r) (neg_ne_zero.mpr hr.ne')).intervalIntegrable (c.re - r) (c.re + r)
  · simpa only [centeredSquareUpper, Complex.add_im, Complex.ofReal_im, add_zero, Complex.mul_im,
      Complex.add_re, Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, zero_add,
      Complex.ofReal_add, inv_pow, centeredSquareLower, Complex.sub_re, Complex.mul_re,
      Complex.sub_im, sub_self] using (horizontal r hr.ne').intervalIntegrable (c.re - r) (c.re + r)
  · simpa only [centeredSquareUpper, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, mul_zero, Complex.add_im, Complex.ofReal_im, add_zero, Complex.I_im, mul_one,
      sub_self, Complex.ofReal_add, inv_pow, centeredSquareLower, Complex.sub_im, Complex.mul_im,
      Complex.sub_re, zero_add] using (vertical r hr.ne').intervalIntegrable (c.im - r) (c.im + r)
  · simpa only [centeredSquareLower, sub_eq_add_neg, Complex.add_re, Complex.ofReal_re,
      Complex.neg_re, Complex.mul_re, Complex.I_re, mul_zero, Complex.add_im, Complex.ofReal_im,
      Complex.neg_im, neg_zero, add_zero, Complex.I_im, mul_one, Complex.ofReal_add,
      Complex.ofReal_neg, inv_pow, Complex.mul_im, zero_add, centeredSquareUpper] using
      (vertical (-r) (neg_ne_zero.mpr hr.ne')).intervalIntegrable (c.im - r) (c.im + r)

/--
Input/assumptions: a center and positive centered-square radius.
Conclusion: the triple inverse principal part is integrable on all four square edges.
Content: each edge stays a nonzero fixed real or imaginary distance from the center, so inversion
and its third power are continuous there.
Role: supplies the edge-integrability premise for triple-pole Laurent boundary formulas.
-/
theorem rectangleBoundaryIntegrable_sub_center_inv_cube_centeredSquare (c : ℂ) {r : ℝ}
    (hr : 0 < r) :
    RectangleBoundaryIntegrable (fun z : ℂ ↦ (z - c)⁻¹ ^ 3) (centeredSquareLower c r)
      (centeredSquareUpper c r) := by
  have horizontal (k : ℝ) (hk : k ≠ 0) :
    Continuous (fun t : ℝ ↦ (t + (c.im + k) * Complex.I - c)⁻¹ ^ 3) := by
    apply (Continuous.inv₀ (by fun_prop) fun t hzero ↦ ?_).pow 3
    have him := congrArg Complex.im hzero
    exact
      hk
        (by
          simpa only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
            Complex.add_re, Complex.ofReal_re, Complex.I_im, mul_one, add_zero, Complex.I_re,
            mul_zero, zero_add, add_sub_cancel_left, Complex.zero_im] using him)
  have vertical (k : ℝ) (hk : k ≠ 0) :
    Continuous (fun t : ℝ ↦ ((c.re + k) + t * Complex.I - c)⁻¹ ^ 3) := by
    apply (Continuous.inv₀ (by fun_prop) fun t hzero ↦ ?_).pow 3
    have hre := congrArg Complex.re hzero
    exact
      hk
        (by
          simpa only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
            Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero,
            add_sub_cancel_left, Complex.zero_re] using hre)
  constructor
  · simpa only [centeredSquareLower, sub_eq_add_neg, Complex.add_im, Complex.ofReal_im,
      Complex.neg_im, neg_zero, add_zero, Complex.mul_im, Complex.add_re, Complex.ofReal_re,
      Complex.neg_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, zero_add, Complex.ofReal_add,
      Complex.ofReal_neg, inv_pow, Complex.mul_re, centeredSquareUpper] using
      (horizontal (-r) (neg_ne_zero.mpr hr.ne')).intervalIntegrable (c.re - r) (c.re + r)
  · simpa only [centeredSquareUpper, Complex.add_im, Complex.ofReal_im, add_zero, Complex.mul_im,
      Complex.add_re, Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, zero_add,
      Complex.ofReal_add, inv_pow, centeredSquareLower, Complex.sub_re, Complex.mul_re,
      Complex.sub_im, sub_self] using (horizontal r hr.ne').intervalIntegrable (c.re - r) (c.re + r)
  · simpa only [centeredSquareUpper, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, mul_zero, Complex.add_im, Complex.ofReal_im, add_zero, Complex.I_im, mul_one,
      sub_self, Complex.ofReal_add, inv_pow, centeredSquareLower, Complex.sub_im, Complex.mul_im,
      Complex.sub_re, zero_add] using (vertical r hr.ne').intervalIntegrable (c.im - r) (c.im + r)
  · simpa only [centeredSquareLower, sub_eq_add_neg, Complex.add_re, Complex.ofReal_re,
      Complex.neg_re, Complex.mul_re, Complex.I_re, mul_zero, Complex.add_im, Complex.ofReal_im,
      Complex.neg_im, neg_zero, add_zero, Complex.I_im, mul_one, Complex.ofReal_add,
      Complex.ofReal_neg, inv_pow, Complex.mul_im, zero_add, centeredSquareUpper] using
      (vertical (-r) (neg_ne_zero.mpr hr.ne')).intervalIntegrable (c.im - r) (c.im + r)

/--
The simple pole at `c` has boundary integral `2πi` on every positive-radius centered square.

The translated corners are identified with the origin-centered model square, after which
`PseudoPrime.AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral_comp_sub_translate`
and the radius-independent origin computation give
the result.  This is the local simple-pole certificate used by downstream punctured contour.
-/
theorem rectangleBoundaryIntegral_sub_center_inv_centeredSquare (c : ℂ) {r : ℝ} (hr : 0 < r) :
    rectangleBoundaryIntegral (fun z : ℂ ↦ (z - c)⁻¹) (centeredSquareLower c r)
        (centeredSquareUpper c r) =
      2 * Real.pi * Complex.I := by
  have hlower : centeredSquareLower c r = c + ((-r : ℝ) - r * Complex.I) := by
    apply Complex.ext <;>
      simp only [centeredSquareLower, sub_eq_add_neg, Complex.add_re, Complex.ofReal_re,
        Complex.neg_re, Complex.mul_re, Complex.I_re, mul_zero, Complex.add_im, Complex.ofReal_im,
        Complex.neg_im, neg_zero, add_zero, Complex.I_im, mul_one, Complex.ofReal_neg,
        Complex.mul_im, zero_add]
  have hupper : centeredSquareUpper c r = c + (r + r * Complex.I) := by
    apply Complex.ext <;>
      simp only [centeredSquareUpper, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, mul_zero, Complex.add_im, Complex.ofReal_im, add_zero, Complex.I_im, mul_one,
        sub_self, Complex.mul_im, zero_add]
  rw [hlower, hupper, rectangleBoundaryIntegral_comp_sub_translate]
  exact rectangleBoundaryIntegral_inv_zero_centeredSquare hr

/--
The inverse-square principal part at `c` has zero boundary integral on every positive-radius
centered square.

Translation reduces the statement to the origin-centered endpoint-cancellation theorem.  This is
the double-pole certificate needed for the logarithmic-derivative kernel at a zeta pole.
-/
theorem rectangleBoundaryIntegral_sub_center_inv_sq_centeredSquare (c : ℂ) {r : ℝ} (hr : 0 < r) :
    rectangleBoundaryIntegral (fun z : ℂ ↦ (z - c)⁻¹ ^ 2) (centeredSquareLower c r)
        (centeredSquareUpper c r) =
      0 := by
  have hlower : centeredSquareLower c r = c + ((-r : ℝ) - r * Complex.I) := by
    apply Complex.ext <;>
      simp only [centeredSquareLower, sub_eq_add_neg, Complex.add_re, Complex.ofReal_re,
        Complex.neg_re, Complex.mul_re, Complex.I_re, mul_zero, Complex.add_im, Complex.ofReal_im,
        Complex.neg_im, neg_zero, add_zero, Complex.I_im, mul_one, Complex.ofReal_neg,
        Complex.mul_im, zero_add]
  have hupper : centeredSquareUpper c r = c + (r + r * Complex.I) := by
    apply Complex.ext <;>
      simp only [centeredSquareUpper, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, mul_zero, Complex.add_im, Complex.ofReal_im, add_zero, Complex.I_im, mul_one,
        sub_self, Complex.mul_im, zero_add]
  rw [hlower, hupper]
  calc
    rectangleBoundaryIntegral (fun z : ℂ ↦ (z - c)⁻¹ ^ 2) (c + ((-r : ℝ) - r * Complex.I))
          (c + (r + r * Complex.I)) =
        rectangleBoundaryIntegral (fun z : ℂ ↦ z⁻¹ ^ 2) ((-r : ℝ) - r * Complex.I)
          (r + r * Complex.I) :=
      by
      exact
        rectangleBoundaryIntegral_comp_sub_translate (fun z : ℂ ↦ z⁻¹ ^ 2) c
          ((-r : ℝ) - r * Complex.I) (r + r * Complex.I)
    _ = 0 := rectangleBoundaryIntegral_inv_sq_zero_centeredSquare hr

/--
The third-order principal part at `c` has zero boundary integral on every centered square.
Translation reduces the claim to the origin-centered primitive computation.
-/
theorem rectangleBoundaryIntegral_sub_center_inv_cube_centeredSquare (c : ℂ) {r : ℝ} (hr : 0 < r) :
    rectangleBoundaryIntegral (fun z : ℂ ↦ (z - c)⁻¹ ^ 3) (centeredSquareLower c r)
        (centeredSquareUpper c r) =
      0 := by
  have hlower : centeredSquareLower c r = c + ((-r : ℝ) - r * Complex.I) := by
    apply Complex.ext <;>
      simp only [centeredSquareLower, sub_eq_add_neg, Complex.add_re, Complex.ofReal_re,
        Complex.neg_re, Complex.mul_re, Complex.I_re, mul_zero, Complex.add_im, Complex.ofReal_im,
        Complex.neg_im, neg_zero, add_zero, Complex.I_im, mul_one, Complex.ofReal_neg,
        Complex.mul_im, zero_add]
  have hupper : centeredSquareUpper c r = c + (r + r * Complex.I) := by
    apply Complex.ext <;>
      simp only [centeredSquareUpper, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, mul_zero, Complex.add_im, Complex.ofReal_im, add_zero, Complex.I_im, mul_one,
        sub_self, Complex.mul_im, zero_add]
  rw [hlower, hupper]
  calc
    rectangleBoundaryIntegral (fun z : ℂ ↦ (z - c)⁻¹ ^ 3) (c + ((-r : ℝ) - r * Complex.I))
          (c + (r + r * Complex.I)) =
        rectangleBoundaryIntegral (fun z : ℂ ↦ z⁻¹ ^ 3) ((-r : ℝ) - r * Complex.I)
          (r + r * Complex.I) :=
      by
      exact
        rectangleBoundaryIntegral_comp_sub_translate (fun z : ℂ ↦ z⁻¹ ^ 3) c
          ((-r : ℝ) - r * Complex.I) (r + r * Complex.I)
    _ = 0 := rectangleBoundaryIntegral_inv_cube_zero_centeredSquare hr

/--
A local Laurent decomposition evaluates a centered-square boundary integral from its simple-pole
coefficient.

The inverse-square term integrates to zero, the inverse term integrates to `2πi`, and the remainder
vanishes by rectangular Cauchy--Goursat.  The explicit edge-integrability certificates keep all uses
of interval-integral linearity kernel checked.  The decomposition is only required on the square's
boundary: at the center `c` itself, `(z - c)⁻¹` takes Lean's junk value `0`, so demanding agreement
there as well would force `g c = kernel c`, which need not match the analytic remainder value.
-/
theorem rectangleBoundaryIntegral_eq_two_pi_I_mul_of_principalParts (kernel g : ℂ → ℂ) (c A B : ℂ)
    {r : ℝ} (hr : 0 < r)
    (hsq :
      RectangleBoundaryIntegrable (fun z : ℂ ↦ (z - c)⁻¹ ^ 2) (centeredSquareLower c r)
        (centeredSquareUpper c r))
    (hinv :
      RectangleBoundaryIntegrable (fun z : ℂ ↦ (z - c)⁻¹) (centeredSquareLower c r)
        (centeredSquareUpper c r))
    (hgint : RectangleBoundaryIntegrable g (centeredSquareLower c r) (centeredSquareUpper c r))
    (hgdiff :
      DifferentiableOn ℂ g
        (Rectangle.rectangleClosedBox (centeredSquareLower c r) (centeredSquareUpper c r)))
    (hkernel :
      Set.EqOn kernel (fun z : ℂ ↦ A * (z - c)⁻¹ ^ 2 + (B * (z - c)⁻¹ + g z))
        (Rectangle.rectangleClosedBox (centeredSquareLower c r) (centeredSquareUpper c r) \
          rectangleOpenBox (centeredSquareLower c r) (centeredSquareUpper c r))) :
    rectangleBoundaryIntegral kernel (centeredSquareLower c r) (centeredSquareUpper c r) =
      2 * Real.pi * Complex.I * B := by
  rw [rectangleBoundaryIntegral_congr_boundary hkernel]
  rw [rectangleBoundaryIntegral_add (hsq.const_mul A) ((hinv.const_mul B).add hgint)]
  rw [rectangleBoundaryIntegral_add (hinv.const_mul B) hgint]
  rw [rectangleBoundaryIntegral_const_mul, rectangleBoundaryIntegral_const_mul]
  rw [rectangleBoundaryIntegral_sub_center_inv_sq_centeredSquare c hr]
  rw [rectangleBoundaryIntegral_sub_center_inv_centeredSquare c hr]
  rw [rectangleBoundaryIntegral_eq_zero_of_differentiableOn g _ _ hgdiff]
  ring

/--
A Laurent decomposition with a third-order principal part still evaluates to its simple-pole
coefficient.  The cubic and quadratic terms have zero centered-square boundary integral.
-/
theorem rectangleBoundaryIntegral_eq_two_pi_I_mul_of_cubicPrincipalParts (kernel g : ℂ → ℂ)
    (c A B C : ℂ) {r : ℝ} (hr : 0 < r)
    (hcube :
      RectangleBoundaryIntegrable (fun z : ℂ ↦ (z - c)⁻¹ ^ 3) (centeredSquareLower c r)
        (centeredSquareUpper c r))
    (hsq :
      RectangleBoundaryIntegrable (fun z : ℂ ↦ (z - c)⁻¹ ^ 2) (centeredSquareLower c r)
        (centeredSquareUpper c r))
    (hinv :
      RectangleBoundaryIntegrable (fun z : ℂ ↦ (z - c)⁻¹) (centeredSquareLower c r)
        (centeredSquareUpper c r))
    (hgint : RectangleBoundaryIntegrable g (centeredSquareLower c r) (centeredSquareUpper c r))
    (hgdiff :
      DifferentiableOn ℂ g
        (Rectangle.rectangleClosedBox (centeredSquareLower c r) (centeredSquareUpper c r)))
    (hkernel :
      Set.EqOn kernel (fun z : ℂ ↦ A * (z - c)⁻¹ ^ 3 + (B * (z - c)⁻¹ ^ 2 + (C * (z - c)⁻¹ + g z)))
        (Rectangle.rectangleClosedBox (centeredSquareLower c r) (centeredSquareUpper c r) \
          rectangleOpenBox (centeredSquareLower c r) (centeredSquareUpper c r))) :
    rectangleBoundaryIntegral kernel (centeredSquareLower c r) (centeredSquareUpper c r) =
      2 * Real.pi * Complex.I * C := by
  rw [rectangleBoundaryIntegral_congr_boundary hkernel]
  rw [rectangleBoundaryIntegral_add (hcube.const_mul A)
      ((hsq.const_mul B).add ((hinv.const_mul C).add hgint))]
  rw [rectangleBoundaryIntegral_add (hsq.const_mul B) ((hinv.const_mul C).add hgint)]
  rw [rectangleBoundaryIntegral_add (hinv.const_mul C) hgint]
  rw [rectangleBoundaryIntegral_const_mul, rectangleBoundaryIntegral_const_mul,
    rectangleBoundaryIntegral_const_mul]
  rw [rectangleBoundaryIntegral_sub_center_inv_cube_centeredSquare c hr]
  rw [rectangleBoundaryIntegral_sub_center_inv_sq_centeredSquare c hr]
  rw [rectangleBoundaryIntegral_sub_center_inv_centeredSquare c hr]
  rw [rectangleBoundaryIntegral_eq_zero_of_differentiableOn g _ _ hgdiff]
  ring

/--
A closed ball contained in an oriented open rectangle places all four centered-square cuts inside.

The proof tests the ball inclusion on the four axial points at distance `r` from the center.  Only
their corresponding coordinate inequalities are used, so the square corners themselves need not
belong to the Euclidean ball.
-/
theorem centeredSquare_cuts_inside {z w c : ℂ} {r : ℝ} (hre : z.re < w.re) (him : z.im < w.im)
    (hr : 0 < r) (hball : Metric.closedBall c r ⊆ rectangleOpenBox z w) :
    z.re < (centeredSquareLower c r).re ∧
      (centeredSquareLower c r).re < (centeredSquareUpper c r).re ∧
      (centeredSquareUpper c r).re < w.re ∧
      z.im < (centeredSquareLower c r).im ∧
      (centeredSquareLower c r).im < (centeredSquareUpper c r).im ∧
      (centeredSquareUpper c r).im < w.im := by
  have hleft :=
    hball
      (show c - (r : ℂ) ∈ Metric.closedBall c r by
        simp only [Metric.mem_closedBall, dist_self_sub_left, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hr, Std.le_refl])
  have hright :=
    hball
      (show c + (r : ℂ) ∈ Metric.closedBall c r by
        simp only [Metric.mem_closedBall, dist_self_add_left, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hr, Std.le_refl])
  have hbottom :=
    hball
      (show c - r * Complex.I ∈ Metric.closedBall c r by
        simp only [Metric.mem_closedBall, dist_self_sub_left, Complex.norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hr, Complex.norm_I, mul_one, Std.le_refl])
  have htop :=
    hball
      (show c + r * Complex.I ∈ Metric.closedBall c r by
        simp only [Metric.mem_closedBall, dist_self_add_left, Complex.norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hr, Complex.norm_I, mul_one, Std.le_refl])
  simp only [rectangleOpenBox, min_eq_left hre.le, max_eq_right hre.le, min_eq_left him.le,
    max_eq_right him.le] at hleft hright hbottom htop
  simp only [centeredSquareLower, centeredSquareUpper, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add]
  constructor
  · simpa only [Complex.sub_re, Complex.ofReal_re] using hleft.1.1
  constructor
  · linarith
  constructor
  · simpa only [Complex.add_re, Complex.ofReal_re] using hright.1.2
  constructor
  · simpa only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, Complex.I_re, mul_zero, add_zero] using hbottom.2.1
  constructor
  · linarith
  · simpa only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, Complex.I_re, mul_zero, add_zero] using htop.2.2

/-- A cell-contained axial ball places its entire centered square in the parent closed box. -/
theorem centeredSquare_closedBox_subset_parent {z w c : ℂ} {r : ℝ} (hre : z.re < w.re)
    (him : z.im < w.im) (hr : 0 < r) (hball : Metric.closedBall c r ⊆ rectangleOpenBox z w) :
    Rectangle.rectangleClosedBox (centeredSquareLower c r) (centeredSquareUpper c r) ⊆
      Rectangle.rectangleClosedBox z w := by
  have hcuts := centeredSquare_cuts_inside hre him hr hball
  apply rectangleClosedBox_subset_rectangleClosedBox
  · exact Set.mem_uIcc_of_le hcuts.1.le (hcuts.2.1.trans hcuts.2.2.1).le
  · exact Set.mem_uIcc_of_le (hcuts.1.trans hcuts.2.1).le hcuts.2.2.1.le
  · exact Set.mem_uIcc_of_le hcuts.2.2.2.1.le (hcuts.2.2.2.2.1.trans hcuts.2.2.2.2.2).le
  · exact Set.mem_uIcc_of_le (hcuts.2.2.2.1.trans hcuts.2.2.2.2.1).le hcuts.2.2.2.2.2.le

/-- A centered square's endpoint-augmented coordinates avoid its center. -/
theorem centeredSquare_augmented_coordinates_avoid {z w c : ℂ} {r : ℝ} (hre : z.re < w.re)
    (him : z.im < w.im) (hr : 0 < r) (hc : c ∈ rectangleOpenBox z w) :
    (∀ u ∈ z.re :: [(centeredSquareLower c r).re, (centeredSquareUpper c r).re] ++ [w.re],
        c.re ≠ u) ∧
      ∀ v ∈ z.im :: [(centeredSquareLower c r).im, (centeredSquareUpper c r).im] ++ [w.im],
        c.im ≠ v := by
  simp only [rectangleOpenBox, min_eq_left hre.le, max_eq_right hre.le, min_eq_left him.le,
    max_eq_right him.le] at hc
  constructor
  · intro u hu
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with (rfl | rfl | rfl) | rfl
    · exact ne_of_gt hc.1.1
    · simp only [centeredSquareLower, Complex.add_re, Complex.sub_re, Complex.ofReal_re,
        Complex.mul_re, Complex.I_re, mul_zero, Complex.sub_im, Complex.ofReal_im, sub_self,
        Complex.I_im, mul_one, add_zero, ne_eq]
      linarith
    · simp only [centeredSquareUpper, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, mul_zero, Complex.add_im, Complex.ofReal_im, add_zero, Complex.I_im, mul_one,
        sub_self, ne_eq, left_eq_add, hr.ne', not_false_eq_true]
    · exact ne_of_lt hc.1.2
  · intro v hv
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with (rfl | rfl | rfl) | rfl
    · exact ne_of_gt hc.2.1
    · simp only [centeredSquareLower, Complex.add_im, Complex.sub_im, Complex.ofReal_im, sub_self,
        Complex.mul_im, Complex.sub_re, Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re,
        mul_zero, add_zero, zero_add, ne_eq]
      linarith
    · simp only [centeredSquareUpper, Complex.add_im, Complex.ofReal_im, add_zero, Complex.mul_im,
        Complex.add_re, Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, zero_add,
        ne_eq, left_eq_add, hr.ne', not_false_eq_true]
    · exact ne_of_lt hc.2.2

/-- Strict outer and inner coordinates make the corresponding `3 × 3` grid duplicate-free. -/
theorem threeByThreeGrid_nodup {z w a b : ℂ} (hzare : z.re < a.re) (habre : a.re < b.re)
    (hbwre : b.re < w.re) (hzaim : z.im < a.im) (habim : a.im < b.im) (hbwim : b.im < w.im) :
    (rectangleGridCells z w [a.re, b.re] [a.im, b.im]).Nodup := by
  apply rectangleGridCells_nodup
  · apply endpointAugmentedCoordinates_nodup (hzare.trans (habre.trans hbwre))
    · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq, habre,
        IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_self]
    · intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · exact ⟨hzare, habre.trans hbwre⟩
      · exact ⟨hzare.trans habre, hbwre⟩
  · apply endpointAugmentedCoordinates_nodup (hzaim.trans (habim.trans hbwim))
    · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq, habim,
        IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_self]
    · intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact ⟨hzaim, habim.trans hbwim⟩
      · exact ⟨hzaim.trans habim, hbwim⟩

/-- A positive-radius centered square contains its center in its open rectangle. -/
theorem center_mem_centeredSquare_openBox (c : ℂ) {r : ℝ} (hr : 0 < r) :
    c ∈ rectangleOpenBox (centeredSquareLower c r) (centeredSquareUpper c r) := by
  have hre : (centeredSquareLower c r).re < (centeredSquareUpper c r).re := by
    simp only [centeredSquareLower, Complex.add_re, Complex.sub_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, mul_zero, Complex.sub_im, Complex.ofReal_im, sub_self,
      Complex.I_im, mul_one, add_zero, centeredSquareUpper, Complex.add_im]
    linarith
  have him : (centeredSquareLower c r).im < (centeredSquareUpper c r).im := by
    simp only [centeredSquareLower, Complex.add_im, Complex.sub_im, Complex.ofReal_im, sub_self,
      Complex.mul_im, Complex.sub_re, Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re,
      mul_zero, add_zero, zero_add, centeredSquareUpper, Complex.add_re]
    linarith
  simp only [rectangleOpenBox, min_eq_left hre.le, max_eq_right hre.le, min_eq_left him.le,
    max_eq_right him.le]
  constructor <;> constructor <;>
    simp only [centeredSquareLower, centeredSquareUpper, Complex.add_re, Complex.sub_re,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero, Complex.sub_im, Complex.ofReal_im,
      sub_self, Complex.I_im, mul_one, add_zero, Complex.add_im, Complex.mul_im, zero_add,
      sub_lt_self_iff, lt_add_iff_pos_right] <;>
    linarith

/-- Every strictly smaller closed ball lies in the open centered square. -/
theorem closedBall_subset_centeredSquare_openBox (c : ℂ) {ρ r : ℝ} (hρ : 0 ≤ ρ) (hρr : ρ < r) :
    Metric.closedBall c ρ ⊆
      rectangleOpenBox (centeredSquareLower c r) (centeredSquareUpper c r) := by
  intro z hz
  have hnorm : ‖z - c‖ ≤ ρ := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have hre := (Complex.abs_re_le_norm (z - c)).trans hnorm
  have him := (Complex.abs_im_le_norm (z - c)).trans hnorm
  rw [abs_le] at hre him
  simp only [Complex.sub_re] at hre
  simp only [Complex.sub_im] at him
  have hr : 0 < r := hρ.trans_lt hρr
  simp only [rectangleOpenBox, centeredSquareLower, centeredSquareUpper, Complex.add_re,
    Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero,
    add_zero, zero_add]
  rw [min_eq_left (by linarith : c.re - r ≤ c.re + r),
    max_eq_right (by linarith : c.re - r ≤ c.re + r),
    min_eq_left (by linarith : c.im - r ≤ c.im + r),
    max_eq_right (by linarith : c.im - r ≤ c.im + r)]
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/--
A point in the open middle rectangle belongs to no other closed cell of the strict `3 × 3` grid.

The finite proof expands the nine cells.  In each of the eight surrounding cases, one coordinate
of the point is strictly beyond the corresponding closed interval; the remaining case contradicts
the hypothesis that the cell is not the middle rectangle.
-/
theorem not_mem_noncentral_threeByThreeGridCell {z w a b c : ℂ} (hzare : z.re < a.re)
    (habre : a.re < b.re) (hbwre : b.re < w.re) (hzaim : z.im < a.im) (habim : a.im < b.im)
    (hbwim : b.im < w.im) (hc : c ∈ rectangleOpenBox a b) {cell : ℂ × ℂ}
    (hcell : cell ∈ rectangleGridCells z w [a.re, b.re] [a.im, b.im]) (hne : cell ≠ (a, b)) :
    c ∉ Rectangle.rectangleClosedBox cell.1 cell.2 := by
  simp only [rectangleGridCells, rectangleHorizontalCells, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hcell
  rcases hcell with (rfl | rfl | rfl) | (rfl | rfl | rfl) | (rfl | rfl | rfl)
  all_goals
    simp only [rectangleOpenBox, min_eq_left habre.le, max_eq_right habre.le, min_eq_left habim.le,
      max_eq_right habim.le] at hc
  all_goals
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero,
      zero_add] at hne ⊢
  all_goals
    intro hclosed
    rcases hc with ⟨hcre, hcim⟩
    change a.re < c.re ∧ c.re < b.re at hcre
    change a.im < c.im ∧ c.im < b.im at hcim
    rcases hclosed with ⟨hclosedre, hclosedim⟩
    simp only [Complex.re_add_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
      mul_one, add_zero, zero_add, sub_self, Set.uIcc_of_le hzare.le, Set.mem_preimage, Set.mem_Icc,
      Set.uIcc_of_le habre.le, Set.uIcc_of_le hbwre.le, Set.uIcc_of_le hzaim.le,
      Set.uIcc_of_le habim.le, Set.uIcc_of_le hbwim.le] at hclosedre hclosedim
    try linarith
  apply hne
  apply Prod.ext <;> apply Complex.ext <;> simp only [Complex.re_add_im]

/-- The set forming the four edges of an axis-aligned closed rectangle. -/
def rectangleClosedBoxBoundary (z w : ℂ) : Set ℂ :=
  Rectangle.rectangleClosedBox z w \
    (Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ Set.Ioo (min z.im w.im) (max z.im w.im))

/--
Every point of a centered-square boundary is at least its coordinate radius from the center.
-/
theorem centeredSquare_radius_le_norm_sub_of_mem_boundary {c s : ℂ} {r : ℝ}
    (hs : s ∈ rectangleClosedBoxBoundary (centeredSquareLower c r) (centeredSquareUpper c r)) :
    r ≤ ‖s - c‖ := by
  by_contra hnorm
  have hlt : ‖s - c‖ < r := lt_of_not_ge hnorm
  have hsball : s ∈ Metric.closedBall c ‖s - c‖ := by
    simp only [Metric.mem_closedBall, dist_eq_norm]
    exact le_rfl
  have hsopen := closedBall_subset_centeredSquare_openBox c (norm_nonneg (s - c)) hlt hsball
  exact hs.2 hsopen

/-- A nonnegative-radius centered square lies in the circumscribed ball of radius `√2 * r`. -/
theorem centeredSquare_closedRectangle_subset_closedBall (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    Rectangle.rectangleClosedBox (centeredSquareLower c r) (centeredSquareUpper c r) ⊆
      Metric.closedBall c (Real.sqrt 2 * r) := by
  intro s hs
  have hcorners : c.re - r ≤ c.re + r ∧ c.im - r ≤ c.im + r := by constructor <;> linarith
  simp only [Rectangle.rectangleClosedBox, Rectangle.rectangleClosedBox, Complex.mem_reProdIm,
    centeredSquareLower, centeredSquareUpper, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add] at hs
  rw [Set.uIcc_of_le hcorners.1, Set.uIcc_of_le hcorners.2] at hs
  have hre : |(s - c).re| ≤ r := by
    rw [abs_le]
    simp only [Complex.sub_re]
    exact ⟨by linarith [hs.1.1], by linarith [hs.1.2]⟩
  have him : |(s - c).im| ≤ r := by
    rw [abs_le]
    simp only [Complex.sub_im]
    exact ⟨by linarith [hs.2.1], by linarith [hs.2.2]⟩
  have hnorm : ‖s - c‖ ≤ Real.sqrt 2 * r :=
    (Complex.norm_le_sqrt_two_mul_max (s - c)).trans
      (mul_le_mul_of_nonneg_left (max_le hre him) (Real.sqrt_nonneg 2))
  simpa only [Metric.mem_closedBall, dist_eq_norm] using hnorm

/--
A punctured-neighborhood simple-pole identity yields the expected boundary integral on every
sufficiently small positive-radius centered square.

This is the square-contour counterpart of
`PseudoPrime.AnalyticNumberTheory.General.exists_radius_forall_circleIntegral_eq_two_pi_I_mul`,
feeding
`rectangleBoundaryIntegral_eq_two_pi_I_mul_of_principalParts`
with a zero double-pole coefficient.
-/
theorem exists_radius_forall_rectangleBoundaryIntegral_eq_two_pi_I_mul {f h : ℂ → ℂ} {c : ℂ}
    (hh : AnalyticAt ℂ h c)
    (heq : Filter.EventuallyEq (nhdsWithin c ({c}ᶜ : Set ℂ)) (fun z ↦ (z - c) * f z) h) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ r : ℝ,
          0 < r →
            r ≤ R →
            rectangleBoundaryIntegral f (centeredSquareLower c r) (centeredSquareUpper c r) =
              2 * Real.pi * Complex.I * h c := by
  obtain ⟨rg, hrg, hganalytic⟩ := hh.exists_ball_analyticOnNhd
  have hevent : ∀ᶠ z in nhds c, z ∈ ({c}ᶜ : Set ℂ) → (z - c) * f z = h z :=
    eventuallyEq_nhdsWithin_iff.mp heq
  obtain ⟨re, hre, hball⟩ := Metric.mem_nhds_iff.mp hevent
  set R := min rg re / 2 with hRdef
  have hR : 0 < R := half_pos (lt_min hrg hre)
  have hsqrtlt : Real.sqrt 2 < 2 := by
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num only)
    nlinarith only [hsq]
  have hsqrt2R : Real.sqrt 2 * R < min rg re := by
    have : Real.sqrt 2 * R < 2 * R := by
      nlinarith only [hsqrtlt, hR, mul_lt_mul_of_pos_right hsqrtlt hR]
    rwa [hRdef, show (2 : ℝ) * (min rg re / 2) = min rg re by ring] at this
  refine ⟨R, hR, fun r hr hrR ↦ ?_⟩
  have hsqrt2r : Real.sqrt 2 * r < min rg re :=
    (mul_le_mul_of_nonneg_left hrR (Real.sqrt_nonneg 2)).trans_lt hsqrt2R
  have hsquareSubsetRg :
    Rectangle.rectangleClosedBox (centeredSquareLower c r) (centeredSquareUpper c r) ⊆
      Metric.ball c rg :=
    (centeredSquare_closedRectangle_subset_closedBall c hr.le).trans
      (Metric.closedBall_subset_ball (hsqrt2r.trans_le (min_le_left rg re)))
  have hsquareSubsetRe :
    Rectangle.rectangleClosedBox (centeredSquareLower c r) (centeredSquareUpper c r) ⊆
      Metric.ball c re :=
    (centeredSquare_closedRectangle_subset_closedBall c hr.le).trans
      (Metric.closedBall_subset_ball (hsqrt2r.trans_le (min_le_right rg re)))
  have hboundaryNeC :
    ∀ z ∈ rectangleClosedBoxBoundary (centeredSquareLower c r) (centeredSquareUpper c r),
      z ≠ c := by
    intro z hz hzc
    have hdist := centeredSquare_radius_le_norm_sub_of_mem_boundary hz
    rw [hzc, sub_self, norm_zero] at hdist
    exact absurd hdist (not_le.mpr hr)
  have heqBoundary :
    ∀ z ∈ rectangleClosedBoxBoundary (centeredSquareLower c r) (centeredSquareUpper c r),
      (z - c) * f z = h z :=
    fun z hz ↦ hball (hsquareSubsetRe hz.1) (Set.mem_compl_singleton_iff.mpr (hboundaryNeC z hz))
  have hmemEdge :
    ∀ z : ℂ,
      z.re ∈ Set.uIcc (centeredSquareLower c r).re (centeredSquareUpper c r).re →
        z.im ∈ Set.uIcc (centeredSquareLower c r).im (centeredSquareUpper c r).im →
        ContinuousAt (dslope h c) z := by
    intro z hre him
    have hz :
      z ∈ Rectangle.rectangleClosedBox (centeredSquareLower c r) (centeredSquareUpper c r) :=
      Complex.mem_reProdIm.mpr ⟨hre, him⟩
    rcases eq_or_ne z c with rfl | hne
    · exact (General.AnalyticAt.dslope hh).continuousAt
    · exact (continuousAt_dslope_of_ne hne).mpr (hganalytic z (hsquareSubsetRg hz)).continuousAt
  have hgint :
    RectangleBoundaryIntegrable (dslope h c) (centeredSquareLower c r)
      (centeredSquareUpper c r) := by
    constructor
    · apply intervalIntegrable_horizontal_of_continuousAt
      intro t ht
      apply hmemEdge
      · simpa only [centeredSquareLower, Complex.add_re, Complex.sub_re, Complex.ofReal_re,
          Complex.mul_re, Complex.I_re, mul_zero, Complex.sub_im, Complex.ofReal_im, sub_self,
          Complex.I_im, mul_one, add_zero, centeredSquareUpper, Complex.add_im, Complex.mul_im,
          zero_add, Complex.ofReal_sub] using ht
      · simp only [centeredSquareLower, Complex.add_im, Complex.sub_im, Complex.ofReal_im, sub_self,
          Complex.mul_im, Complex.sub_re, Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re,
          mul_zero, add_zero, zero_add, centeredSquareUpper, Complex.add_re, Complex.ofReal_sub,
          Set.left_mem_uIcc]
    · apply intervalIntegrable_horizontal_of_continuousAt
      intro t ht
      apply hmemEdge
      · simpa only [centeredSquareLower, Complex.add_re, Complex.sub_re, Complex.ofReal_re,
          Complex.mul_re, Complex.I_re, mul_zero, Complex.sub_im, Complex.ofReal_im, sub_self,
          Complex.I_im, mul_one, add_zero, centeredSquareUpper, Complex.add_im, Complex.mul_im,
          zero_add, Complex.ofReal_add] using ht
      · simp only [centeredSquareLower, Complex.add_im, Complex.sub_im, Complex.ofReal_im, sub_self,
          Complex.mul_im, Complex.sub_re, Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re,
          mul_zero, add_zero, zero_add, centeredSquareUpper, Complex.add_re, Complex.ofReal_add,
          Set.right_mem_uIcc]
    · apply intervalIntegrable_vertical_of_continuousAt
      intro t ht
      apply hmemEdge
      · simp only [centeredSquareLower, Complex.add_re, Complex.sub_re, Complex.ofReal_re,
          Complex.mul_re, Complex.I_re, mul_zero, Complex.sub_im, Complex.ofReal_im, sub_self,
          Complex.I_im, mul_one, add_zero, centeredSquareUpper, Complex.add_im, Complex.ofReal_add,
          Set.right_mem_uIcc]
      · simpa only [centeredSquareLower, Complex.add_im, Complex.sub_im, Complex.ofReal_im,
          sub_self, Complex.mul_im, Complex.sub_re, Complex.ofReal_re, Complex.I_im, mul_one,
          Complex.I_re, mul_zero, add_zero, zero_add, centeredSquareUpper, Complex.add_re,
          Complex.mul_re, Complex.ofReal_add] using ht
    · apply intervalIntegrable_vertical_of_continuousAt
      intro t ht
      apply hmemEdge
      · simp only [centeredSquareLower, Complex.add_re, Complex.sub_re, Complex.ofReal_re,
          Complex.mul_re, Complex.I_re, mul_zero, Complex.sub_im, Complex.ofReal_im, sub_self,
          Complex.I_im, mul_one, add_zero, centeredSquareUpper, Complex.add_im, Complex.ofReal_sub,
          Set.left_mem_uIcc]
      · simpa only [centeredSquareLower, Complex.add_im, Complex.sub_im, Complex.ofReal_im,
          sub_self, Complex.mul_im, Complex.sub_re, Complex.ofReal_re, Complex.I_im, mul_one,
          Complex.I_re, mul_zero, add_zero, zero_add, centeredSquareUpper, Complex.add_re,
          Complex.mul_re, Complex.ofReal_sub] using ht
  have hgdiff :
    DifferentiableOn ℂ (dslope h c)
      (Rectangle.rectangleClosedBox (centeredSquareLower c r) (centeredSquareUpper c r)) := by
    intro z hz
    rcases eq_or_ne z c with rfl | hne
    · exact (General.AnalyticAt.dslope hh).differentiableAt.differentiableWithinAt
    · exact
        ((differentiableAt_dslope_of_ne hne).mpr
            (hganalytic z (hsquareSubsetRg hz)).differentiableAt).differentiableWithinAt
  have hkernel :
    Set.EqOn f (fun z : ℂ ↦ (0 : ℂ) * (z - c)⁻¹ ^ 2 + (h c * (z - c)⁻¹ + dslope h c z))
      (Rectangle.rectangleClosedBox (centeredSquareLower c r) (centeredSquareUpper c r) \
        rectangleOpenBox (centeredSquareLower c r) (centeredSquareUpper c r)) := by
    intro z hz
    have hne : z ≠ c := hboundaryNeC z hz
    have hsub : z - c ≠ 0 := sub_ne_zero.mpr hne
    have heqz := heqBoundary z hz
    have hfz : f z = h z / (z - c) := by
      field_simp at heqz ⊢
      linear_combination heqz
    have hdslope : dslope h c z = (h z - h c) / (z - c) := by
      rw [dslope_of_ne h hne, slope_def_field]
    simp only [hfz, hdslope]
    field_simp
    ring
  unfold rectangleBoundaryIntegral
  exact
    rectangleBoundaryIntegral_eq_two_pi_I_mul_of_principalParts f (dslope h c) c 0 (h c) hr
      (rectangleBoundaryIntegrable_sub_center_inv_sq_centeredSquare c hr)
      (rectangleBoundaryIntegrable_sub_center_inv_centeredSquare c hr) hgint hgdiff hkernel

/--
A punctured-neighborhood simple-pole identity yields the expected boundary integral on some
positive-radius centered square.

This is the square-contour counterpart of
`PseudoPrime.AnalyticNumberTheory.General.exists_circleIntegral_eq_two_pi_I_mul`.
-/
theorem exists_rectangleBoundaryIntegral_eq_two_pi_I_mul {f h : ℂ → ℂ} {c : ℂ}
    (hh : AnalyticAt ℂ h c)
    (heq : Filter.EventuallyEq (nhdsWithin c ({c}ᶜ : Set ℂ)) (fun z ↦ (z - c) * f z) h) :
    ∃ R : ℝ,
      0 < R ∧
        rectangleBoundaryIntegral f (centeredSquareLower c R) (centeredSquareUpper c R) =
          2 * Real.pi * Complex.I * h c := by
  obtain ⟨R, hR, hforall⟩ := exists_radius_forall_rectangleBoundaryIntegral_eq_two_pi_I_mul hh heq
  exact ⟨R, hR, hforall R hR le_rfl⟩

/--
A punctured-neighborhood double-pole identity yields the expected boundary integral on every
sufficiently small positive-radius centered square.

This is the square-contour counterpart of
`General.exists_radius_forall_circleIntegral_eq_two_pi_I_mul_deriv`.
-/
theorem exists_radius_forall_rectangleBoundaryIntegral_eq_two_pi_I_mul_deriv {f h : ℂ → ℂ} {c : ℂ}
    (hh : AnalyticAt ℂ h c)
    (heq : Filter.EventuallyEq (nhdsWithin c ({c}ᶜ : Set ℂ)) (fun z ↦ (z - c) ^ 2 * f z) h) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ r : ℝ,
          0 < r →
            r ≤ R →
            rectangleBoundaryIntegral f (centeredSquareLower c r) (centeredSquareUpper c r) =
              2 * Real.pi * Complex.I * deriv h c := by
  obtain ⟨rg, hrg, hganalytic⟩ := hh.exists_ball_analyticOnNhd
  have hevent : ∀ᶠ z in nhds c, z ∈ ({c}ᶜ : Set ℂ) → (z - c) ^ 2 * f z = h z :=
    eventuallyEq_nhdsWithin_iff.mp heq
  obtain ⟨re, hre, hball⟩ := Metric.mem_nhds_iff.mp hevent
  set R := min rg re / 2 with hRdef
  have hR : 0 < R := half_pos (lt_min hrg hre)
  have hsqrtlt : Real.sqrt 2 < 2 := by
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num only)
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hsqrt2R : Real.sqrt 2 * R < min rg re := by
    have : Real.sqrt 2 * R < 2 * R := by nlinarith
    rwa [hRdef, show (2 : ℝ) * (min rg re / 2) = min rg re by ring] at this
  refine ⟨R, hR, fun r hr hrR ↦ ?_⟩
  have hsqrt2r : Real.sqrt 2 * r < min rg re :=
    (mul_le_mul_of_nonneg_left hrR (Real.sqrt_nonneg 2)).trans_lt hsqrt2R
  have hsquareSubsetRg :
    Rectangle.rectangleClosedBox (centeredSquareLower c r) (centeredSquareUpper c r) ⊆
      Metric.ball c rg :=
    (centeredSquare_closedRectangle_subset_closedBall c hr.le).trans
      (Metric.closedBall_subset_ball (hsqrt2r.trans_le (min_le_left rg re)))
  have hsquareSubsetRe :
    Rectangle.rectangleClosedBox (centeredSquareLower c r) (centeredSquareUpper c r) ⊆
      Metric.ball c re :=
    (centeredSquare_closedRectangle_subset_closedBall c hr.le).trans
      (Metric.closedBall_subset_ball (hsqrt2r.trans_le (min_le_right rg re)))
  have hboundaryNeC :
    ∀ z ∈ rectangleClosedBoxBoundary (centeredSquareLower c r) (centeredSquareUpper c r),
      z ≠ c := by
    intro z hz hzc
    have hdist := centeredSquare_radius_le_norm_sub_of_mem_boundary hz
    rw [hzc, sub_self, norm_zero] at hdist
    exact absurd hdist (not_le.mpr hr)
  have heqBoundary :
    ∀ z ∈ rectangleClosedBoxBoundary (centeredSquareLower c r) (centeredSquareUpper c r),
      (z - c) ^ 2 * f z = h z :=
    fun z hz ↦ hball (hsquareSubsetRe hz.1) (Set.mem_compl_singleton_iff.mpr (hboundaryNeC z hz))
  have hmemEdge :
    ∀ z : ℂ,
      z.re ∈ Set.uIcc (centeredSquareLower c r).re (centeredSquareUpper c r).re →
        z.im ∈ Set.uIcc (centeredSquareLower c r).im (centeredSquareUpper c r).im →
        ContinuousAt (dslope (dslope h c) c) z := by
    intro z hre him
    have hz :
      z ∈ Rectangle.rectangleClosedBox (centeredSquareLower c r) (centeredSquareUpper c r) :=
      Complex.mem_reProdIm.mpr ⟨hre, him⟩
    rcases eq_or_ne z c with rfl | hne
    · exact (General.AnalyticAt.dslope (General.AnalyticAt.dslope hh)).continuousAt
    · exact
        (continuousAt_dslope_of_ne hne).mpr
          (((differentiableAt_dslope_of_ne hne).mpr
              (hganalytic z (hsquareSubsetRg hz)).differentiableAt)).continuousAt
  have hgint :
    RectangleBoundaryIntegrable (dslope (dslope h c) c) (centeredSquareLower c r)
      (centeredSquareUpper c r) := by
    constructor
    · apply intervalIntegrable_horizontal_of_continuousAt
      intro t ht
      apply hmemEdge
      · simpa only [centeredSquareLower, Complex.add_re, Complex.sub_re, Complex.ofReal_re,
          Complex.mul_re, Complex.I_re, mul_zero, Complex.sub_im, Complex.ofReal_im, sub_self,
          Complex.I_im, mul_one, add_zero, centeredSquareUpper, Complex.add_im, Complex.mul_im,
          zero_add, Complex.ofReal_sub] using ht
      · simp only [centeredSquareLower, Complex.add_im, Complex.sub_im, Complex.ofReal_im, sub_self,
          Complex.mul_im, Complex.sub_re, Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re,
          mul_zero, add_zero, zero_add, centeredSquareUpper, Complex.add_re, Complex.ofReal_sub,
          Set.left_mem_uIcc]
    · apply intervalIntegrable_horizontal_of_continuousAt
      intro t ht
      apply hmemEdge
      · simpa only [centeredSquareLower, Complex.add_re, Complex.sub_re, Complex.ofReal_re,
          Complex.mul_re, Complex.I_re, mul_zero, Complex.sub_im, Complex.ofReal_im, sub_self,
          Complex.I_im, mul_one, add_zero, centeredSquareUpper, Complex.add_im, Complex.mul_im,
          zero_add, Complex.ofReal_add] using ht
      · simp only [centeredSquareLower, Complex.add_im, Complex.sub_im, Complex.ofReal_im, sub_self,
          Complex.mul_im, Complex.sub_re, Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re,
          mul_zero, add_zero, zero_add, centeredSquareUpper, Complex.add_re, Complex.ofReal_add,
          Set.right_mem_uIcc]
    · apply intervalIntegrable_vertical_of_continuousAt
      intro t ht
      apply hmemEdge
      · simp only [centeredSquareLower, Complex.add_re, Complex.sub_re, Complex.ofReal_re,
          Complex.mul_re, Complex.I_re, mul_zero, Complex.sub_im, Complex.ofReal_im, sub_self,
          Complex.I_im, mul_one, add_zero, centeredSquareUpper, Complex.add_im, Complex.ofReal_add,
          Set.right_mem_uIcc]
      · simpa only [centeredSquareLower, Complex.add_im, Complex.sub_im, Complex.ofReal_im,
          sub_self, Complex.mul_im, Complex.sub_re, Complex.ofReal_re, Complex.I_im, mul_one,
          Complex.I_re, mul_zero, add_zero, zero_add, centeredSquareUpper, Complex.add_re,
          Complex.mul_re, Complex.ofReal_add] using ht
    · apply intervalIntegrable_vertical_of_continuousAt
      intro t ht
      apply hmemEdge
      · simp only [centeredSquareLower, Complex.add_re, Complex.sub_re, Complex.ofReal_re,
          Complex.mul_re, Complex.I_re, mul_zero, Complex.sub_im, Complex.ofReal_im, sub_self,
          Complex.I_im, mul_one, add_zero, centeredSquareUpper, Complex.add_im, Complex.ofReal_sub,
          Set.left_mem_uIcc]
      · simpa only [centeredSquareLower, Complex.add_im, Complex.sub_im, Complex.ofReal_im,
          sub_self, Complex.mul_im, Complex.sub_re, Complex.ofReal_re, Complex.I_im, mul_one,
          Complex.I_re, mul_zero, add_zero, zero_add, centeredSquareUpper, Complex.add_re,
          Complex.mul_re, Complex.ofReal_sub] using ht
  have hgdiff :
    DifferentiableOn ℂ (dslope (dslope h c) c)
      (Rectangle.rectangleClosedBox (centeredSquareLower c r) (centeredSquareUpper c r)) := by
    intro z hz
    rcases eq_or_ne z c with rfl | hne
    · exact
        (General.AnalyticAt.dslope
            (General.AnalyticAt.dslope hh)).differentiableAt.differentiableWithinAt
    · exact
        ((differentiableAt_dslope_of_ne hne).mpr
            ((differentiableAt_dslope_of_ne hne).mpr
              (hganalytic z (hsquareSubsetRg hz)).differentiableAt)).differentiableWithinAt
  have hkernel :
    Set.EqOn f (fun z : ℂ ↦ h c * (z - c)⁻¹ ^ 2 + (deriv h c * (z - c)⁻¹ + dslope (dslope h c) c z))
      (Rectangle.rectangleClosedBox (centeredSquareLower c r) (centeredSquareUpper c r) \
        rectangleOpenBox (centeredSquareLower c r) (centeredSquareUpper c r)) := by
    intro z hz
    have hne : z ≠ c := hboundaryNeC z hz
    have hsub : z - c ≠ 0 := sub_ne_zero.mpr hne
    have heqz := heqBoundary z hz
    have hfz : f z = h z / (z - c) ^ 2 := by
      field_simp at heqz ⊢
      linear_combination heqz
    have hk : dslope h c z = (h z - h c) / (z - c) := by rw [dslope_of_ne h hne, slope_def_field]
    have hkc : dslope h c c = deriv h c := dslope_same h c
    have hdslope : dslope (dslope h c) c z = (h z - h c - deriv h c * (z - c)) / (z - c) ^ 2 := by
      rw [dslope_of_ne (dslope h c) hne, slope_def_field, hk, hkc]
      field_simp
    simp only [hfz, hdslope]
    field_simp
    ring
  unfold rectangleBoundaryIntegral
  exact
    rectangleBoundaryIntegral_eq_two_pi_I_mul_of_principalParts f (dslope (dslope h c) c) c (h c)
      (deriv h c) hr (rectangleBoundaryIntegrable_sub_center_inv_sq_centeredSquare c hr)
      (rectangleBoundaryIntegrable_sub_center_inv_centeredSquare c hr) hgint hgdiff hkernel

/--
A cubic punctured-neighborhood identity yields the expected boundary integral on every
sufficiently small positive-radius centered square.  Its coefficient is the central value of the
second divided slope, equivalently half of the regularization's second derivative.
-/
theorem exists_radius_forall_rectangleBoundaryIntegral_eq_two_pi_I_mul_cubic {f h : ℂ → ℂ} {c : ℂ}
    (hh : AnalyticAt ℂ h c)
    (heq : Filter.EventuallyEq (nhdsWithin c ({c}ᶜ : Set ℂ)) (fun z ↦ (z - c) ^ 3 * f z) h) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ r : ℝ,
          0 < r →
            r ≤ R →
            rectangleBoundaryIntegral f (centeredSquareLower c r) (centeredSquareUpper c r) =
              2 * Real.pi * Complex.I * dslope (dslope h c) c c := by
  obtain ⟨rg, hrg, hganalytic⟩ := hh.exists_ball_analyticOnNhd
  have hevent : ∀ᶠ z in nhds c, z ∈ ({c}ᶜ : Set ℂ) → (z - c) ^ 3 * f z = h z :=
    eventuallyEq_nhdsWithin_iff.mp heq
  obtain ⟨re, hre, hball⟩ := Metric.mem_nhds_iff.mp hevent
  set R := min rg re / 2 with hRdef
  have hR : 0 < R := half_pos (lt_min hrg hre)
  have hsqrtlt : Real.sqrt 2 < 2 := by
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num only)
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hsqrt2R : Real.sqrt 2 * R < min rg re := by
    have : Real.sqrt 2 * R < 2 * R := by nlinarith
    rwa [hRdef, show (2 : ℝ) * (min rg re / 2) = min rg re by ring] at this
  refine ⟨R, hR, fun r hr hrR ↦ ?_⟩
  have hsqrt2r : Real.sqrt 2 * r < min rg re :=
    (mul_le_mul_of_nonneg_left hrR (Real.sqrt_nonneg 2)).trans_lt hsqrt2R
  have hsquareSubsetRg :
    Rectangle.rectangleClosedBox (centeredSquareLower c r) (centeredSquareUpper c r) ⊆
      Metric.ball c rg :=
    (centeredSquare_closedRectangle_subset_closedBall c hr.le).trans
      (Metric.closedBall_subset_ball (hsqrt2r.trans_le (min_le_left rg re)))
  have hsquareSubsetRe :
    Rectangle.rectangleClosedBox (centeredSquareLower c r) (centeredSquareUpper c r) ⊆
      Metric.ball c re :=
    (centeredSquare_closedRectangle_subset_closedBall c hr.le).trans
      (Metric.closedBall_subset_ball (hsqrt2r.trans_le (min_le_right rg re)))
  have hboundaryNeC :
    ∀ z ∈ rectangleClosedBoxBoundary (centeredSquareLower c r) (centeredSquareUpper c r),
      z ≠ c := by
    intro z hz hzc
    have hdist := centeredSquare_radius_le_norm_sub_of_mem_boundary hz
    rw [hzc, sub_self, norm_zero] at hdist
    exact absurd hdist (not_le.mpr hr)
  have heqBoundary :
    ∀ z ∈ rectangleClosedBoxBoundary (centeredSquareLower c r) (centeredSquareUpper c r),
      (z - c) ^ 3 * f z = h z :=
    fun z hz ↦ hball (hsquareSubsetRe hz.1) (Set.mem_compl_singleton_iff.mpr (hboundaryNeC z hz))
  have hmemEdge :
    ∀ z : ℂ,
      z.re ∈ Set.uIcc (centeredSquareLower c r).re (centeredSquareUpper c r).re →
        z.im ∈ Set.uIcc (centeredSquareLower c r).im (centeredSquareUpper c r).im →
        ContinuousAt (dslope (dslope (dslope h c) c) c) z := by
    intro z hre him
    have hz :
      z ∈ Rectangle.rectangleClosedBox (centeredSquareLower c r) (centeredSquareUpper c r) :=
      Complex.mem_reProdIm.mpr ⟨hre, him⟩
    rcases eq_or_ne z c with rfl | hne
    · exact (General.analyticAt_dslope_dslope_dslope hh).continuousAt
    · exact
        (continuousAt_dslope_of_ne hne).mpr
          (((differentiableAt_dslope_of_ne hne).mpr
              ((differentiableAt_dslope_of_ne hne).mpr
                (hganalytic z (hsquareSubsetRg hz)).differentiableAt)).continuousAt)
  have hgint :
    RectangleBoundaryIntegrable (dslope (dslope (dslope h c) c) c) (centeredSquareLower c r)
      (centeredSquareUpper c r) := by
    constructor
    · apply intervalIntegrable_horizontal_of_continuousAt
      intro t ht
      apply hmemEdge
      · simpa only [centeredSquareLower, Complex.add_re, Complex.sub_re, Complex.ofReal_re,
          Complex.mul_re, Complex.I_re, mul_zero, Complex.sub_im, Complex.ofReal_im, sub_self,
          Complex.I_im, mul_one, add_zero, centeredSquareUpper, Complex.add_im, Complex.mul_im,
          zero_add, Complex.ofReal_sub] using ht
      · simp only [centeredSquareLower, Complex.add_im, Complex.sub_im, Complex.ofReal_im, sub_self,
          Complex.mul_im, Complex.sub_re, Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re,
          mul_zero, add_zero, zero_add, centeredSquareUpper, Complex.add_re, Complex.ofReal_sub,
          Set.left_mem_uIcc]
    · apply intervalIntegrable_horizontal_of_continuousAt
      intro t ht
      apply hmemEdge
      · simpa only [centeredSquareLower, Complex.add_re, Complex.sub_re, Complex.ofReal_re,
          Complex.mul_re, Complex.I_re, mul_zero, Complex.sub_im, Complex.ofReal_im, sub_self,
          Complex.I_im, mul_one, add_zero, centeredSquareUpper, Complex.add_im, Complex.mul_im,
          zero_add, Complex.ofReal_add] using ht
      · simp only [centeredSquareLower, Complex.add_im, Complex.sub_im, Complex.ofReal_im, sub_self,
          Complex.mul_im, Complex.sub_re, Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re,
          mul_zero, add_zero, zero_add, centeredSquareUpper, Complex.add_re, Complex.ofReal_add,
          Set.right_mem_uIcc]
    · apply intervalIntegrable_vertical_of_continuousAt
      intro t ht
      apply hmemEdge
      · simp only [centeredSquareLower, Complex.add_re, Complex.sub_re, Complex.ofReal_re,
          Complex.mul_re, Complex.I_re, mul_zero, Complex.sub_im, Complex.ofReal_im, sub_self,
          Complex.I_im, mul_one, add_zero, centeredSquareUpper, Complex.add_im, Complex.ofReal_add,
          Set.right_mem_uIcc]
      · simpa only [centeredSquareLower, Complex.add_im, Complex.sub_im, Complex.ofReal_im,
          sub_self, Complex.mul_im, Complex.sub_re, Complex.ofReal_re, Complex.I_im, mul_one,
          Complex.I_re, mul_zero, add_zero, zero_add, centeredSquareUpper, Complex.add_re,
          Complex.mul_re, Complex.ofReal_add] using ht
    · apply intervalIntegrable_vertical_of_continuousAt
      intro t ht
      apply hmemEdge
      · simp only [centeredSquareLower, Complex.add_re, Complex.sub_re, Complex.ofReal_re,
          Complex.mul_re, Complex.I_re, mul_zero, Complex.sub_im, Complex.ofReal_im, sub_self,
          Complex.I_im, mul_one, add_zero, centeredSquareUpper, Complex.add_im, Complex.ofReal_sub,
          Set.left_mem_uIcc]
      · simpa only [centeredSquareLower, Complex.add_im, Complex.sub_im, Complex.ofReal_im,
          sub_self, Complex.mul_im, Complex.sub_re, Complex.ofReal_re, Complex.I_im, mul_one,
          Complex.I_re, mul_zero, add_zero, zero_add, centeredSquareUpper, Complex.add_re,
          Complex.mul_re, Complex.ofReal_sub] using ht
  have hgdiff :
    DifferentiableOn ℂ (dslope (dslope (dslope h c) c) c)
      (Rectangle.rectangleClosedBox (centeredSquareLower c r) (centeredSquareUpper c r)) := by
    intro z hz
    rcases eq_or_ne z c with rfl | hne
    · exact (General.analyticAt_dslope_dslope_dslope hh).differentiableAt.differentiableWithinAt
    · exact
        ((differentiableAt_dslope_of_ne hne).mpr
            ((differentiableAt_dslope_of_ne hne).mpr
              ((differentiableAt_dslope_of_ne hne).mpr
                (hganalytic z (hsquareSubsetRg hz)).differentiableAt))).differentiableWithinAt
  have hkernel :=
    General.eqOn_cubicPrincipalParts_of_mul_eq (f := f) (h := h) (S :=
      Rectangle.rectangleClosedBox (centeredSquareLower c r) (centeredSquareUpper c r) \
        rectangleOpenBox (centeredSquareLower c r) (centeredSquareUpper c r))
      (fun z hz ↦ hboundaryNeC z hz) (fun z hz ↦ heqBoundary z hz)
  unfold rectangleBoundaryIntegral
  exact
    rectangleBoundaryIntegral_eq_two_pi_I_mul_of_cubicPrincipalParts f
      (dslope (dslope (dslope h c) c) c) c (h c) (deriv h c) (dslope (dslope h c) c c) hr
      (rectangleBoundaryIntegrable_sub_center_inv_cube_centeredSquare c hr)
      (rectangleBoundaryIntegrable_sub_center_inv_sq_centeredSquare c hr)
      (rectangleBoundaryIntegrable_sub_center_inv_centeredSquare c hr) hgint hgdiff hkernel

/--
A punctured-neighborhood double-pole identity yields the expected boundary integral on some
positive-radius centered square.

This is the square-contour counterpart of
`PseudoPrime.AnalyticNumberTheory.General.exists_circleIntegral_eq_two_pi_I_mul_deriv`.
-/
theorem exists_rectangleBoundaryIntegral_eq_two_pi_I_mul_deriv {f h : ℂ → ℂ} {c : ℂ}
    (hh : AnalyticAt ℂ h c)
    (heq : Filter.EventuallyEq (nhdsWithin c ({c}ᶜ : Set ℂ)) (fun z ↦ (z - c) ^ 2 * f z) h) :
    ∃ R : ℝ,
      0 < R ∧
        rectangleBoundaryIntegral f (centeredSquareLower c R) (centeredSquareUpper c R) =
          2 * Real.pi * Complex.I * deriv h c := by
  obtain ⟨R, hR, hforall⟩ :=
    exists_radius_forall_rectangleBoundaryIntegral_eq_two_pi_I_mul_deriv hh heq
  exact ⟨R, hR, hforall R hR le_rfl⟩

/-- The boundary of a closed rectangle is closed. -/
theorem isClosed_rectangleClosedBoxBoundary (z w : ℂ) :
    IsClosed (rectangleClosedBoxBoundary z w) := by
  exact (Rectangle.isCompact_rectangleClosedBox z w).isClosed.sdiff (isOpen_Ioo.reProdIm isOpen_Ioo)

/-- The boundary of a closed rectangle contains its first corner. -/
theorem nonempty_rectangleClosedBoxBoundary (z w : ℂ) :
    (rectangleClosedBoxBoundary z w).Nonempty := by
  refine ⟨z, ?_⟩
  rcases le_total z.re w.re with h | h
  · simp only [rectangleClosedBoxBoundary, Rectangle.rectangleClosedBox, Complex.reProdIm, h,
      Set.uIcc_of_le, inf_of_le_left, sup_of_le_right, Set.mem_sdiff, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_Icc, Std.le_refl, and_self, Set.left_mem_uIcc, Set.mem_Ioo,
      lt_self_iff_false, false_and, min_lt_iff, false_or, lt_max_iff, true_and]
    intro hf
    exact hf
  · simp only [rectangleClosedBoxBoundary, Rectangle.rectangleClosedBox, Complex.reProdIm, h,
      Set.uIcc_of_ge, inf_of_le_right, sup_of_le_left, Set.mem_sdiff, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_Icc, Std.le_refl, and_self, Set.left_mem_uIcc, Set.mem_Ioo,
      lt_self_iff_false, and_false, min_lt_iff, false_or, lt_max_iff, true_and, false_and]
    intro hf
    exact hf

/-- Half the distance from a point to the closed rectangle boundary. -/
noncomputable def rectangleClosedBoxBoundaryClearance (s z w : ℂ) : ℝ :=
  Metric.infDist s (rectangleClosedBoxBoundary z w) / 2

/-- A radius bounded by all boundary distances gives a boundary-disjoint closed ball. -/
theorem disjoint_closedBall_rectangleClosedBoxBoundary {z w s : ℂ} {ε : ℝ}
    (hsep : ∀ y ∈ rectangleClosedBoxBoundary z w, ε < dist s y) :
    Disjoint (Metric.closedBall s ε) (rectangleClosedBoxBoundary z w) := by
  rw [Set.disjoint_left]
  intro y hyball hyboundary
  have hyball' : dist s y ≤ ε := by simpa only [Metric.mem_closedBall, dist_comm] using hyball
  exact (not_le_of_gt (hsep y hyboundary)) hyball'

/-- Twice-radius separation gives disjoint closed balls around distinct singularities. -/
theorem disjoint_singularity_closedBalls {s t : ℂ} {ε : ℝ} (hsep : 2 * ε < dist s t) :
    Disjoint (Metric.closedBall s ε) (Metric.closedBall t ε) := by
  apply Metric.closedBall_disjoint_closedBall
  linarith

end PseudoPrime.AnalyticNumberTheory.RectangleGeometry

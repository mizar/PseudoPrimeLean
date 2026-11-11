/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! # Positive kernel for the Gamma-phase remainder -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The periodic quadratic Euler–Maclaurin weight `fract x * (1 - fract x)`.
It is nonnegative and bounded by `1/4`; it weights the Gamma remainder. -/
noncomputable def backlundGammaWeight (x : ℝ) : ℝ :=
  Int.fract x * (1 - Int.fract x)

/-- The rational kernel whose positive weighted integral controls the
imaginary Gamma remainder at `a + iy`. The intended inputs are `a,y > 0`
and integration variable `x ≥ 0`. -/
noncomputable def backlundGammaKernel (a y x : ℝ) : ℝ :=
  y * (x + a) / (((x + a) ^ 2 + y ^ 2) ^ 2)

/-- The periodic quadratic weight lies between zero and `1/4` at every
real point. Its maximum follows from the square of `fract x - 1/2`. -/
theorem backlundGammaWeight_bounds (x : ℝ) :
    0 ≤ backlundGammaWeight x ∧ backlundGammaWeight x ≤ 1 / 4 := by
  dsimp only [backlundGammaWeight]
  have h0 := Int.fract_nonneg x
  have h1 := (Int.fract_lt_one x).le
  constructor
  · exact mul_nonneg h0 (sub_nonneg.mpr h1)
  · nlinarith only [sq_nonneg (Int.fract x - 1 / 2)]

/-- The Euler–Maclaurin weight is measurable and interval integrable on
every finite interval. Its uniform `1/4` bound dominates it by an integrable
constant on the interval. -/
theorem backlundGammaWeight_intervalIntegrable (R : ℝ) :
    IntervalIntegrable backlundGammaWeight MeasureTheory.volume 0 R := by
  have hm : Measurable backlundGammaWeight := by
    exact measurable_fract.mul (measurable_const.sub measurable_fract)
  have hc : IntervalIntegrable (fun _ : ℝ => (1 / 4 : ℝ)) MeasureTheory.volume 0 R :=
    continuous_const.intervalIntegrable 0 R
  apply intervalIntegrable_iff.mpr
  apply (intervalIntegrable_iff.mp hc).mono' hm.aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (backlundGammaWeight_bounds x).1]
  exact (backlundGammaWeight_bounds x).2

/-- At positive height, the rational kernel is continuous on the real line:
its denominator is strictly positive because it contains `y²`. -/
theorem backlundGammaKernel_continuous (a : ℝ) {y : ℝ} (hy : 0 < y) :
    Continuous (backlundGammaKernel a y) := by
  apply
    (continuous_const.mul (continuous_id.add continuous_const)).div₀
      (((continuous_id.add continuous_const).pow 2).add continuous_const |>.pow 2)
  intro x
  exact pow_ne_zero 2 (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hy)).ne'

/-- The rational kernel has the displayed elementary antiderivative at
positive height. Differentiate the inverse quadratic denominator and simplify
the scalar coefficient. -/
theorem backlundGammaKernel_hasDerivAt (a : ℝ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    HasDerivAt (fun t : ℝ => -(y / 2) * (((t + a) ^ 2 + y ^ 2)⁻¹)) (backlundGammaKernel a y x)
      x := by
  have hden : 0 < (x + a) ^ 2 + y ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hy)
  have hd := (((hasDerivAt_id x).add_const a).pow 2).add_const (y ^ 2)
  have hi := (hd.inv hden.ne').const_mul (-(y / 2))
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat] at hi
  have he :
    -(y / 2) * (-(2 * (x + a) ^ (2 - 1) * 1) / ((x + a) ^ 2 + y ^ 2) ^ 2) =
      y * (x + a) / (((x + a) ^ 2 + y ^ 2) ^ 2) := by
    ring
  rw [he] at hi
  exact hi

/-- The integral of the rational kernel over any finite interval from zero
has the exact difference of its antiderivative values. Continuity gives
interval integrability and the fundamental theorem evaluates the integral. -/
theorem backlundGammaKernel_integral (a R : ℝ) {y : ℝ} (hy : 0 < y) :
    (∫ x in (0 : ℝ)..R, backlundGammaKernel a y x) =
      -(y / 2) * (((R + a) ^ 2 + y ^ 2)⁻¹) - (-(y / 2) * ((a ^ 2 + y ^ 2)⁻¹)) := by
  have hc := backlundGammaKernel_continuous a hy
  have h :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => backlundGammaKernel_hasDerivAt a hy x) (hc.intervalIntegrable 0 R)
  simpa only [zero_add] using h

/-- For `a ≥ 0`, `y > 0` and `R ≥ 0`, the weighted kernel integral over
`[0,R]` lies between zero and `y/(8(a²+y²))`. Compare the weight with `1/4`
and use the exact antiderivative of the nonnegative rational kernel. -/
theorem backlundGammaWeight_integral_bounds {a y R : ℝ} (ha : 0 ≤ a) (hy : 0 < y) (hR : 0 ≤ R) :
    0 ≤ (∫ x in (0 : ℝ)..R, backlundGammaWeight x * backlundGammaKernel a y x) ∧
      (∫ x in (0 : ℝ)..R, backlundGammaWeight x * backlundGammaKernel a y x) ≤
        y / (8 * (a ^ 2 + y ^ 2)) := by
  have hk0 : ∀ x ∈ Set.Icc (0 : ℝ) R, 0 ≤ backlundGammaKernel a y x := by
    intro x hx
    apply div_nonneg
    · exact mul_nonneg hy.le (add_nonneg hx.1 ha)
    · exact sq_nonneg _
  have hw :
    IntervalIntegrable (fun x => backlundGammaWeight x * backlundGammaKernel a y x)
      MeasureTheory.volume 0 R :=
    (backlundGammaWeight_intervalIntegrable R).mul_continuousOn
      (backlundGammaKernel_continuous a hy).continuousOn
  have hmaj :
    IntervalIntegrable (fun x => (1 / 4 : ℝ) * backlundGammaKernel a y x) MeasureTheory.volume 0
      R :=
    ((backlundGammaKernel_continuous a hy).intervalIntegrable 0 R).const_mul (1 / 4)
  have hmono :=
    intervalIntegral.integral_mono_on hR hw hmaj
      (fun x hx => mul_le_mul_of_nonneg_right (backlundGammaWeight_bounds x).2 (hk0 x hx))
  have hnonneg : 0 ≤ ∫ x in (0 : ℝ)..R, backlundGammaWeight x * backlundGammaKernel a y x := by
    apply intervalIntegral.integral_nonneg hR
    intro x hx
    exact mul_nonneg (backlundGammaWeight_bounds x).1 (hk0 x hx)
  rw [intervalIntegral.integral_const_mul, backlundGammaKernel_integral a R hy] at hmono
  have hd : 0 ≤ (y / 2) * (((R + a) ^ 2 + y ^ 2)⁻¹) :=
    mul_nonneg (by linarith only [hy]) (inv_nonneg.mpr (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  have hupper :
    (1 / 4 : ℝ) * (-(y / 2) * (((R + a) ^ 2 + y ^ 2)⁻¹) - (-(y / 2) * ((a ^ 2 + y ^ 2)⁻¹))) ≤
      (1 / 4 : ℝ) * (y / 2) * ((a ^ 2 + y ^ 2)⁻¹) := by
    nlinarith only [hd]
  have he : (1 / 4 : ℝ) * (y / 2) * ((a ^ 2 + y ^ 2)⁻¹) = y / (8 * (a ^ 2 + y ^ 2)) := by
    simp only [div_eq_mul_inv, mul_inv]
    norm_num only
    ring
  exact ⟨hnonneg, (hmono.trans hupper).trans_eq he⟩

end PseudoPrime.PrimeTestBounds.MillerRabin

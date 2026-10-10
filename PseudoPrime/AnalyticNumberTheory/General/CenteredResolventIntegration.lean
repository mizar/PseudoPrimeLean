/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.VerticalResolventBounds
public import PseudoPrime.Analysis.IntegralSeries

/-!
# Termwise vertical integration of centered resolvents

Power-weighted pole mass controls the sum of integral norms.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- A pole with nonpositive real part increases the norm distance from a positive
vertical line relative to its imaginary translate. Compare squared norms and use
monotonicity of the square root. This bounds every pole by the same translated profile. -/
theorem norm_vertical_sub_ge {α : ℂ} (hα : α.re ≤ 0) {τ : ℝ} (hτ : 0 < τ) (y : ℝ) :
    ‖(τ : ℂ) + ((y - α.im : ℝ) : ℂ) * Complex.I‖ ≤ ‖(τ : ℂ) + y * Complex.I - α‖ := by
  rw [Complex.norm_def, Complex.norm_def]
  apply Real.sqrt_le_sqrt
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add]
  nlinarith only [mul_nonpos_of_nonneg_of_nonpos hτ.le hα, sq_nonneg α.re]

/-- The kernel `x^z/(α z(z-α))`, where z = τ + i y, defined for complex α and real x,τ,y.
Away from its denominators, it is the centered reciprocal difference
`1/(z-α) + 1/α` multiplied by x^z/z². For Re α < 0, τ > 0, and x > 1,
its normalized vertical integral is `(x^α-1)/α²`. This is the kernel whose pole-mass
bounds permit termwise integration of the zero and gamma expansions. -/
noncomputable def centeredResolventKernel (α : ℂ) (x τ y : ℝ) : ℂ :=
  (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
    (α * ((τ : ℂ) + y * Complex.I) * ((τ : ℂ) + y * Complex.I - α))

/-- For Re α < 0, x > 0 and τ > 0, the centered kernel norm is bounded by
2x^τ/norm(α)^(3/2) times two inverse-three-halves vertical profiles.
Use the reciprocal-product estimate and compare the shifted norm to its imaginary translate.
This is the uniform integral majorant for zero and gamma-pole series. -/
theorem norm_centeredResolventKernel_le {α : ℂ} (hα : α.re < 0) {τ x : ℝ} (hτ : 0 < τ) (hx : 0 < x)
    (y : ℝ) :
    ‖centeredResolventKernel α x τ y‖ ≤
      (2 * x ^ τ / ‖α‖ ^ (3 / 2 : ℝ)) *
        (verticalResolventMajorant τ y + verticalResolventMajorant τ (y - α.im)) := by
  have ha : 0 < ‖α‖ :=
    norm_pos_iff.mpr
      (fun h ↦ by
        rw [h, Complex.zero_re] at hα
        exact lt_irrefl _ hα)
  have hu : 0 < ‖(τ : ℂ) + y * Complex.I‖ :=
    norm_pos_iff.mpr (ne_zero_add_mul_I_of_re_ne_zero hτ.ne' y)
  have hw : 0 < ‖(τ : ℂ) + ((y - α.im : ℝ) : ℂ) * Complex.I‖ :=
    norm_pos_iff.mpr (ne_zero_add_mul_I_of_re_ne_zero hτ.ne' _)
  have hd := norm_vertical_sub_ge hα.le hτ y
  have hv : 0 < ‖(τ : ℂ) + y * Complex.I - α‖ := hw.trans_le hd
  have ht : ‖α‖ ≤ ‖(τ : ℂ) + y * Complex.I‖ + ‖(τ : ℂ) + y * Complex.I - α‖ := by
    have h := norm_sub_le ((τ : ℂ) + y * Complex.I) ((τ : ℂ) + y * Complex.I - α)
    simpa only [sub_sub_cancel] using h
  have hm := resolvent_norm_product_bound ha hu hv ht
  have hp :
    1 / (‖(τ : ℂ) + y * Complex.I - α‖ * Real.sqrt ‖(τ : ℂ) + y * Complex.I - α‖) ≤
      verticalResolventMajorant τ (y - α.im) :=
    div_le_div_of_nonneg_left zero_le_one (mul_pos hw (Real.sqrt_pos.mpr hw))
      (mul_le_mul hd (Real.sqrt_le_sqrt hd) (Real.sqrt_nonneg _) (norm_nonneg _))
  unfold centeredResolventKernel
  rw [norm_div, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, mul_zero, zero_mul, sub_self, add_zero]
  have hs :=
    hm.trans
      (mul_le_mul_of_nonneg_left (add_le_add (le_refl _) hp)
        (div_nonneg zero_le_two (mul_pos ha (Real.sqrt_pos.mpr ha)).le))
  have hb := mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hx.le τ)
  rw [rpow_three_halves_eq ha]
  unfold verticalResolventMajorant at hb ⊢
  convert hb using 1 <;> ring

/-- For a left-half-plane pole and positive x,τ, the centered kernel is integrable.
Its denominator never vanishes on the line and its continuous numerator has constant norm.
The two translated profiles give an integrable majorant, enabling termwise Mellin evaluation. -/
theorem integrable_centeredResolventKernel {α : ℂ} (hα : α.re < 0) {τ x : ℝ} (hτ : 0 < τ)
    (hx : 0 < x) : MeasureTheory.Integrable (centeredResolventKernel α x τ) := by
  have ha : α ≠ 0 := fun h ↦ by
    rw [h, Complex.zero_re] at hα
    exact lt_irrefl _ hα
  have hz : ∀ y : ℝ, (τ : ℂ) + y * Complex.I ≠ 0 := fun y ↦ ne_zero_add_mul_I_of_re_ne_zero hτ.ne' y
  have hd : ∀ y : ℝ, (τ : ℂ) + y * Complex.I - α ≠ 0 := by
    intro y h
    have he := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_self, add_zero,
      Complex.zero_re] at he
    linarith only [he, hτ, hα]
  have hc : Continuous (centeredResolventKernel α x τ) :=
    (continuous_const.cpow (continuous_const.add (Complex.continuous_ofReal.mul_const Complex.I))
          (fun _ ↦ Complex.ofReal_mem_slitPlane.mpr hx)).div
      ((continuous_const.mul
            (continuous_const.add (Complex.continuous_ofReal.mul_const Complex.I))).mul
        ((continuous_const.add (Complex.continuous_ofReal.mul_const Complex.I)).sub
          continuous_const))
      (fun y ↦ mul_ne_zero (mul_ne_zero ha (hz y)) (hd y))
  have hg :=
    ((integrable_verticalResolventMajorant hτ).add
          ((integrable_verticalResolventMajorant hτ).comp_add_right (-α.im))).const_mul
      (2 * x ^ τ / ‖α‖ ^ (3 / 2 : ℝ))
  apply hg.mono' hc.aestronglyMeasurable
  filter_upwards with y
  exact norm_centeredResolventKernel_le hα hτ hx y

/-- For Re α < 0, τ > 0, and x > 0, the integral of the centered kernel's norm is
at most `4 x^τ/norm(α)^(3/2)` times the integral of verticalResolventMajorant τ.
Integrate the two-profile pointwise bound and use translation invariance.
This converts three-halves pole-mass summability into a summable family of norm integrals. -/
theorem integral_norm_centeredResolventKernel_le {α : ℂ} (hα : α.re < 0) {τ x : ℝ} (hτ : 0 < τ)
    (hx : 0 < x) :
    (∫ y : ℝ, ‖centeredResolventKernel α x τ y‖) ≤
      (4 * x ^ τ / ‖α‖ ^ (3 / 2 : ℝ)) * (∫ y : ℝ, verticalResolventMajorant τ y) := by
  have hg :=
    (integrable_verticalResolventMajorant hτ).add
      ((integrable_verticalResolventMajorant hτ).comp_add_right (-α.im))
  have hb :=
    MeasureTheory.integral_mono (integrable_centeredResolventKernel hα hτ hx).norm
      (hg.const_mul (2 * x ^ τ / ‖α‖ ^ (3 / 2 : ℝ))) (norm_centeredResolventKernel_le hα hτ hx)
  simp only [Pi.add_apply] at hb
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_add (integrable_verticalResolventMajorant hτ)
      ((integrable_verticalResolventMajorant hτ).comp_add_right (-α.im)),
    MeasureTheory.integral_add_right_eq_self] at hb
  convert hb using 1
  ring

/-- For any family of poles with Re α_i < 0 and natural multiplicities, assume τ > 0,
x > 0, and summability of `m_i/norm(α_i)^(3/2)`. Then the integrals of the norms
of the multiplicity-weighted centered kernels form a summable family.
Apply the uniform translated-profile bound termwise and scale the mass series.
This supplies the absolute-integrability condition for summation and integration. -/
theorem summable_integral_norm_centeredResolventKernel {ι : Type*} (α : ι → ℂ) (m : ι → ℕ)
    (hα : ∀ i, (α i).re < 0) {τ x : ℝ} (hτ : 0 < τ) (hx : 0 < x)
    (hm : Summable (fun i ↦ (m i : ℝ) / ‖α i‖ ^ (3 / 2 : ℝ))) :
    Summable (fun i ↦ ∫ y : ℝ, ‖(m i : ℂ) * centeredResolventKernel (α i) x τ y‖) := by
  have hs : Summable (fun i ↦ ∫ y : ℝ, ‖(m i : ℂ) * centeredResolventKernel (α i) x τ y‖) := by
    apply
      Summable.of_nonneg_of_le (fun i ↦ MeasureTheory.integral_nonneg (fun _ ↦ norm_nonneg _))
        (fun i ↦ ?_) (hm.mul_left (4 * x ^ τ * ∫ y : ℝ, verticalResolventMajorant τ y))
    rw [show
        (fun y ↦ ‖(m i : ℂ) * centeredResolventKernel (α i) x τ y‖) =
          (fun y ↦ (m i : ℝ) * ‖centeredResolventKernel (α i) x τ y‖)
        from funext (fun y ↦ by rw [norm_mul, Complex.norm_natCast]),
      MeasureTheory.integral_const_mul]
    have hb :=
      mul_le_mul_of_nonneg_left (integral_norm_centeredResolventKernel_le (hα i) hτ hx)
        (Nat.cast_nonneg (m i))
    convert hb using 1
    ring
  exact hs

/-- For any indexed family of left-half-plane poles and natural multiplicities, assume
τ > 0, x > 0, and summable three-halves multiplicity mass. The centered kernel tsum
is integrable over y. Mass summability makes the nonzero-multiplicity support countable;
restrict to it, apply the summable-integral-norm theorem, and extend by zero.
This permits combining the zero and gamma series in the ordinary logarithmic derivative. -/
theorem integrable_tsum_centeredResolventKernel {ι : Type*} (α : ι → ℂ) (m : ι → ℕ)
    (hα : ∀ i, (α i).re < 0) {τ x : ℝ} (hτ : 0 < τ) (hx : 0 < x)
    (hm : Summable (fun i ↦ (m i : ℝ) / ‖α i‖ ^ (3 / 2 : ℝ))) :
    MeasureTheory.Integrable
      (fun y : ℝ ↦ ∑' i, (m i : ℂ) * centeredResolventKernel (α i) x τ y) := by
  let S : Set ι := {i | m i ≠ 0}
  have hS : S.Countable :=
    hm.countable_support.mono
      (by
        intro i hi
        have ha : 0 < ‖α i‖ :=
          norm_pos_iff.mpr
            (fun h ↦ by
              have he := hα i
              rw [h, Complex.zero_re] at he
              exact lt_irrefl _ he)
        exact div_ne_zero (Nat.cast_ne_zero.mpr hi) (Real.rpow_pos_of_pos ha _).ne')
  let : Countable S := hS.to_subtype
  have ht :=
    Analysis.integrable_tsum_of_summable_integral_norm
      (fun i : S ↦ fun y : ℝ ↦ (m i : ℂ) * centeredResolventKernel (α i) x τ y)
      (fun i : S ↦ (integrable_centeredResolventKernel (hα i) hτ hx).const_mul _)
      (summable_integral_norm_centeredResolventKernel (fun i : S ↦ α i) (fun i : S ↦ m i)
        (fun i ↦ hα i) hτ hx (hm.subtype S))
  convert ht using 1
  funext y
  symm
  apply
    tsum_subtype_eq_of_support_subset (s := S) (f := fun i : ι ↦
      (m i : ℂ) * centeredResolventKernel (α i) x τ y)
  intro i hi
  by_contra hn
  have hz : m i = 0 := Classical.not_not.mp hn
  exact hi (by simp only [hz, Nat.cast_zero, zero_mul])

/-- For a countable family of poles with Re α_i < 0, natural multiplicities, τ > 0,
x > 0, and summable `m_i/norm(α_i)^(3/2)`, the vertical integral of the centered
kernel tsum equals the tsum of the individual integrals, weighted by multiplicity.
The uniform integral-norm bound justifies Bochner interchange, then each constant
multiplicity is pulled out. This is the termwise zero and gamma integration interface. -/
theorem integral_tsum_centeredResolventKernel {ι : Type*} [Countable ι] (α : ι → ℂ) (m : ι → ℕ)
    (hα : ∀ i, (α i).re < 0) {τ x : ℝ} (hτ : 0 < τ) (hx : 0 < x)
    (hm : Summable (fun i ↦ (m i : ℝ) / ‖α i‖ ^ (3 / 2 : ℝ))) :
    (∫ y : ℝ, ∑' i, (m i : ℂ) * centeredResolventKernel (α i) x τ y) =
      ∑' i, (m i : ℂ) * (∫ y : ℝ, centeredResolventKernel (α i) x τ y) := by
  have hi :
    ∀ i, MeasureTheory.Integrable (fun y ↦ (m i : ℂ) * centeredResolventKernel (α i) x τ y) :=
    fun i ↦ (integrable_centeredResolventKernel (hα i) hτ hx).const_mul _
  have hs := summable_integral_norm_centeredResolventKernel α m hα hτ hx hm
  rw [← MeasureTheory.integral_tsum_of_summable_integral_norm hi hs]
  exact tsum_congr (fun i ↦ MeasureTheory.integral_const_mul _ _)

end PseudoPrime.AnalyticNumberTheory.General

/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.SecondDerivativeInterpolation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Moment-controlled interpolation for positive cosine integrals -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: real amplitude, frequency and ordinate.
Claim: the cosine weight has the stated derivative.
Proof: chain rule and multiplication by a constant.
Role: establish pointwise curvature before integrating. -/
theorem hasDerivAt_weightedCos (w l t : ℝ) :
    HasDerivAt (fun x : ℝ ↦ w * Real.cos (x * l)) (-w * l * Real.sin (t * l)) t := by
  have h := ((Real.hasDerivAt_cos (t * l)).comp t ((hasDerivAt_id t).mul_const l)).const_mul w
  convert h using 1
  · rfl
  · ring

/-- Input: real amplitude, frequency and ordinate.
Claim: the first cosine derivative has second derivative -w*l^2*cos(t*l).
Proof: chain rule for sine and multiplication by a constant.
Role: bound curvature using a positive frequency moment. -/
theorem hasDerivAt_weightedCosDeriv (w l t : ℝ) :
    HasDerivAt (fun x : ℝ ↦ -w * l * Real.sin (x * l)) (-w * l ^ 2 * Real.cos (t * l)) t := by
  have h :=
    ((Real.hasDerivAt_sin (t * l)).comp t ((hasDerivAt_id t).mul_const l)).const_mul (-w * l)
  convert h using 1
  · rfl
  · ring

/-- Input: nonnegative amplitude and any frequency and interval.
Claim: subtracting w*l^2*t^2/2 from the weighted cosine gives a concave function.
Proof: the cosine second derivative is bounded above by w*l^2.
Role: keep the common density inside the pointwise comparison. -/
theorem concaveOn_weightedCos_quadratic {w : ℝ} (hw : 0 ≤ w) (l a b : ℝ) :
    ConcaveOn ℝ (Set.Icc a b) (fun t ↦ w * Real.cos (t * l) - (w * l ^ 2) / 2 * t ^ 2) := by
  apply
    concaveOn_quadratic_correction_of_second_deriv_le (fun t _ ↦ hasDerivAt_weightedCos w l t)
      (fun t _ ↦ hasDerivAt_weightedCosDeriv w l t)
  intro t _
  have h :=
    mul_le_mul_of_nonneg_left (neg_le_neg (Real.neg_one_le_cos (t * l)))
      (mul_nonneg hw (sq_nonneg l))
  nlinarith only [h]

/-- Input: an integrable amplitude and an almost everywhere strongly measurable frequency.
Claim: the cosine-weighted amplitude is integrable at every ordinate.
Proof: its norm is bounded by the absolute amplitude.
Role: justify integration of pointwise concavity inequalities. -/
theorem integrable_weightedCos {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {w l : α → ℝ} (hw : MeasureTheory.Integrable w μ) (hl : MeasureTheory.AEStronglyMeasurable l μ)
    (t : ℝ) : MeasureTheory.Integrable (fun u ↦ w u * Real.cos (t * l u)) μ := by
  apply
    hw.norm.mono'
      (hw.aestronglyMeasurable.mul (Real.continuous_cos.comp_aestronglyMeasurable (hl.const_mul t)))
  exact
    Filter.Eventually.of_forall
      (fun u ↦ by
        rw [Pi.mul_apply, norm_mul, Real.norm_eq_abs (Real.cos _)]
        exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_cos_le_one _))

/-- Input: an integrable nonnegative density, measurable frequency and integrable second moment.
Claim: the cosine integral minus its second moment times t^2/2 is concave on every interval.
Proof: integrate the pointwise corrected concavity and evaluate the correction integral.
Role: avoid interchanging differentiation and integration in spectral interpolation. -/
theorem concaveOn_cosineIntegral_quadratic {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {w l : α → ℝ} (hw : MeasureTheory.Integrable w μ)
    (hl : MeasureTheory.AEStronglyMeasurable l μ) (hw0 : ∀ᵐ u ∂μ, 0 ≤ w u)
    (hM : MeasureTheory.Integrable (fun u ↦ w u * (l u) ^ 2) μ) (a b : ℝ) :
    ConcaveOn ℝ (Set.Icc a b)
      (fun t ↦ (∫ u, w u * Real.cos (t * l u) ∂μ) - (∫ u, w u * (l u) ^ 2 ∂μ) / 2 * t ^ 2) := by
  have h :=
    MeasureTheory.integral_concaveOn_of_integrand_ae (convex_Icc a b)
      (hw0.mono (fun u hu ↦ concaveOn_weightedCos_quadratic hu (l u) a b))
      (fun t _ ↦ (integrable_weightedCos hw hl t).sub ((hM.div_const 2).mul_const (t ^ 2)))
  have he :
    (fun t ↦ ∫ u, w u * Real.cos (t * l u) - (w u * (l u) ^ 2) / 2 * t ^ 2 ∂μ) =
      (fun t ↦ (∫ u, w u * Real.cos (t * l u) ∂μ) - (∫ u, w u * (l u) ^ 2 ∂μ) / 2 * t ^ 2) := by
    funext t
    rw [MeasureTheory.integral_sub (integrable_weightedCos hw hl t)
        ((hM.div_const 2).mul_const (t ^ 2)),
      MeasureTheory.integral_mul_const, MeasureTheory.integral_div]
  rw [he] at h
  exact h

/-- Input: a concave quadratic correction with nonnegative cost and two lower endpoint values.
Claim: the interval lower bound loses at most M*(b-a)^2/8.
Proof: use the barycentric coordinate in the established chord inequality.
Role: support integral comparisons without derivative hypotheses. -/
theorem lower_bound_on_interval_of_concave_quadratic {f : ℝ → ℝ} {a b M c x : ℝ} (hab : a < b)
    (hM : 0 ≤ M) (hc : ConcaveOn ℝ (Set.Icc a b) (fun t ↦ f t - M / 2 * t ^ 2)) (ha : c ≤ f a)
    (hb : c ≤ f b) (hx : x ∈ Set.Icc a b) : c - M * (b - a) ^ 2 / 8 ≤ f x := by
  have hd : 0 < b - a := sub_pos.mpr hab
  have hu : 0 ≤ (x - a) / (b - a) := div_nonneg (sub_nonneg.mpr hx.1) hd.le
  have hu1 : (x - a) / (b - a) ≤ 1 := (div_le_one₀ hd).mpr (by linarith only [hx.2])
  have he : (1 - (x - a) / (b - a)) * a + (x - a) / (b - a) * b = x := by
    field_simp (discharger := exact hd.ne')
    ring
  simpa only [he] using lower_bound_of_concave_quadratic hab.le hM hc ha hb hu hu1

/-- Input: the positive cosine density hypotheses, a moment cap C, and a comparison function
whose quadratic correction has cost MR, with endpoint gap at least c.
Claim: the whole interval gap is at least c-(MR+C)*(b-a)^2/8.
Proof: add the two concave corrections and apply the chord bound.
Role: turn certified spectral nodes into continuous phase comparisons. -/
theorem cosineIntegral_gap_lower_on_interval {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {w l : α → ℝ} (hw : MeasureTheory.Integrable w μ)
    (hl : MeasureTheory.AEStronglyMeasurable l μ) (hw0 : ∀ᵐ u ∂μ, 0 ≤ w u)
    (hM : MeasureTheory.Integrable (fun u ↦ w u * (l u) ^ 2) μ) {a b MR C c t : ℝ} (hab : a < b)
    (hMR : 0 ≤ MR) {R : ℝ → ℝ} (hR : ConcaveOn ℝ (Set.Icc a b) (fun x ↦ R x - MR / 2 * x ^ 2))
    (hbound : (∫ u, w u * (l u) ^ 2 ∂μ) ≤ C) (ha : c ≤ R a + (∫ u, w u * Real.cos (a * l u) ∂μ))
    (hb : c ≤ R b + (∫ u, w u * Real.cos (b * l u) ∂μ)) (ht : t ∈ Set.Icc a b) :
    c - (MR + C) * (b - a) ^ 2 / 8 ≤ R t + (∫ u, w u * Real.cos (t * l u) ∂μ) := by
  have hc := hR.add (concaveOn_cosineIntegral_quadratic hw hl hw0 hM a b)
  have he :
    (fun x ↦
        (R x - MR / 2 * x ^ 2) +
          ((∫ u, w u * Real.cos (x * l u) ∂μ) - (∫ u, w u * (l u) ^ 2 ∂μ) / 2 * x ^ 2)) =
      (fun x ↦
        (R x + (∫ u, w u * Real.cos (x * l u) ∂μ)) -
          (MR + (∫ u, w u * (l u) ^ 2 ∂μ)) / 2 * x ^ 2) := by
    funext x
    ring
  change
    ConcaveOn ℝ (Set.Icc a b)
      (fun x ↦
        (R x - MR / 2 * x ^ 2) +
          ((∫ u, w u * Real.cos (x * l u) ∂μ) - (∫ u, w u * (l u) ^ 2 ∂μ) / 2 * x ^ 2)) at hc
  rw [he] at hc
  have hmn : 0 ≤ ∫ u, w u * (l u) ^ 2 ∂μ :=
    MeasureTheory.integral_nonneg_of_ae (hw0.mono (fun u hu ↦ mul_nonneg hu (sq_nonneg _)))
  have h := lower_bound_on_interval_of_concave_quadratic hab (add_nonneg hMR hmn) hc ha hb ht
  have hm := mul_le_mul_of_nonneg_right hbound (sq_nonneg (b - a))
  nlinarith only [h, hm]

end PseudoPrime.Analysis

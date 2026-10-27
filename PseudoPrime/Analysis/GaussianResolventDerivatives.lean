/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianResolventCertificate
public import PseudoPrime.Analysis.GaussianGammaNormCurvature
public import PseudoPrime.Analysis.SecondDerivativeInterpolation
public import PseudoPrime.Analysis.ScaledResolventDerivatives

/-! # Uniform curvature of the signed Gaussian resolvent majorant

The fixed rational coefficient certificate bounds the absolute second derivative
of (1+t²)g(t) by 434. The bound applies on the whole real line.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Differentiate a finite list sum termwise. List induction preserves repeated
indices and supplies the derivative sums used by the fixed rational certificate. -/
private theorem hasDerivAt_list_sum {ι : Type} (l : List ι) (f f' : ι → ℝ → ℝ) (t : ℝ)
    (h : ∀ i ∈ l, HasDerivAt (f i) (f' i t) t) :
    HasDerivAt (fun x ↦ (l.map (fun i ↦ f i x)).sum) (l.map (fun i ↦ f' i t)).sum t := by
  induction l with
  | nil => simpa only [List.map_nil, List.sum_nil] using hasDerivAt_const t (0 : ℝ)
  | cons i l ih =>
    have hi := h i (List.mem_cons_self)
    have hl := ih (fun j hj ↦ h j (List.mem_cons_of_mem i hj))
    simpa only [List.map_cons, List.sum_cons] using hi.fun_add hl

/-- The absolute value of a list sum is at most the sum of absolute values.
List induction lets signed resolvent weights contribute only through their magnitudes. -/
private theorem abs_list_sum_le {ι : Type} (l : List ι) (f : ι → ℝ) :
    |(l.map f).sum| ≤ (l.map (fun i ↦ |f i|)).sum := by
  induction l with
  | nil => norm_num only [List.map_nil, List.sum_nil, abs_zero, le_refl]
  | cons i l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (abs_add_le (f i) (l.map f).sum).trans (add_le_add_right ih |f i|)

/-- The signed Gaussian resolvent multiplied by 1+t². Scaling exposes a uniform
curvature bound and preserves the sign of the difference from the Gamma norm. -/
noncomputable def gaussianResolventScaled (t : ℝ) : ℝ :=
  (1 + t ^ 2) * gaussianResolventMajorant t

/-- First derivative of the scaled signed resolvent. Sum the weighted rational
first derivatives at the certificate's positive scales. -/
noncomputable def gaussianResolventScaledDeriv (t : ℝ) : ℝ :=
  (gaussianResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ) * scaledResolventDeriv (ab.1 : ℝ) t)).sum

/-- Second derivative of the scaled signed resolvent. Each signed weight is
retained; absolute weights are used only when bounding the curvature. -/
noncomputable def gaussianResolventScaledSecondDeriv (t : ℝ) : ℝ :=
  (gaussianResolventCoefficients.map
      (fun ab ↦ (ab.2 : ℝ) * scaledResolventSecondDeriv (ab.1 : ℝ) t)).sum

/-- The scaled majorant equals the sum of scaled individual resolvents.
Distribute the positive scaling factor through the finite sum and normalize each term. -/
theorem gaussianResolvent_scaled_eq_sum (t : ℝ) :
    gaussianResolventScaled t =
      (gaussianResolventCoefficients.map
          (fun ab ↦ (ab.2 : ℝ) * scaledResolvent (ab.1 : ℝ) t)).sum := by
  unfold gaussianResolventScaled gaussianResolventMajorant
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro ab _hab
  dsimp only [scaledResolvent]
  ring

/-- The finite rational first-derivative sum differentiates the scaled Gaussian
majorant at every real ordinate. Each scale is positive, so the quotient rule applies. -/
theorem gaussianResolvent_hasDerivAt_scaled (t : ℝ) :
    HasDerivAt gaussianResolventScaled (gaussianResolventScaledDeriv t) t := by
  have h :=
    hasDerivAt_list_sum gaussianResolventCoefficients
      (fun ab x ↦ (ab.2 : ℝ) * scaledResolvent (ab.1 : ℝ) x)
      (fun ab x ↦ (ab.2 : ℝ) * scaledResolventDeriv (ab.1 : ℝ) x) t
  have ha (ab : ℚ × ℚ) (hab : ab ∈ gaussianResolventCoefficients) : 0 < (ab.1 : ℝ) := by
    have hr := List.forall_iff_forall_mem.mp gaussianResolvent_scales_gt_half ab hab
    exact Rat.cast_pos.mpr ((by norm_num only : (0 : ℚ) < 1 / 2).trans hr)
  have hf := h (fun ab hab ↦ (hasDerivAt_scaledResolvent (ha ab hab)).const_mul (ab.2 : ℝ))
  have he :
    gaussianResolventScaled = fun x ↦
      (gaussianResolventCoefficients.map
          (fun ab ↦ (ab.2 : ℝ) * scaledResolvent (ab.1 : ℝ) x)).sum :=
    funext gaussianResolvent_scaled_eq_sum
  rw [he]
  exact hf

/-- The finite rational second-derivative sum differentiates the first sum.
Termwise differentiation supplies actual curvature, rather than an assumed derivative. -/
theorem gaussianResolvent_hasDerivAt_scaledDeriv (t : ℝ) :
    HasDerivAt gaussianResolventScaledDeriv (gaussianResolventScaledSecondDeriv t) t := by
  apply
    hasDerivAt_list_sum gaussianResolventCoefficients
      (fun ab x ↦ (ab.2 : ℝ) * scaledResolventDeriv (ab.1 : ℝ) x)
      (fun ab x ↦ (ab.2 : ℝ) * scaledResolventSecondDeriv (ab.1 : ℝ) x) t
  intro ab hab
  have hr := List.forall_iff_forall_mem.mp gaussianResolvent_scales_gt_half ab hab
  have ha : 0 < (ab.1 : ℝ) := Rat.cast_pos.mpr ((by norm_num only : (0 : ℚ) < 1 / 2).trans hr)
  exact (hasDerivAt_scaledResolventDeriv ha).const_mul (ab.2 : ℝ)

/-- The sum of absolute-weight curvature bounds is strictly below 434.
Exact rational arithmetic verifies the twelve fixed scales and weights. This certificate
bounds the rational part of the compact Gamma comparison. -/
theorem gaussianResolvent_curvature_certificate :
    (gaussianResolventCoefficients.map
          (fun ab ↦ |(ab.2 : ℝ)| * (6 * |1 - (ab.1 : ℝ) ^ 2| / (ab.1 : ℝ) ^ 3))).sum <
      434 := by
  exact gaussianResolvent_scaled_curvature_lt

/-- At every real ordinate, the scaled majorant's absolute second derivative
is below 434. Apply the triangle inequality, the single-resolvent curvature bound,
and the exact finite certificate. -/
theorem gaussianResolvent_abs_scaledSecondDeriv_lt (t : ℝ) :
    |gaussianResolventScaledSecondDeriv t| < 434 := by
  have hs :=
    abs_list_sum_le gaussianResolventCoefficients
      (fun ab ↦ (ab.2 : ℝ) * scaledResolventSecondDeriv (ab.1 : ℝ) t)
  have ht :
    (gaussianResolventCoefficients.map
          (fun ab ↦ |(ab.2 : ℝ) * scaledResolventSecondDeriv (ab.1 : ℝ) t|)).sum ≤
      (gaussianResolventCoefficients.map
          (fun ab ↦ |(ab.2 : ℝ)| * (6 * |1 - (ab.1 : ℝ) ^ 2| / (ab.1 : ℝ) ^ 3))).sum := by
    apply List.sum_le_sum
    intro ab hab
    rw [abs_mul]
    have hr := List.forall_iff_forall_mem.mp gaussianResolvent_scales_gt_half ab hab
    have ha : 0 < (ab.1 : ℝ) := Rat.cast_pos.mpr ((by norm_num only : (0 : ℚ) < 1 / 2).trans hr)
    exact mul_le_mul_of_nonneg_left (abs_scaledResolventSecondDeriv_le ha) (abs_nonneg (ab.2 : ℝ))
  exact (hs.trans ht).trans_lt gaussianResolvent_curvature_certificate

/-- The scaled rational majorant minus the scaled Gaussian Gamma norm.
Its positive sign certifies the desired pointwise domination. -/
noncomputable def gaussianResolventScaledGap (t : ℝ) : ℝ :=
  gaussianResolventScaled t - scaledGaussianGammaNorm t

/-- First derivative of the scaled majorant gap, retaining the signed weights.
It supplies the first interpolation derivative. -/
noncomputable def gaussianResolventScaledGapDeriv (t : ℝ) : ℝ :=
  gaussianResolventScaledDeriv t - scaledGaussianGammaNormDeriv t

/-- Second derivative of the scaled majorant gap. Its upper bound is 474
on the nonnegative half-line, using resolvent curvature 434 and density curvature 40. -/
noncomputable def gaussianResolventScaledGapSecondDeriv (t : ℝ) : ℝ :=
  gaussianResolventScaledSecondDeriv t - scaledGaussianGammaNormSecondDeriv t

/-- The first gap derivative differentiates the actual scaled gap at every height.
Subtract the two previously established derivative theorems. -/
theorem gaussianResolvent_gap_hasDerivAt (t : ℝ) :
    HasDerivAt gaussianResolventScaledGap (gaussianResolventScaledGapDeriv t) t :=
  (gaussianResolvent_hasDerivAt_scaled t).sub (hasDerivAt_scaledGaussianGammaNorm t)

/-- The second gap derivative differentiates the first at every height.
Subtract the two actual second-derivative theorems for interpolation. -/
theorem gaussianResolvent_gapDeriv_hasDerivAt (t : ℝ) :
    HasDerivAt gaussianResolventScaledGapDeriv (gaussianResolventScaledGapSecondDeriv t) t :=
  (gaussianResolvent_hasDerivAt_scaledDeriv t).sub (hasDerivAt_scaledGaussianGammaNormDeriv t)

/-- At nonnegative height, the actual gap second derivative is below 474.
The triangle inequality combines resolvent curvature below 434 with density curvature at most 40. -/
theorem gaussianResolvent_gapSecondDeriv_lt {t : ℝ} (ht : 0 ≤ t) :
    gaussianResolventScaledGapSecondDeriv t < 474 := by
  have h :=
    (abs_sub (gaussianResolventScaledSecondDeriv t) (scaledGaussianGammaNormSecondDeriv t)).trans_lt
      (add_lt_add_of_lt_of_le (gaussianResolvent_abs_scaledSecondDeriv_lt t)
        (abs_scaledGaussianGammaNormSecondDeriv_le_forty ht))
  have h' : |gaussianResolventScaledGapSecondDeriv t| < 474 := by
    norm_num only [gaussianResolventScaledGapSecondDeriv] at h ⊢
    exact h
  exact (le_abs_self _).trans_lt h'

/-- On a nonnegative interval of width at most 1/1000, endpoint gap bounds
9/100000 imply the uniform lower bound 123/4000000. Apply the actual gap derivatives
and the second-derivative interpolation theorem; grid endpoint certification remains separate. -/
theorem gaussianResolvent_gap_ge_of_endpoints {a b t : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hw : b - a ≤ 1 / 1000) (hleft : 9 / 100000 ≤ gaussianResolventScaledGap a)
    (hright : 9 / 100000 ≤ gaussianResolventScaledGap b) (ht : t ∈ Set.Icc a b) :
    123 / 4000000 ≤ gaussianResolventScaledGap t := by
  have h :=
    lower_bound_on_interval_of_second_deriv_le hab (by norm_num only : (0 : ℝ) ≤ 474)
      (fun y _ ↦ gaussianResolvent_gap_hasDerivAt y)
      (fun y _ ↦ gaussianResolvent_gapDeriv_hasDerivAt y)
      (fun y hy ↦ (gaussianResolvent_gapSecondDeriv_lt (ha.trans hy.1)).le) hleft hright ht
  have hs := pow_le_pow_left₀ (sub_pos.mpr hab).le hw 2
  nlinarith only [h, hs]

/-- On a nonnegative interval of width at most 1/1000, the certified endpoint
gaps imply domination of the actual Gaussian kernel norm by the rational majorant.
Use the gap interpolation and cancel the positive factor 1+t². This supplies
the compact pointwise comparison once the grid endpoint bounds are certified. -/
theorem gaussianResolvent_norm_le_of_endpoints {a b t : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hw : b - a ≤ 1 / 1000) (hleft : 9 / 100000 ≤ gaussianResolventScaledGap a)
    (hright : 9 / 100000 ≤ gaussianResolventScaledGap b) (ht : t ∈ Set.Icc a b) :
    ‖gaussianGammaFunction (Complex.I * (t : ℂ))‖ ≤ gaussianResolventMajorant t := by
  have h := gaussianResolvent_gap_ge_of_endpoints ha hab hw hleft hright ht
  have h0 : 0 ≤ gaussianResolventScaledGap t := (by norm_num only : (0 : ℝ) ≤ 123 / 4000000).trans h
  have hb : scaledGaussianGammaNorm t ≤ gaussianResolventScaled t := sub_nonneg.mp h0
  rw [scaledGaussianGammaNorm_eq_kernel_norm] at hb
  exact (mul_le_mul_iff_right₀ (by nlinarith only [sq_nonneg t] : 0 < 1 + t ^ 2)).mp hb

end PseudoPrime.Analysis

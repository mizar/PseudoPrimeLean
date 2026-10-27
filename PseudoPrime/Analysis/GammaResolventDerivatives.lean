/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaResolventCertificate
public import PseudoPrime.Analysis.ScaledResolventDerivatives

/-! # Uniform curvature of the signed Gamma resolvent majorant

The fixed rational coefficient certificate bounds the absolute second derivative
of (1+t²)g(t) by 24. The bound applies on the whole real line.
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

/-- The signed Gamma resolvent multiplied by 1+t². Scaling exposes a uniform
curvature bound and preserves the sign of the difference from the Gamma norm. -/
noncomputable def gammaResolventScaled (t : ℝ) : ℝ :=
  (1 + t ^ 2) * gammaResolventMajorant t

/-- First derivative of the scaled signed resolvent. Sum the weighted rational
first derivatives at the certificate's positive scales. -/
noncomputable def gammaResolventScaledDeriv (t : ℝ) : ℝ :=
  (gammaResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ) * scaledResolventDeriv (ab.1 : ℝ) t)).sum

/-- Second derivative of the scaled signed resolvent. Each signed weight is
retained; absolute weights are used only when bounding the curvature. -/
noncomputable def gammaResolventScaledSecondDeriv (t : ℝ) : ℝ :=
  (gammaResolventCoefficients.map
      (fun ab ↦ (ab.2 : ℝ) * scaledResolventSecondDeriv (ab.1 : ℝ) t)).sum

/-- The scaled majorant equals the sum of scaled individual resolvents.
Distribute the positive scaling factor through the finite sum and normalize each term. -/
theorem gammaResolvent_scaled_eq_sum (t : ℝ) :
    gammaResolventScaled t =
      (gammaResolventCoefficients.map
          (fun ab ↦ (ab.2 : ℝ) * scaledResolvent (ab.1 : ℝ) t)).sum := by
  unfold gammaResolventScaled gammaResolventMajorant
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro ab _hab
  dsimp only [scaledResolvent]
  ring

/-- The finite rational first-derivative sum differentiates the scaled Gamma
majorant at every real ordinate. Each scale is positive, so the quotient rule applies. -/
theorem gammaResolvent_hasDerivAt_scaled (t : ℝ) :
    HasDerivAt gammaResolventScaled (gammaResolventScaledDeriv t) t := by
  have h :=
    hasDerivAt_list_sum gammaResolventCoefficients
      (fun ab x ↦ (ab.2 : ℝ) * scaledResolvent (ab.1 : ℝ) x)
      (fun ab x ↦ (ab.2 : ℝ) * scaledResolventDeriv (ab.1 : ℝ) x) t
  have ha (ab : ℚ × ℚ) (hab : ab ∈ gammaResolventCoefficients) : 0 < (ab.1 : ℝ) := by
    have hr := List.forall_iff_forall_mem.mp gammaResolvent_scales_gt_half ab hab
    exact Rat.cast_pos.mpr ((by norm_num only : (0 : ℚ) < 1 / 2).trans hr)
  have hf := h (fun ab hab ↦ (hasDerivAt_scaledResolvent (ha ab hab)).const_mul (ab.2 : ℝ))
  have he :
    gammaResolventScaled = fun x ↦
      (gammaResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ) * scaledResolvent (ab.1 : ℝ) x)).sum :=
    funext gammaResolvent_scaled_eq_sum
  rw [he]
  exact hf

/-- The finite rational second-derivative sum differentiates the first sum.
Termwise differentiation supplies actual curvature, rather than an assumed derivative. -/
theorem gammaResolvent_hasDerivAt_scaledDeriv (t : ℝ) :
    HasDerivAt gammaResolventScaledDeriv (gammaResolventScaledSecondDeriv t) t := by
  apply
    hasDerivAt_list_sum gammaResolventCoefficients
      (fun ab x ↦ (ab.2 : ℝ) * scaledResolventDeriv (ab.1 : ℝ) x)
      (fun ab x ↦ (ab.2 : ℝ) * scaledResolventSecondDeriv (ab.1 : ℝ) x) t
  intro ab hab
  have hr := List.forall_iff_forall_mem.mp gammaResolvent_scales_gt_half ab hab
  have ha : 0 < (ab.1 : ℝ) := Rat.cast_pos.mpr ((by norm_num only : (0 : ℚ) < 1 / 2).trans hr)
  exact (hasDerivAt_scaledResolventDeriv ha).const_mul (ab.2 : ℝ)

/-- The sum of absolute-weight curvature bounds is strictly below 24.
Exact rational arithmetic verifies the ten fixed scales and weights. This certificate
bounds the rational part of the compact Gamma comparison. -/
theorem gammaResolvent_curvature_certificate :
    (gammaResolventCoefficients.map
          (fun ab ↦ |(ab.2 : ℝ)| * (6 * |1 - (ab.1 : ℝ) ^ 2| / (ab.1 : ℝ) ^ 3))).sum <
      24 := by
  norm_num only [gammaResolventCoefficients, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Rat.cast_div, Rat.cast_natCast, Rat.cast_neg, abs_neg, abs_div, abs_sub, abs_zero]

/-- At every real ordinate, the scaled majorant's absolute second derivative
is below 24. Apply the triangle inequality, the single-resolvent curvature bound,
and the exact finite certificate. -/
theorem gammaResolvent_abs_scaledSecondDeriv_lt (t : ℝ) :
    |gammaResolventScaledSecondDeriv t| < 24 := by
  have hs :=
    abs_list_sum_le gammaResolventCoefficients
      (fun ab ↦ (ab.2 : ℝ) * scaledResolventSecondDeriv (ab.1 : ℝ) t)
  have ht :
    (gammaResolventCoefficients.map
          (fun ab ↦ |(ab.2 : ℝ) * scaledResolventSecondDeriv (ab.1 : ℝ) t|)).sum ≤
      (gammaResolventCoefficients.map
          (fun ab ↦ |(ab.2 : ℝ)| * (6 * |1 - (ab.1 : ℝ) ^ 2| / (ab.1 : ℝ) ^ 3))).sum := by
    apply List.sum_le_sum
    intro ab hab
    rw [abs_mul]
    have hr := List.forall_iff_forall_mem.mp gammaResolvent_scales_gt_half ab hab
    have ha : 0 < (ab.1 : ℝ) := Rat.cast_pos.mpr ((by norm_num only : (0 : ℚ) < 1 / 2).trans hr)
    exact mul_le_mul_of_nonneg_left (abs_scaledResolventSecondDeriv_le ha) (abs_nonneg (ab.2 : ℝ))
  exact (hs.trans ht).trans_lt gammaResolvent_curvature_certificate

end PseudoPrime.Analysis

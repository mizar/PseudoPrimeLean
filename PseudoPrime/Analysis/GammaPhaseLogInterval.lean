/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.SymmetricGammaPhaseInterpolation
public import Mathlib.Analysis.Convex.Deriv

/-! # Continuous log-scale Gamma-phase coverage from two endpoint bounds -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For real constants, compute the derivative of a trigonometric phase
plus a quadratic. Combine the elementary derivative rules with ring normalization.
This provides an explicit first-derivative witness for convexity. -/
theorem hasDerivAt_quadratic_trigonometric (A B t M r : ℝ) :
    HasDerivAt (fun u : ℝ ↦ A * Real.cos (t * u) + B * Real.sin (t * u) + M / 2 * u ^ 2)
      (-A * t * Real.sin (t * r) + B * t * Real.cos (t * r) + M * r) r := by
  have hi := (hasDerivAt_id r).const_mul t
  have hc := ((Real.hasDerivAt_cos (t * r)).comp r hi).const_mul A
  have hs := ((Real.hasDerivAt_sin (t * r)).comp r hi).const_mul B
  have hq := (hasDerivAt_pow 2 r).const_mul (M / 2)
  convert (hc.add hs).add hq using 1 <;> (try rfl); ring

/-- Compute the second derivative through the displayed first-derivative
function. Explicit chain and product rules give minus t^2 times the phase plus M.
This connects a phase envelope to nonnegative curvature. -/
theorem hasDerivAt_quadratic_trigonometric_derivative (A B t M r : ℝ) :
    HasDerivAt (fun u : ℝ ↦ -A * t * Real.sin (t * u) + B * t * Real.cos (t * u) + M * u)
      (-t ^ 2 * (A * Real.cos (t * r) + B * Real.sin (t * r)) + M) r := by
  have hi := (hasDerivAt_id r).const_mul t
  have hs := ((Real.hasDerivAt_sin (t * r)).comp r hi).const_mul (-A * t)
  have hc := ((Real.hasDerivAt_cos (t * r)).comp r hi).const_mul (B * t)
  have hq := (hasDerivAt_id r).const_mul M
  convert (hs.add hc).add hq using 1 <;> (try rfl); ring

/-- If t^2 times the phase is at most M everywhere, adding M*r^2/2
makes the phase convex on the real line. Apply the explicit second-derivative
criterion. This removes the need to certify each interior scale separately. -/
theorem convexOn_quadratic_trigonometric (A B t M : ℝ)
    (hbound : ∀ r : ℝ, t ^ 2 * (A * Real.cos (t * r) + B * Real.sin (t * r)) ≤ M) :
    ConvexOn ℝ Set.univ
      (fun r : ℝ ↦ A * Real.cos (t * r) + B * Real.sin (t * r) + M / 2 * r ^ 2) := by
  apply
    convexOn_of_hasDerivWithinAt2_nonneg convex_univ
      (fun r _ ↦ (hasDerivAt_quadratic_trigonometric A B t M r).continuousAt.continuousWithinAt)
      (fun r _ ↦ (hasDerivAt_quadratic_trigonometric A B t M r).hasDerivWithinAt)
      (fun r _ ↦ (hasDerivAt_quadratic_trigonometric_derivative A B t M r).hasDerivWithinAt)
  intro r _
  linarith only [hbound r]

/-- For a function made convex by adding M*r^2/2, M nonnegative,
and two endpoint caps R, every convex combination is at most R+M*(b-a)^2/8.
Use weighted variance and u*v<=1/4. This generic bound is independent of Gamma. -/
theorem upper_of_quadratic_convex_combination {f : ℝ → ℝ} {M a b R u v : ℝ} (hM : 0 ≤ M)
    (hc : ConvexOn ℝ Set.univ (fun r : ℝ ↦ f r + M / 2 * r ^ 2)) (ha : f a ≤ R) (hb : f b ≤ R)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1) : f (u * a + v * b) ≤ R + M / 8 * (b - a) ^ 2 := by
  have h := hc.2 (Set.mem_univ a) (Set.mem_univ b) hu hv huv
  simp only [smul_eq_mul] at h
  have hfa := mul_le_mul_of_nonneg_left ha hu
  have hfb := mul_le_mul_of_nonneg_left hb hv
  have hsum : (u + v) ^ 2 = 1 := by
    rw [huv]; norm_num only
  have hprod : u * v ≤ 1 / 4 := by nlinarith only [hsum, sq_nonneg (u - v)]
  have hvar : u * a ^ 2 + v * b ^ 2 - (u * a + v * b) ^ 2 = u * v * (b - a) ^ 2 := by
    have he : v = 1 - u := by linarith only [huv]
    rw [he]
    ring
  have hvarle := mul_le_mul_of_nonneg_right hprod (sq_nonneg (b - a))
  have hcost := mul_le_mul_of_nonneg_left hvarle hM
  have hR : u * R + v * R = R := by rw [← add_mul, huv, one_mul]
  have hvarM := congrArg (fun z : ℝ ↦ M * z) hvar
  nlinarith only [h, hfa, hfb, hvarM, hcost, hR]

/-- Under the quadratic convexity and two endpoint cap hypotheses,
every point in the closed interval is at most R+M*(b-a)^2/8. Choose barycentric
weights, treating the degenerate interval separately. This yields continuous coverage. -/
theorem upper_of_quadratic_convex_interval {f : ℝ → ℝ} {M a b R r : ℝ} (hM : 0 ≤ M)
    (hc : ConvexOn ℝ Set.univ (fun u : ℝ ↦ f u + M / 2 * u ^ 2)) (ha : f a ≤ R) (hb : f b ≤ R)
    (har : a ≤ r) (hrb : r ≤ b) : f r ≤ R + M / 8 * (b - a) ^ 2 := by
  by_cases hab : a = b
  · have hr : r = a := le_antisymm (hrb.trans_eq hab.symm) har
    rw [hr, ← hab, sub_self, zero_pow (by norm_num only), mul_zero, add_zero]
    exact ha
  · have hd : 0 < b - a := sub_pos.mpr (lt_of_le_of_ne (har.trans hrb) hab)
    have hu : 0 ≤ (b - r) / (b - a) := div_nonneg (sub_nonneg.mpr hrb) hd.le
    have hv : 0 ≤ (r - a) / (b - a) := div_nonneg (sub_nonneg.mpr har) hd.le
    have hs : (b - r) / (b - a) + (r - a) / (b - a) = 1 := by
      rw [← add_div, sub_add_sub_cancel, div_self hd.ne']
    have hr : (b - r) / (b - a) * a + (r - a) / (b - a) * b = r := by
      field_simp [hd.ne']
      ring
    have h := upper_of_quadratic_convex_combination hM hc ha hb hu hv hs
    rw [hr] at h
    exact h

/-- For every height, adding 5*r^2/(2*(1+t^2)) to the negative Gamma
phase makes it convex in the real logarithmic scale. Expand into sine and cosine,
then use the proved second-height Gamma bound. No finite height grid enters. -/
theorem gammaHalf_quadratic_phase_convex (t : ℝ) :
    ConvexOn ℝ Set.univ
      (fun r : ℝ ↦
        -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) *
                Complex.exp (((t * r : ℝ) : ℂ) * Complex.I)).re +
          (5 / (1 + t ^ 2)) / 2 * r ^ 2) := by
  let G := Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)
  have hbound (r : ℝ) :
    t ^ 2 * (-G.re * Real.cos (t * r) + G.im * Real.sin (t * r)) ≤ 5 / (1 + t ^ 2) := by
    have hr :=
      (neg_le_abs (G * Complex.exp (((t * r : ℝ) : ℂ) * Complex.I)).re).trans
        (Complex.abs_re_le_norm _)
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] at hr
    simp only [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im] at hr
    have hm := mul_le_mul_of_nonneg_left hr (sq_nonneg t)
    have hg := gammaHalf_second_height_le_five_resolvent t
    dsimp only [G] at hm
    linarith only [hm, hg]
  have hc := convexOn_quadratic_trigonometric (-G.re) G.im t (5 / (1 + t ^ 2)) hbound
  convert hc using 1
  funext r
  dsimp only [G]
  simp only [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

/-- Given a positive scale whose logarithm lies between rational endpoints,
and one resolvent majorizing the phase at both endpoints, extend that resolvent
with delta=5*(b-a)^2/16 to majorize the actual phase at every interior scale.
Apply the continuous quadratic envelope and identify the rational extra node. -/
theorem gammaHalf_phase_majorant_on_log_interval {x : ℝ} (hx : 0 < x) (l : List (ℚ × ℚ)) (a b : ℚ)
    (har : (a : ℝ) ≤ Real.log x) (hrb : Real.log x ≤ (b : ℝ))
    (ha :
      ∀ t : ℝ,
        -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) *
                Complex.exp (((t * a : ℝ) : ℂ) * Complex.I)).re ≤
          finiteSignedResolvent l t)
    (hb :
      ∀ t : ℝ,
        -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) *
                Complex.exp (((t * b : ℝ) : ℂ) * Complex.I)).re ≤
          finiteSignedResolvent l t)
    (t : ℝ) :
    -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re ≤
      finiteSignedResolvent (logarithmicPhaseExtension l ((5 / 16) * (b - a) ^ 2)) t := by
  have hM : 0 ≤ (5 : ℝ) / (1 + t ^ 2) :=
    div_nonneg (by norm_num only) (by nlinarith only [sq_nonneg t])
  have hi :=
    upper_of_quadratic_convex_interval hM (gammaHalf_quadratic_phase_convex t) (ha t) (hb t) har hrb
  rw [imaginary_power_eq_phase hx, mul_comm Complex.I ((t * Real.log x : ℝ) : ℂ),
    finiteSignedResolvent_logarithmicPhaseExtension]
  norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_sub, Rat.cast_ofNat]
  have he :
    2 * (5 / 16 * ((b : ℝ) - a) ^ 2) / (1 + t ^ 2) = (5 / (1 + t ^ 2)) / 8 * ((b : ℝ) - a) ^ 2 := by
    ring
  rw [he]
  exact hi

end PseudoPrime.Analysis

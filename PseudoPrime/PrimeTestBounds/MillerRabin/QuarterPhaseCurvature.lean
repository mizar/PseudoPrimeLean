/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! # Endpoint lower bounds from curvature for logarithmic phase sums -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A twice differentiable function with second derivative bounded above by `M`
lies above its smaller endpoint value minus the quadratic interpolation error.
Adding the quadratic correction makes the function concave on the interval. -/
theorem phase_lower_of_curvature {f f' f'' : ℝ → ℝ} {a b x M : ℝ} (hx : x ∈ Set.Icc a b)
    (hM : 0 ≤ M) (hf : ContinuousOn f (Set.Icc a b)) (hd : ∀ t ∈ Set.Ioo a b, HasDerivAt f (f' t) t)
    (hdd : ∀ t ∈ Set.Ioo a b, HasDerivAt f' (f'' t) t) (hcurv : ∀ t ∈ Set.Ioo a b, f'' t ≤ M) :
    min (f a) (f b) - M * (b - a) ^ 2 / 8 ≤ f x := by
  let g (t : ℝ) := f t + M / 2 * ((t - a) * (b - t))
  let g' (t : ℝ) := f' t + M / 2 * (a + b - 2 * t)
  have hcorr (t : ℝ) :
    HasDerivAt (fun y : ℝ ↦ M / 2 * ((y - a) * (b - y))) (M / 2 * (a + b - 2 * t)) t := by
    convert
      (((hasDerivAt_id t).sub_const a).mul ((hasDerivAt_id t).const_sub b)).const_mul (M / 2) using
      1
    · funext y
      simp only [Pi.mul_apply, id_eq]
    · simp only [id_eq]
      ring
  have hcg : ContinuousOn g (Set.Icc a b) := hf.add (by fun_prop)
  have hg : ConcaveOn ℝ (Set.Icc a b) g := by
    apply
      concaveOn_of_hasDerivWithinAt2_nonpos (f' := g') (f'' := fun t ↦ f'' t - M) (convex_Icc a b)
        hcg
    · intro t ht
      rw [interior_Icc] at ht
      exact ((hd t ht).add (hcorr t)).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have hc := (((hasDerivAt_id t).const_mul 2).const_sub (a + b)).const_mul (M / 2)
      apply HasDerivAt.hasDerivWithinAt
      convert (hdd t ht).add hc using 1
      · funext y
        simp only [Pi.add_apply, id_eq, g']
      · ring
    · intro t ht
      rw [interior_Icc] at ht
      exact sub_nonpos.mpr (hcurv t ht)
  have hab : a ≤ b := hx.1.trans hx.2
  have hgx := hg.min_le_of_mem_Icc (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab) hx
  have hquad : (x - a) * (b - x) ≤ (b - a) ^ 2 / 4 := by nlinarith only [sq_nonneg (2 * x - a - b)]
  have hp := mul_le_mul_of_nonneg_left hquad (div_nonneg hM (by norm_num only : (0 : ℝ) ≤ 2))
  dsimp only [g] at hgx
  simp only [sub_self, zero_mul, mul_zero, add_zero] at hgx
  linarith only [hgx, hp]

/-- The curvature error on `[2 log l, 2 log u]` is at most
`M (u-l)^2 / (2 l^2)`. This estimates the logarithmic interval length by
`2 (u-l)/l` and transfers the endpoint bounds to every radius in `[l,u]`. -/
theorem log_phase_lower_of_curvature {f f' f'' : ℝ → ℝ} {l r u M : ℝ} (hl : 0 < l)
    (hr : r ∈ Set.Icc l u) (hM : 0 ≤ M)
    (hf : ContinuousOn f (Set.Icc (2 * Real.log l) (2 * Real.log u)))
    (hd : ∀ t ∈ Set.Ioo (2 * Real.log l) (2 * Real.log u), HasDerivAt f (f' t) t)
    (hdd : ∀ t ∈ Set.Ioo (2 * Real.log l) (2 * Real.log u), HasDerivAt f' (f'' t) t)
    (hcurv : ∀ t ∈ Set.Ioo (2 * Real.log l) (2 * Real.log u), f'' t ≤ M) :
    min (f (2 * Real.log l)) (f (2 * Real.log u)) - M * (u - l) ^ 2 / (2 * l ^ 2) ≤
      f (2 * Real.log r) := by
  have hu := hl.trans_le (hr.1.trans hr.2)
  have hh := Real.log_le_sub_one_of_pos (div_pos hu hl)
  rw [Real.log_div hu.ne' hl.ne',
    show u / l - 1 = (u - l) / l by rw [sub_div, div_self hl.ne']] at hh
  have hlog := Real.log_le_log hl (hr.1.trans hr.2)
  have hsq :=
    pow_le_pow_left₀ (show 0 ≤ 2 * Real.log u - 2 * Real.log l by linarith only [hlog])
      (show 2 * Real.log u - 2 * Real.log l ≤ 2 * ((u - l) / l) by linarith only [hh]) 2
  have he :=
    phase_lower_of_curvature (x := 2 * Real.log r)
      ⟨by linarith only [Real.log_le_log hl hr.1], by
        linarith only [Real.log_le_log (hl.trans_le hr.1) hr.2]⟩
      hM hf hd hdd hcurv
  have hc := mul_le_mul_of_nonneg_left hsq (div_nonneg hM (by norm_num only : (0 : ℝ) ≤ 8))
  have hEq : (M / 8) * (2 * ((u - l) / l)) ^ 2 = M * (u - l) ^ 2 / (2 * l ^ 2) := by ring
  rw [hEq] at hc
  linarith only [he, hc]

/-- The derivative of one real Fourier term has the same frequency with
rotated coefficients, scaled by that frequency. -/
private theorem phase_term_deriv (A B g d t : ℝ) :
    HasDerivAt (fun x : ℝ ↦ A * Real.cos (g * (x + d)) + B * Real.sin (g * (x + d)))
      ((g * B) * Real.cos (g * (t + d)) + (-g * A) * Real.sin (g * (t + d))) t := by
  have h := ((hasDerivAt_id t).add_const d).const_mul g
  convert (h.cos.const_mul A).add (h.sin.const_mul B) using 1
  · funext x
    simp only [Pi.add_apply, id_eq]
  · simp only [id_eq]
    ring

/-- Freeze a finite set of zero frequencies, phase shifts, and real sine and cosine coefficients.
An upper bound on the sum of squared frequencies times absolute coefficients
is a curvature bound. The endpoint estimates then give a bound for every
logarithmic phase in the radius interval. -/
theorem finite_phase_lower {ι : Type*} (s : Finset ι) (A B γ d : ι → ℝ) {l r u M : ℝ} (hl : 0 < l)
    (hr : r ∈ Set.Icc l u) (hM : ∑ j ∈ s, (γ j) ^ 2 * (|A j| + |B j|) ≤ M) :
    let Z (t : ℝ) := ∑ j ∈ s, (A j * Real.cos (γ j * (t + d j)) + B j * Real.sin (γ j * (t + d j)))
    min (Z (2 * Real.log l)) (Z (2 * Real.log u)) - M * (u - l) ^ 2 / (2 * l ^ 2) ≤
      Z (2 * Real.log r) := by
  intro Z
  let W (t : ℝ) :=
    ∑ j ∈ s, ((γ j * B j) * Real.cos (γ j * (t + d j)) + (-γ j * A j) * Real.sin (γ j * (t + d j)))
  let V (t : ℝ) :=
    ∑ j ∈ s, (-(γ j) ^ 2 * (A j * Real.cos (γ j * (t + d j)) + B j * Real.sin (γ j * (t + d j))))
  have hZ (t : ℝ) : HasDerivAt Z (W t) t :=
    HasDerivAt.fun_sum (fun j _ ↦ phase_term_deriv (A j) (B j) (γ j) (d j) t)
  have hW (t : ℝ) : HasDerivAt W (V t) t := by
    apply HasDerivAt.fun_sum
    intro j _
    convert phase_term_deriv (γ j * B j) (-γ j * A j) (γ j) (d j) t using 1
    ring
  have hc (t : ℝ) : V t ≤ M := by
    refine (Finset.sum_le_sum ?_).trans hM
    intro j _
    have ha :=
      (abs_mul (A j) (Real.cos (γ j * (t + d j)))).le.trans
        ((mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)).trans_eq (mul_one _))
    have hb :=
      (abs_mul (B j) (Real.sin (γ j * (t + d j)))).le.trans
        ((mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)).trans_eq (mul_one _))
    rw [neg_mul, ← mul_neg]
    exact
      mul_le_mul_of_nonneg_left ((neg_le_abs _).trans ((abs_add_le _ _).trans (add_le_add ha hb)))
        (sq_nonneg (γ j))
  have hM0 :=
    (Finset.sum_nonneg fun j (_ : j ∈ s) ↦
          mul_nonneg (sq_nonneg (γ j)) (add_nonneg (abs_nonneg _) (abs_nonneg _))).trans
      hM
  exact
    log_phase_lower_of_curvature hl hr hM0 (fun t _ ↦ (hZ t).continuousAt.continuousWithinAt)
      (fun t _ ↦ hZ t) (fun t _ ↦ hW t) (fun t _ ↦ hc t)

end PseudoPrime.PrimeTestBounds.MillerRabin

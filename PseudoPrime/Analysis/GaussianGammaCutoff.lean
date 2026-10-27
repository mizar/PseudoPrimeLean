/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianGammaProfile
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Gaussian Gamma cutoff integrals -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The logarithmic Gaussian density times exp(v/2)(1-exp(-l exp(-v))).
The cutoff l and shift v determine the integrated smoothing density.
It is the one-variable integrand used by the rational cutoff certificate. -/
noncomputable def gaussianGammaCutoffIntegrand (l v : ℝ) : ℝ :=
  normalizedGaussianWeight v * Real.exp (v / 2) * (1 - Real.exp (-l * Real.exp (-v)))

/-- Clamp the real argument to the nonnegative half line. On every finite
interval, the half Gaussian moment dominates the resulting product integrand.
This provides absolute integrability for the cutoff Fubini exchange. -/
private theorem integrable_gaussianGammaProfileIntegrand_clamped_prod (a b : ℝ) :
    MeasureTheory.Integrable (fun z : ℝ × ℝ ↦ gaussianGammaProfileIntegrand (max 0 z.1) z.2)
      ((MeasureTheory.volume.restrict (Set.uIoc a b)).prod MeasureTheory.volume) := by
  let : MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict (Set.uIoc a b)) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr
      (measure_Ioc_lt_top (μ := MeasureTheory.volume) (a := min a b) (b := max a b)).ne
  have hc : Continuous (fun z : ℝ × ℝ ↦ gaussianGammaProfileIntegrand (max 0 z.1) z.2) :=
    ((continuous_normalizedGaussianWeight.comp continuous_snd).mul
          (Real.continuous_exp.comp (continuous_const.mul continuous_snd))).mul
      (Real.continuous_exp.comp
        ((continuous_const.max continuous_fst).neg.mul
          (Real.continuous_exp.comp continuous_snd.neg)))
  apply
    ((integrable_normalizedGaussian_mul_exp (-(1 / 2 : ℝ))).comp_snd
          (MeasureTheory.volume.restrict (Set.uIoc a b))).mono'
      hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs, abs_of_pos (gaussianGammaProfileIntegrand_pos _ _)]
  exact gaussianGammaProfileIntegrand_le (le_max_left 0 z.1) z.2

/-- At positive decay rate r, the finite exponential integral equals
(1-exp(-lr))/r. Rescale the elementary exponential antiderivative.
This evaluates the inner integral in the Gaussian cutoff exchange. -/
private theorem integral_exp_neg_mul_interval (l r : ℝ) (hr : 0 < r) :
    (∫ u in (0 : ℝ)..l, Real.exp (-u * r)) = (1 - Real.exp (-l * r)) / r := by
  have he : (fun u : ℝ ↦ Real.exp (-u * r)) = (fun u : ℝ ↦ Real.exp ((-r) * u)) := by
    funext u
    congr 1
    ring
  rw [he, intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr hr.ne'), integral_exp]
  simp only [mul_zero, Real.exp_zero, smul_eq_mul, inv_neg, neg_mul, div_eq_mul_inv]
  rw [mul_comm r l]
  ring

/-- For every cutoff l and shift v, integrating the smoothing density in u
gives the cutoff integrand. Evaluate the exponential integral and combine
the reciprocal exponential with the half moment. This supplies the Fubini endpoint. -/
theorem integral_gaussianGammaProfileIntegrand_interval (l v : ℝ) :
    (∫ u in (0 : ℝ)..l, gaussianGammaProfileIntegrand u v) = gaussianGammaCutoffIntegrand l v := by
  simp only [gaussianGammaProfileIntegrand, gaussianGammaCutoffIntegrand]
  rw [intervalIntegral.integral_const_mul, integral_exp_neg_mul_interval l _ (Real.exp_pos _)]
  have he : Real.exp (-(1 / 2 : ℝ) * v) / Real.exp (-v) = Real.exp (v / 2) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [div_eq_mul_inv] at he
  calc
    _ =
        normalizedGaussianWeight v * (Real.exp (-(1 / 2 : ℝ) * v) * (Real.exp (-v))⁻¹) *
          (1 - Real.exp (-l * Real.exp (-v))) :=
      by ring
    _ = _ := by rw [he]

/-- For a nonnegative cutoff, exchange the smoothing integral with the finite
u-integral. The clamped product is absolutely integrable and agrees with the
original density on the interval. This connects cutoff mass to one real integral. -/
theorem integral_gaussianGammaProfile_average_interval {l : ℝ} (hl : 0 ≤ l) :
    (∫ u in (0 : ℝ)..l, ∫ v : ℝ, gaussianGammaProfileIntegrand u v) =
      ∫ v : ℝ, gaussianGammaCutoffIntegrand l v := by
  calc
    _ = ∫ u in (0 : ℝ)..l, ∫ v : ℝ, gaussianGammaProfileIntegrand (max 0 u) v := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le hl] at hu
      simp only [max_eq_right hu.1]
    _ = ∫ v : ℝ, ∫ u in (0 : ℝ)..l, gaussianGammaProfileIntegrand (max 0 u) v :=
      MeasureTheory.intervalIntegral_integral_swap
        (integrable_gaussianGammaProfileIntegrand_clamped_prod 0 l)
    _ = _ := by
      apply MeasureTheory.integral_congr_ae
      apply Filter.Eventually.of_forall
      intro v
      calc
        _ = ∫ u in (0 : ℝ)..l, gaussianGammaProfileIntegrand u v := by
          apply intervalIntegral.integral_congr
          intro u hu
          rw [Set.uIcc_of_le hl] at hu
          simp only [max_eq_right hu.1]
        _ = _ := integral_gaussianGammaProfileIntegrand_interval l v

/-- For a nonnegative cutoff, the profile divided by sqrt(u) has the Gaussian
cutoff integrand as its integral. Cancel sqrt(u) away from the zero endpoint
and apply the absolutely integrable Fubini exchange. This is the certificate interface. -/
theorem integral_gaussianGammaProfile_div_sqrt {l : ℝ} (hl : 0 ≤ l) :
    (∫ u in (0 : ℝ)..l, gaussianGammaProfile u / Real.sqrt u) =
      ∫ v : ℝ, gaussianGammaCutoffIntegrand l v := by
  calc
    _ = ∫ u in (0 : ℝ)..l, ∫ v : ℝ, gaussianGammaProfileIntegrand u v := by
      apply intervalIntegral.integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u hu
      rw [Set.uIoc_of_le hl] at hu
      simp only [gaussianGammaProfile, mul_div_cancel_left₀ _ (Real.sqrt_pos.mpr hu.1).ne']
    _ = _ := integral_gaussianGammaProfile_average_interval hl

/-- At a nonnegative cutoff, the one-variable cutoff density is nonnegative.
The remaining exponential is at most one. This allows tails to be omitted
when proving a lower bound from a finite integration interval. -/
theorem gaussianGammaCutoffIntegrand_nonneg {l : ℝ} (hl : 0 ≤ l) (v : ℝ) :
    0 ≤ gaussianGammaCutoffIntegrand l v := by
  apply mul_nonneg (mul_pos (normalizedGaussianWeight_pos v) (Real.exp_pos _)).le
  apply sub_nonneg.mpr
  exact
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hl) (Real.exp_pos _).le)

/-- At a nonnegative cutoff, the cutoff density is absolutely integrable.
Its norm is bounded by the positive half Gaussian moment integrand.
This validates finite-interval lower bounds without any tail assumption. -/
theorem integrable_gaussianGammaCutoffIntegrand {l : ℝ} (hl : 0 ≤ l) :
    MeasureTheory.Integrable (gaussianGammaCutoffIntegrand l) := by
  have hc : Continuous (gaussianGammaCutoffIntegrand l) :=
    (continuous_normalizedGaussianWeight.mul
          (Real.continuous_exp.comp (continuous_id.div_const 2))).mul
      (continuous_const.sub
        (Real.continuous_exp.comp
          (continuous_const.mul (Real.continuous_exp.comp continuous_id.neg))))
  apply (integrable_normalizedGaussian_mul_exp (1 / 2)).mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro v
  rw [Real.norm_eq_abs, abs_of_nonneg (gaussianGammaCutoffIntegrand_nonneg hl v),
    gaussianGammaCutoffIntegrand]
  have he : (1 / 2 : ℝ) * v = v / 2 := by ring
  rw [he]
  exact
    mul_le_of_le_one_right (mul_pos (normalizedGaussianWeight_pos v) (Real.exp_pos _)).le
      (sub_le_self 1 (Real.exp_pos _).le)

/-- At nonnegative cutoff l and ordered endpoints a,b, the finite density integral
is at most the full profile cutoff mass. Absolute integrability and nonnegative
tails justify restriction. This supplies the interval certificate's lower-bound interface. -/
theorem gaussianGammaCutoff_interval_le_mass {l a b : ℝ} (hl : 0 ≤ l) (hab : a ≤ b) :
    (∫ v in a..b, gaussianGammaCutoffIntegrand l v) ≤
      ∫ u in (0 : ℝ)..l, gaussianGammaProfile u / Real.sqrt u := by
  rw [integral_gaussianGammaProfile_div_sqrt hl, intervalIntegral.integral_of_le hab]
  exact
    MeasureTheory.setIntegral_le_integral (integrable_gaussianGammaCutoffIntegrand hl)
      (Filter.Eventually.of_forall (gaussianGammaCutoffIntegrand_nonneg hl))

end PseudoPrime.Analysis

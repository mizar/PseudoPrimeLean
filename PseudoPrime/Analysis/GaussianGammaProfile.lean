/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianMoments

/-! # Positive logarithmic Gaussian smoothing of the Gamma density -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The normalized Gaussian times exp(-v/2)exp(-u exp(-v)).
The real argument u and logarithmic shift v define the smoothing integrand.
Its positive integrable average gives the inverse-transform profile. -/
noncomputable def gaussianGammaProfileIntegrand (u v : ℝ) : ℝ :=
  normalizedGaussianWeight v * Real.exp (-(1 / 2 : ℝ) * v) * Real.exp (-u * Real.exp (-v))

/-- For each real u the profile integrand is continuous in the shift.
Products and compositions of exponential functions preserve continuity.
This supplies measurability for its Bochner integral. -/
theorem continuous_gaussianGammaProfileIntegrand (u : ℝ) :
    Continuous (gaussianGammaProfileIntegrand u) := by
  exact
    (continuous_normalizedGaussianWeight.mul
          (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul
      (Real.continuous_exp.comp (continuous_const.mul (Real.continuous_exp.comp continuous_id.neg)))

/-- The integrand is strictly positive for every real argument and shift.
All three factors are positive. This proves positivity of the inverse profile. -/
theorem gaussianGammaProfileIntegrand_pos (u v : ℝ) : 0 < gaussianGammaProfileIntegrand u v := by
  exact mul_pos (mul_pos (normalizedGaussianWeight_pos v) (Real.exp_pos _)) (Real.exp_pos _)

/-- For u>=0 the integrand is bounded by the half Gaussian moment integrand.
The last exponential is at most one. This gives an integrable majorant. -/
theorem gaussianGammaProfileIntegrand_le {u : ℝ} (hu : 0 ≤ u) (v : ℝ) :
    gaussianGammaProfileIntegrand u v ≤
      normalizedGaussianWeight v * Real.exp (-(1 / 2 : ℝ) * v) := by
  have he : Real.exp (-u * Real.exp (-v)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu) (Real.exp_pos _).le)
  exact mul_le_of_le_one_right (mul_pos (normalizedGaussianWeight_pos v) (Real.exp_pos _)).le he

/-- For each nonnegative u the smoothing integrand is absolutely integrable.
Use continuity and dominate its norm by the integrable half Gaussian moment.
This validates the profile average and its integral comparisons. -/
theorem integrable_gaussianGammaProfileIntegrand {u : ℝ} (hu : 0 ≤ u) :
    MeasureTheory.Integrable (gaussianGammaProfileIntegrand u) := by
  apply
    (integrable_normalizedGaussian_mul_exp (-(1 / 2 : ℝ))).mono'
      (continuous_gaussianGammaProfileIntegrand u).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro v
  rw [Real.norm_eq_abs, abs_of_pos (gaussianGammaProfileIntegrand_pos u v)]
  exact gaussianGammaProfileIntegrand_le hu v

/-- An integrable profile integrand has strictly positive integral.
Pointwise positivity makes its support the whole real line of positive measure.
This supplies the strict positivity of the inverse-transform profile. -/
theorem integral_gaussianGammaProfileIntegrand_pos (u : ℝ)
    (hi : MeasureTheory.Integrable (gaussianGammaProfileIntegrand u)) :
    0 < ∫ v : ℝ, gaussianGammaProfileIntegrand u v := by
  apply
    (MeasureTheory.integral_pos_iff_support_of_nonneg
        (fun v ↦ (gaussianGammaProfileIntegrand_pos u v).le) hi).mpr
  have hs : Function.support (gaussianGammaProfileIntegrand u) = Set.univ := by
    ext v
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (gaussianGammaProfileIntegrand_pos u v).ne'
  rw [hs, Real.volume_univ]
  exact ENNReal.zero_lt_top

/-- The positive real density proposed for Gaussian Gamma Mellin inversion.
For nonnegative u it is sqrt(u) times the logarithmic Gaussian average of
exp(-v/2)exp(-u exp(-v)). It supplies the P2 inverse transform. -/
noncomputable def gaussianGammaProfile (u : ℝ) : ℝ :=
  Real.sqrt u * ∫ v : ℝ, gaussianGammaProfileIntegrand u v

/-- At a positive argument, the Gaussian Gamma profile is strictly positive.
Its square-root factor and its integrable average are positive. This proves
the positivity required by the Mellin-kernel interface. -/
theorem gaussianGammaProfile_pos {u : ℝ} (hu : 0 < u) : 0 < gaussianGammaProfile u := by
  exact
    mul_pos (Real.sqrt_pos.mpr hu)
      (integral_gaussianGammaProfileIntegrand_pos u
        (integrable_gaussianGammaProfileIntegrand hu.le))

/-- At every nonnegative argument, the profile is at most sqrt(u)exp(1/16).
Drop the exponential factor bounded by one and evaluate the half Gaussian
moment. This controls the profile at the lower integration endpoint. -/
theorem gaussianGammaProfile_le {u : ℝ} (hu : 0 ≤ u) :
    gaussianGammaProfile u ≤ Real.sqrt u * Real.exp (1 / 16 : ℝ) := by
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg u)
  have h :=
    MeasureTheory.integral_mono (integrable_gaussianGammaProfileIntegrand hu)
      (integrable_normalizedGaussian_mul_exp (-(1 / 2 : ℝ))) (gaussianGammaProfileIntegrand_le hu)
  rw [integral_normalizedGaussian_mul_exp] at h
  norm_num only at h
  exact h

end PseudoPrime.Analysis

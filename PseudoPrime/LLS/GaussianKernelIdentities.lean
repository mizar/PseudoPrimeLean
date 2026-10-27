/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaKernelIdentities
public import PseudoPrime.Analysis.GaussianGammaKernel
public import PseudoPrime.Analysis.GaussianGammaProfile
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Gaussian Gamma inversion by an absolutely integrable logarithmic mixture -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The joint Gaussian-shift and vertical Gamma inversion integrand.
The real inputs are the line, positive argument, shift and height. Its norm
separates into a Gaussian moment and a Gamma inversion norm for Fubini. -/
noncomputable def gaussianInverseJoint (c u : ℝ) (v t : ℝ) : ℂ :=
  (Analysis.normalizedGaussianWeight v : ℂ) *
    Complex.exp (((c : ℂ) + Complex.I * (t : ℂ)) * (v : ℂ)) *
    (Complex.Gamma ((c : ℂ) + Complex.I * (t : ℂ) + 1 / 2) *
      (u : ℂ) ^ (-((c : ℂ) + Complex.I * (t : ℂ))))

/-- The joint norm separates into two nonnegative one-variable factors.
Compute the real part of the Gaussian exponential. This gives the integrable
product majorant used to interchange logarithmic smoothing and inversion. -/
theorem norm_gaussianInverseJoint (c u v t : ℝ) :
    ‖gaussianInverseJoint c u v t‖ =
      Analysis.normalizedGaussianWeight v * Real.exp (c * v) *
        ‖Complex.Gamma ((c : ℂ) + Complex.I * (t : ℂ) + 1 / 2) *
            (u : ℂ) ^ (-((c : ℂ) + Complex.I * (t : ℂ)))‖ := by
  rw [gaussianInverseJoint, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Analysis.normalizedGaussianWeight_pos v), Complex.norm_exp]
  congr 2
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, zero_add]

/-- For c>-1/2 and u>0 the joint integrand is measurable for product volume.
Its Gaussian factor is continuous, while the Gamma inversion factor is
absolutely integrable and hence measurable. This is the Fubini measurability gate. -/
theorem measurable_gaussianInverseJoint {c u : ℝ} (hc : -(1 : ℝ) / 2 < c) (hu : 0 < u) :
    MeasureTheory.AEStronglyMeasurable (Function.uncurry (gaussianInverseJoint c u))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  have hcont :
    Continuous
      (fun z : ℝ × ℝ ↦
        (Analysis.normalizedGaussianWeight z.1 : ℂ) *
          Complex.exp (((c : ℂ) + Complex.I * (z.2 : ℂ)) * (z.1 : ℂ))) :=
    ((Complex.continuous_ofReal.comp
          (Analysis.continuous_normalizedGaussianWeight.comp continuous_fst)).mul
      (Complex.continuous_exp.comp
        ((continuous_const.add
              (continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd))).mul
          (Complex.continuous_ofReal.comp continuous_fst))))
  exact
    hcont.aestronglyMeasurable.mul
      (integrable_inverseMellin_gamma hc hu).aestronglyMeasurable.comp_snd

/-- The measurable joint integrand is absolutely integrable when c>-1/2, u>0.
Its exact norm is the product of two integrable one-variable functions.
This permits exchanging Gaussian averaging and inverse Mellin integration. -/
theorem integrable_gaussianInverseJoint_of_measurable {c u : ℝ} (hc : -(1 : ℝ) / 2 < c) (hu : 0 < u)
    (hm :
      MeasureTheory.AEStronglyMeasurable (Function.uncurry (gaussianInverseJoint c u))
        (MeasureTheory.volume.prod MeasureTheory.volume)) :
    MeasureTheory.Integrable (Function.uncurry (gaussianInverseJoint c u))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  apply
    ((Analysis.integrable_normalizedGaussian_mul_exp c).mul_prod
          (integrable_inverseMellin_gamma hc hu).norm).mono'
      hm
  apply Filter.Eventually.of_forall
  intro z
  exact (norm_gaussianInverseJoint c u z.1 z.2).le

/-- Averaging the joint integrand in the shift gives Gaussian Gamma inversion.
Evaluate the complex Gaussian moment and rearrange the fixed factors.
This identifies the first iterated integral in the Fubini identity. -/
theorem integral_gaussianInverseJoint_left (c u t : ℝ) :
    (∫ v : ℝ, gaussianInverseJoint c u v t) =
      Complex.Gamma ((c : ℂ) + Complex.I * (t : ℂ) + 1 / 2) *
        Complex.exp (((c : ℂ) + Complex.I * (t : ℂ)) ^ 2 / 4) *
        (u : ℂ) ^ (-((c : ℂ) + Complex.I * (t : ℂ))) := by
  simp only [gaussianInverseJoint, MeasureTheory.integral_mul_const,
    Analysis.integral_normalizedGaussian_mul_cexp]
  ring

/-- At positive u, multiplying u^(-s) by exp(sv) replaces u by u exp(-v).
Expand positive-base complex powers through real logarithms and add the
exponents. This transports the shift into the Gamma inverse transform. -/
theorem gaussian_cpow_scale {u : ℝ} (hu : 0 < u) (v : ℝ) (s : ℂ) :
    Complex.exp (s * (v : ℂ)) * (u : ℂ) ^ (-s) = ((u * Real.exp (-v) : ℝ) : ℂ) ^ (-s) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (mul_pos hu (Real.exp_pos _)).ne'), ←
    Complex.exp_add, ← Complex.ofReal_log hu.le, ←
    Complex.ofReal_log (mul_pos hu (Real.exp_pos _)).le, Real.log_mul hu.ne' (Real.exp_ne_zero _),
    Real.log_exp, Complex.ofReal_add, Complex.ofReal_neg]
  congr 1
  ring

/-- Inverting at a fixed shift gives the Gaussian-weighted Gamma density.
Transport the positive argument to u exp(-v) and apply the existing Gamma
inverse Mellin theorem. This identifies the second iterated integral. -/
theorem integral_gaussianInverseJoint_right {c u : ℝ} (hc : -(1 : ℝ) / 2 < c) (hu : 0 < u) (v : ℝ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, gaussianInverseJoint c u v t) =
      (Analysis.normalizedGaussianWeight v : ℂ) *
        (Real.sqrt (u * Real.exp (-v)) * Real.exp (-(u * Real.exp (-v))) : ℝ) := by
  have he :
    (fun t : ℝ ↦ gaussianInverseJoint c u v t) =
      (fun t : ℝ ↦
        (Analysis.normalizedGaussianWeight v : ℂ) *
          (Complex.Gamma ((c : ℂ) + Complex.I * (t : ℂ) + 1 / 2) *
            ((u * Real.exp (-v) : ℝ) : ℂ) ^ (-((c : ℂ) + Complex.I * (t : ℂ))))) := by
    funext t
    rw [gaussianInverseJoint, ← gaussian_cpow_scale hu]
    ring
  rw [he, MeasureTheory.integral_const_mul]
  have h := inverseMellin_gamma hc (mul_pos hu (Real.exp_pos (-v)))
  unfold inverseMellin at h
  rw [← mul_assoc, mul_comm ((1 / (2 * Real.pi) : ℝ) : ℂ), mul_assoc, h]

/-- For every c>-1/2 and u>0 Gaussian Gamma inversion is a real positive mixture.
The joint integrand is absolutely integrable, so Fubini exchanges the Gaussian
moment with Gamma inversion. This establishes inversion without an added assumption. -/
theorem inverseMellin_gaussianGamma_average {c u : ℝ} (hc : -(1 : ℝ) / 2 < c) (hu : 0 < u) :
    inverseMellin Analysis.gaussianGammaFunction c u =
      ∫ v : ℝ,
        (Analysis.normalizedGaussianWeight v : ℂ) *
          (Real.sqrt (u * Real.exp (-v)) * Real.exp (-(u * Real.exp (-v))) : ℝ) := by
  have hi :=
    integrable_gaussianInverseJoint_of_measurable hc hu (measurable_gaussianInverseJoint hc hu)
  have he :
    (fun t : ℝ ↦
        Analysis.gaussianGammaFunction ((c : ℂ) + Complex.I * (t : ℂ)) *
          (u : ℂ) ^ (-((c : ℂ) + Complex.I * (t : ℂ)))) =
      (fun t : ℝ ↦ ∫ v : ℝ, gaussianInverseJoint c u v t) := by
    funext t
    exact (integral_gaussianInverseJoint_left c u t).symm
  unfold inverseMellin
  rw [he, ← MeasureTheory.integral_integral_swap hi, ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall (integral_gaussianInverseJoint_right hc hu)

/-- At positive u the shifted Gamma density integrand equals sqrt(u) times
the profile integrand. The square root of exp(-v) is exp(-v/2).
This identifies the real Gaussian mixture with the normalized inverse profile. -/
theorem gaussian_density_profile_integrand {u : ℝ} (hu : 0 < u) (v : ℝ) :
    Analysis.normalizedGaussianWeight v *
        (Real.sqrt (u * Real.exp (-v)) * Real.exp (-(u * Real.exp (-v)))) =
      Real.sqrt u * Analysis.gaussianGammaProfileIntegrand u v := by
  rw [Real.sqrt_mul hu.le, Real.sqrt_eq_rpow (Real.exp (-v)), ← Real.exp_mul]
  have he : -v * (1 / 2 : ℝ) = -(1 / 2 : ℝ) * v := by ring
  rw [he, Analysis.gaussianGammaProfileIntegrand]
  simp only [neg_mul, mul_assoc, mul_left_comm]

/-- At positive u, the Gaussian density average is the normalized profile.
Identify the real integrands and extract sqrt(u) from the integral.
This transfers positivity from the real profile to Mellin inversion. -/
theorem gaussian_density_average_eq_profile {u : ℝ} (hu : 0 < u) :
    (∫ v : ℝ,
        (Analysis.normalizedGaussianWeight v : ℂ) *
          (Real.sqrt (u * Real.exp (-v)) * Real.exp (-(u * Real.exp (-v))) : ℝ)) =
      (Analysis.gaussianGammaProfile u : ℂ) := by
  simp only [← Complex.ofReal_mul, integral_complex_ofReal]
  congr 1
  rw [Analysis.gaussianGammaProfile, ← MeasureTheory.integral_const_mul]
  exact
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (gaussian_density_profile_integrand hu))

/-- For c>-1/2 and u>0 the Gaussian Gamma inverse Mellin transform is the
positive real profile. Combine the absolutely convergent mixture identity
with its real normalization. This supplies line independence and positivity. -/
theorem inverseMellin_gaussianGamma {c u : ℝ} (hc : -(1 : ℝ) / 2 < c) (hu : 0 < u) :
    inverseMellin Analysis.gaussianGammaFunction c u = (Analysis.gaussianGammaProfile u : ℂ) :=
  (inverseMellin_gaussianGamma_average hc hu).trans (gaussian_density_average_eq_profile hu)

/-- The Gaussian inverse Mellin integrand is absolutely integrable for c>-1/2,
u>0. Fubini's integrable marginal and the complex moment identity identify
the integrand. This is the integrability field of the admissible kernel. -/
theorem integrable_inverseMellin_gaussianGamma {c u : ℝ} (hc : -(1 : ℝ) / 2 < c) (hu : 0 < u) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        Analysis.gaussianGammaFunction ((c : ℂ) + Complex.I * (t : ℂ)) *
          (u : ℂ) ^ (-((c : ℂ) + Complex.I * (t : ℂ)))) := by
  have hi :=
    integrable_gaussianInverseJoint_of_measurable hc hu (measurable_gaussianInverseJoint hc hu)
  apply hi.integral_prod_right.congr
  exact Filter.Eventually.of_forall (fun t ↦ integral_gaussianInverseJoint_left c u t)

end PseudoPrime.LLS.PaperStatements

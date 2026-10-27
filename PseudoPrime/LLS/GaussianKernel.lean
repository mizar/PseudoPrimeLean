/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaKernel
public import PseudoPrime.LLS.GaussianKernelIdentities
public import PseudoPrime.Analysis.GaussianGammaCutoff
public import PseudoPrime.Analysis.GaussianGammaCutoffQuadrature
public import PseudoPrime.Analysis.GaussianGammaCutoffLowerBound
public import PseudoPrime.Analysis.GaussianGammaCutoffSixFifths

/-! # The admissible Gaussian Gamma Mellin kernel with tau = 1/4 -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The Gaussian multiplier is holomorphic at every complex input.
The exponential of the polynomial s²/4 is differentiable everywhere.
This preserves holomorphy and regularization of the Gamma kernel. -/
theorem gaussian_multiplier_differentiable :
    Differentiable ℂ (fun s : ℂ ↦ Complex.exp (s ^ 2 / 4)) :=
  Complex.differentiable_exp.comp ((differentiable_id.pow 2).div_const _)

/-- In the open Gamma strip the squared real part is at most 9/16.
The product (re(s)+3/4)(3/4-re(s)) is nonnegative. This gives a uniform
Gaussian multiplier bound needed for the kernel decay condition. -/
theorem gaussian_strip_re_sq_le {s : ℂ} (hs : -(3 : ℝ) / 4 < s.re ∧ s.re < 3 / 4) :
    s.re ^ 2 ≤ 9 / 16 := by
  have h :=
    mul_nonneg (by linarith only [hs.1] : 0 ≤ s.re + 3 / 4)
      (by linarith only [hs.2] : 0 ≤ 3 / 4 - s.re)
  nlinarith only [h]

/-- The Gaussian multiplier is at most exp(9/64) throughout the Gamma strip.
Use its norm bound and the real-part square bound. This preserves the existing
quadratic decay estimate away from the Gamma pole. -/
theorem gaussian_multiplier_strip_le {s : ℂ} (hs : s ∈ gammaMellinKernel.region) :
    ‖Complex.exp (s ^ 2 / 4)‖ ≤ Real.exp (9 / 64 : ℝ) := by
  apply (Analysis.norm_gaussian_multiplier_le s).trans
  apply Real.exp_le_exp.mpr
  have h := gaussian_strip_re_sq_le hs
  linarith only [h]

/-- At positive distance from the Gamma pole the Gaussian Gamma kernel has
uniform quadratic decay in the Gamma strip. Multiply the existing Gamma
decay bound by the bounded Gaussian multiplier. This is kernel admissibility. -/
theorem gaussianGamma_strip_decay {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ s ∈ gammaMellinKernel.region,
          η ≤ ‖s + 1 / 2‖ → ‖Analysis.gaussianGammaFunction s‖ ≤ C / (1 + ‖s‖ ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := gammaMellinKernel.decay η hη
  refine ⟨C * Real.exp (9 / 64), mul_pos hC (Real.exp_pos _), ?_⟩
  intro s hs hd
  rw [Analysis.gaussianGammaFunction, norm_mul]
  have h :=
    mul_le_mul (hbound s hs hd) (gaussian_multiplier_strip_le hs) (norm_nonneg _)
      (div_nonneg hC.le (add_nonneg zero_le_one (sq_nonneg ‖s‖)))
  simpa only [gammaMellinKernel, div_mul_eq_mul_div] using h

/-- The admissible fixed kernel Gamma(s+1/2)exp(s²/4), with strip width 1/8.
It retains the Gamma pole regularization and quadratic strip decay. Its inverse
transform is the strictly positive real Gaussian profile, obtained by Fubini.
This kernel supplies the general comparison interface for the P2 refinements. -/
noncomputable def gaussianGammaMellinKernel : MellinKernel := by
  exact
    { function := Analysis.gaussianGammaFunction
      delta := gammaMellinKernel.delta
      delta_pos := gammaMellinKernel.delta_pos
      region := gammaMellinKernel.region
      region_open := gammaMellinKernel.region_open
      strip_subset := gammaMellinKernel.strip_subset
      holomorphic := by
        intro s hs
        change
          DifferentiableWithinAt ℂ (fun z ↦ Complex.Gamma (z + 1 / 2) * Complex.exp (z ^ 2 / 4))
            (gammaMellinKernel.region \ {(-1 / 2 : ℂ)}) s
        simpa only [gammaMellinKernel, Pi.mul_def] using
          (gammaMellinKernel.holomorphic s hs).mul
            (gaussian_multiplier_differentiable s).differentiableWithinAt
      regularized := fun s ↦ gammaMellinKernel.regularized s * Complex.exp (s ^ 2 / 4)
      regularized_holomorphic := fun s hs ↦
        (gammaMellinKernel.regularized_holomorphic s hs).mul
          (gaussian_multiplier_differentiable s).differentiableWithinAt
      regularized_eq := by
        intro s hs hn
        rw [gammaMellinKernel.regularized_eq s hs hn]
        simp only [gammaMellinKernel, Analysis.gaussianGammaFunction, mul_assoc]
      decay := fun η hη ↦ gaussianGamma_strip_decay hη
      mellin_integrable := fun c u hc _ hu ↦ integrable_inverseMellin_gaussianGamma hc hu
      mellin_eq := fun c u hc _ hu ↦
        (inverseMellin_gaussianGamma hc hu).trans
          (inverseMellin_gaussianGamma (by norm_num only) hu).symm
      mellin_nonneg := by
        intro u hu
        rw [inverseMellin_gaussianGamma (by norm_num only) hu, Complex.ofReal_re]
        exact (Analysis.gaussianGammaProfile_pos hu).le
      mellin_nonzero := by
        refine ⟨1, zero_lt_one, ?_⟩
        rw [inverseMellin_gaussianGamma (by norm_num only) zero_lt_one, Complex.ofReal_re]
        exact (Analysis.gaussianGammaProfile_pos zero_lt_one).ne'
      mellin_real := by
        intro u hu
        rw [inverseMellin_gaussianGamma (by norm_num only) hu, Complex.ofReal_im] }

/-- For positive u, the admissible kernel transform is the real Gaussian profile.
Use the proved inverse Mellin identity on the central line. This identifies
the integrand used by finite sums and cutoff-mass comparisons. -/
theorem gaussianGamma_transform {u : ℝ} (hu : 0 < u) :
    gaussianGammaMellinKernel.transform u = (Analysis.gaussianGammaProfile u : ℂ) := by
  exact inverseMellin_gaussianGamma (by norm_num only) hu

/-- The Gaussian kernel mass is the Gamma norm integral with damping exp(-t²/4).
Use the exact central-line norm and the definition of kernel mass.
This fixes the true mass normalization; it does not assert a resolvent majorant certificate. -/
theorem gaussianGamma_mass :
    gaussianGammaMellinKernel.mass =
      (∫ t : ℝ, ‖Complex.Gamma (Complex.I * (t : ℂ) + 1 / 2)‖ * Real.exp (-(t ^ 2) / 4)) /
        (2 * Real.pi) := by
  unfold MellinKernel.mass
  congr 1
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  simp only [gaussianGammaMellinKernel, Analysis.norm_gaussianGammaFunction, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    one_mul, mul_zero, zero_add, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_sub]

/-- The admissible kernel endpoint obeys the rational bound 2129/2000.
Its function is the fixed Gaussian Gamma function. This transfers the proved
Taylor certificate into the subgroup comparison denominator. -/
theorem gaussianGamma_kernel_endpoint_le :
    (gaussianGammaMellinKernel.function (1 / 2)).re ≤ 2129 / 2000 :=
  Analysis.gaussianGammaFunction_endpoint_le

/-- At every nonnegative cutoff l, the actual Mellin transform cutoff mass
equals the one-variable logarithmic Gaussian density integral. The inverse
transform and absolutely integrable Fubini exchange identify the certificate input. -/
theorem gaussianGamma_cutoff_integral {l : ℝ} (hl : 0 ≤ l) :
    (∫ u in (0 : ℝ)..l, (gaussianGammaMellinKernel.transform u).re / Real.sqrt u) =
      ∫ v : ℝ, Analysis.gaussianGammaCutoffIntegrand l v := by
  calc
    _ = ∫ u in (0 : ℝ)..l, Analysis.gaussianGammaProfile u / Real.sqrt u := by
      apply intervalIntegral.integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u hu
      rw [Set.uIoc_of_le hl] at hu
      simp only [gaussianGamma_transform hu.1, Complex.ofReal_re]
    _ = _ := Analysis.integral_gaussianGammaProfile_div_sqrt hl

/-- For nonnegative cutoff and ordered endpoints, the finite Gaussian density
integral is a lower bound for the actual kernel cutoff mass. The cutoff identity
and nonnegative integrable tails justify the restriction used by the certificate. -/
theorem gaussianGamma_cutoff_interval_le {l a b : ℝ} (hl : 0 ≤ l) (hab : a ≤ b) :
    (∫ v in a..b, Analysis.gaussianGammaCutoffIntegrand l v) ≤
      ∫ u in (0 : ℝ)..l, (gaussianGammaMellinKernel.transform u).re / Real.sqrt u := by
  rw [gaussianGamma_cutoff_integral hl, intervalIntegral.integral_of_le hab]
  exact
    MeasureTheory.setIntegral_le_integral (Analysis.integrable_gaussianGammaCutoffIntegrand hl)
      (Filter.Eventually.of_forall (Analysis.gaussianGammaCutoffIntegrand_nonneg hl))

/-- The actual Gaussian Mellin kernel cutoff at 21/10 is bounded below by the
16,000-cell midpoint sum minus its proven error 97/12000000. The cutoff identity
transfers the analytic density estimate. This leaves only finite node arithmetic. -/
theorem gaussianGamma_cutoff_midpoint_16000_lower :
    (1 / 2000 : ℝ) *
          (∑ k ∈ Finset.range 16000,
            Analysis.gaussianGammaCutoffIntegrand (21 / 10) (-4 + ((k : ℝ) + 1 / 2) * (1 / 2000))) -
        97 / 12000000 ≤
      ∫ u in (0 : ℝ)..(21 / 10), (gaussianGammaMellinKernel.transform u).re / Real.sqrt u := by
  rw [gaussianGamma_cutoff_integral (by norm_num only), ←
    Analysis.integral_gaussianGammaProfile_div_sqrt (by norm_num only)]
  exact Analysis.gaussianGammaCutoff_midpoint_16000_lower

/-- The actual Gaussian Mellin cutoff mass at 21/10 exceeds 81470555/100000000.
Transfer the proved profile lower bound through the cutoff identity.
This eliminates the previously explicit integral premise from the P2 denominator. -/
theorem gaussianGamma_cutoff_gt_target :
    (81470555 / 100000000 : ℝ) <
      ∫ u in (0 : ℝ)..(21 / 10), (gaussianGammaMellinKernel.transform u).re / Real.sqrt u := by
  rw [gaussianGamma_cutoff_integral (by norm_num only), ←
    Analysis.integral_gaussianGammaProfile_div_sqrt (by norm_num only)]
  exact Analysis.gaussianGammaCutoff_mass_gt_target

/-- The actual Gaussian Mellin cutoff mass at 6/5 exceeds 16/25.
Transfer the 128-node kernel-checked profile certificate through the cutoff identity.
This supplies the improved mass input for the 6/5 witness branch. -/
theorem gaussianGamma_cutoff_sixFifths_gt_target :
    (16 / 25 : ℝ) <
      ∫ u in (0 : ℝ)..(6 / 5), (gaussianGammaMellinKernel.transform u).re / Real.sqrt u := by
  rw [gaussianGamma_cutoff_integral (by norm_num only), ←
    Analysis.integral_gaussianGammaProfile_div_sqrt (by norm_num only)]
  exact Analysis.gaussianGammaCutoffSixFifths_mass_gt

end PseudoPrime.LLS.PaperStatements

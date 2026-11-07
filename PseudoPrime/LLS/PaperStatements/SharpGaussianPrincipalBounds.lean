/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.SharpLogWeightedCutoff
public import PseudoPrime.LLS.PaperStatements.GaussianPrincipalMixture
public import PseudoPrime.Analysis.GaussianGammaCutoff

/-! # Sharp finite Gaussian principal lower bound -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Gaussian-weighted endpoint density at cutoff ratio `l` and logarithmic shift `v`.
Its integral weights the endpoint contribution in the averaged finite Gamma sum. -/
noncomputable def gaussianEndpointDensity (l v : ℝ) : ℝ :=
  Analysis.normalizedGaussianWeight v * Real.exp (-(3 / 2 : ℝ) * v) * Real.exp (-l * Real.exp (-v))

/-- For a nonnegative cutoff ratio, the endpoint density is integrable.
Dominate its positive factor by a Gaussian exponential moment. -/
theorem integrable_gaussianEndpointDensity {l : ℝ} (hl : 0 ≤ l) :
    MeasureTheory.Integrable (gaussianEndpointDensity l) := by
  have hc : Continuous (gaussianEndpointDensity l) :=
    (Analysis.continuous_normalizedGaussianWeight.mul
          (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul
      (Real.continuous_exp.comp (continuous_const.mul (Real.continuous_exp.comp continuous_id.neg)))
  apply
    (Analysis.integrable_normalizedGaussian_mul_exp (-(3 / 2 : ℝ))).mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro v
  have hp : 0 < gaussianEndpointDensity l v := by
    exact
      mul_pos (mul_pos (Analysis.normalizedGaussianWeight_pos v) (Real.exp_pos _)) (Real.exp_pos _)
  rw [Real.norm_eq_abs, abs_of_pos hp, gaussianEndpointDensity]
  have he : Real.exp (-l * Real.exp (-v)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hl) (Real.exp_pos _).le)
  exact
    mul_le_of_le_one_right (mul_pos (Analysis.normalizedGaussianWeight_pos v) (Real.exp_pos _)).le
      he

/-- Pointwise Gaussian average of the sharp finite Gamma lower envelope.
The Chebyshev deficit and weighted-Mangoldt error use the fixed cutoff `l * x`.
Its integral supplies a lower bound for the actual finite Gaussian principal sum. -/
noncomputable def gaussianSharpLowerEnvelope (x l v : ℝ) : ℝ :=
  Real.sqrt x * Analysis.gaussianGammaCutoffIntegrand l v -
    ((l * x - Chebyshev.psi (l * x)) / Real.sqrt x) * Analysis.gaussianGammaProfileIntegrand l v -
    (((231 / 5000 : ℝ) * Real.sqrt (l * x) + (1839 / 1000 : ℝ) * Real.log (l * x) + 2) /
        Real.sqrt x) *
      (l * gaussianEndpointDensity l v +
        2 * Real.exp (-1) * (Analysis.normalizedGaussianWeight v * Real.exp (-(1 / 2 : ℝ) * v)))

/-- Under RH, the sharp Gaussian envelope is bounded by the shifted finite Gamma sum.
The shifted scale and cutoff ratio have the same product, preserving the arithmetic endpoint. -/
theorem gaussian_sharp_envelope_le (hRH : RiemannHypothesis) {x l : ℝ} (hx : 0 < x) (hl : 0 ≤ l)
    (hlx : 1 ≤ l * x) (v : ℝ) :
    gaussianSharpLowerEnvelope x l v ≤
      Analysis.normalizedGaussianWeight v *
        ∑ n ∈ Finset.Ioc 0 ⌊l * x⌋₊,
          (gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) (x * Real.exp v) n).re := by
  have hc : (x * Real.exp v) * (l * Real.exp (-v)) = l * x := by
    rw [Real.exp_neg]
    field_simp [(Real.exp_pos v).ne']
  have h :=
    LLS.gamma_level_one_lower_sharp hRH (mul_pos hx (Real.exp_pos v))
      (mul_nonneg hl (Real.exp_pos (-v)).le) (hc ▸ hlx)
  rw [hc] at h
  have hw := mul_le_mul_of_nonneg_left h (Analysis.normalizedGaussianWeight_pos v).le
  rw [sqrt_gaussian_shift hx] at hw
  have he : Real.exp (-(3 / 2 : ℝ) * v) = Real.exp (-(1 / 2 : ℝ) * v) * Real.exp (-v) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he2 : Real.exp (-(1 / 2 : ℝ) * v) = (Real.exp (v / 2))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  have he3 : Real.exp (-v) = (Real.exp v)⁻¹ := Real.exp_neg v
  have hid :
    gaussianSharpLowerEnvelope x l v =
      Analysis.normalizedGaussianWeight v *
        (((x * Real.exp v) * (1 - Real.exp (-(l * Real.exp (-v)))) -
            Real.exp (-(l * Real.exp (-v))) * (l * x - Chebyshev.psi (l * x)) -
            ((231 / 5000 : ℝ) * Real.sqrt (l * x) + (1839 / 1000 : ℝ) * Real.log (l * x) + 2) *
              ((l * Real.exp (-v)) * Real.exp (-(l * Real.exp (-v))) + 2 * Real.exp (-1))) /
          (Real.sqrt x * Real.exp (v / 2))) := by
    dsimp only [gaussianSharpLowerEnvelope, Analysis.gaussianGammaCutoffIntegrand,
      Analysis.gaussianGammaProfileIntegrand, gaussianEndpointDensity]
    rw [he, he2, he3]
    field_simp [(Real.sqrt_pos.mpr hx).ne', (Real.exp_pos v).ne', (Real.exp_pos (v / 2)).ne']
    have hs := Real.sq_sqrt hx.le
    have hexp : Real.exp v = Real.exp (v / 2) * Real.exp (v / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    rw [hs]
    ring
  exact hid.trans_le hw

/-- The sharp lower envelope is integrable for a nonnegative cutoff ratio.
Each term is controlled by an integrable Gaussian moment or cutoff density. -/
theorem integrable_gaussianSharpLowerEnvelope (x : ℝ) {l : ℝ} (hl : 0 ≤ l) :
    MeasureTheory.Integrable (gaussianSharpLowerEnvelope x l) := by
  have ha := (Analysis.integrable_gaussianGammaCutoffIntegrand hl).const_mul (Real.sqrt x)
  have hb :=
    (Analysis.integrable_gaussianGammaProfileIntegrand hl).const_mul
      ((l * x - Chebyshev.psi (l * x)) / Real.sqrt x)
  have hc := (integrable_gaussianEndpointDensity hl).const_mul l
  have hd :=
    (Analysis.integrable_normalizedGaussian_mul_exp (-(1 / 2 : ℝ))).const_mul (2 * Real.exp (-1))
  have he :=
    (hc.add hd).const_mul
      (((231 / 5000 : ℝ) * Real.sqrt (l * x) + (1839 / 1000 : ℝ) * Real.log (l * x) + 2) /
        Real.sqrt x)
  convert (ha.sub hb).sub he using 1
  funext v
  rfl

/-- Under RH, the actual finite Gaussian principal sum has the sharp averaged lower bound.
The Chebyshev deficit and weighted-Mangoldt error remain at the fixed arithmetic cutoff.
Gaussian integrability and the finite Gamma mixture justify averaging pointwise. -/
theorem gaussian_level_one_lower_sharp (hRH : RiemannHypothesis) {x l : ℝ} (hx : 0 < x) (hl : 0 ≤ l)
    (hlx : 1 ≤ l * x) :
    Real.sqrt x * (∫ v : ℝ, Analysis.gaussianGammaCutoffIntegrand l v) -
        ((l * x - Chebyshev.psi (l * x)) / Real.sqrt x) *
          (∫ v : ℝ, Analysis.gaussianGammaProfileIntegrand l v) -
        (((231 / 5000 : ℝ) * Real.sqrt (l * x) + (1839 / 1000 : ℝ) * Real.log (l * x) + 2) /
            Real.sqrt x) *
          (l * (∫ v : ℝ, gaussianEndpointDensity l v) + 2 * Real.exp (-1) * Real.exp (1 / 16 : ℝ)) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊l * x⌋₊,
        (gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re := by
  rw [gaussian_principal_finite_sum_eq_gamma_average hx]
  have h :=
    MeasureTheory.integral_mono (integrable_gaussianSharpLowerEnvelope x hl)
      (integrable_gaussian_weighted_gamma_finite_sum hx ⌊l * x⌋₊)
      (gaussian_sharp_envelope_le hRH hx hl hlx)
  have ha := (Analysis.integrable_gaussianGammaCutoffIntegrand hl).const_mul (Real.sqrt x)
  have hb :=
    (Analysis.integrable_gaussianGammaProfileIntegrand hl).const_mul
      ((l * x - Chebyshev.psi (l * x)) / Real.sqrt x)
  have hc := (integrable_gaussianEndpointDensity hl).const_mul l
  have hd :=
    (Analysis.integrable_normalizedGaussian_mul_exp (-(1 / 2 : ℝ))).const_mul (2 * Real.exp (-1))
  have he :=
    (hc.add hd).const_mul
      (((231 / 5000 : ℝ) * Real.sqrt (l * x) + (1839 / 1000 : ℝ) * Real.log (l * x) + 2) /
        Real.sqrt x)
  have h1 := MeasureTheory.integral_sub (ha.sub hb) he
  have h2 := MeasureTheory.integral_sub ha hb
  have h3 := MeasureTheory.integral_add hc hd
  simp only [Pi.sub_apply, Pi.add_apply] at h1 h2 h3
  change (∫ v : ℝ, gaussianSharpLowerEnvelope x l v) ≤ _ at h
  unfold gaussianSharpLowerEnvelope at h
  rw [h1, h2, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, h3, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, Analysis.integral_normalizedGaussian_mul_exp] at h
  norm_num only at h
  exact h

end PseudoPrime.LLS.PaperStatements

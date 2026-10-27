/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RelativeGammaPrincipalBounds
public import PseudoPrime.LLS.GaussianPrincipalBounds

/-! # Relative-loss Gaussian principal cutoff lower bounds -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Gaussian-weighted relative-loss Gamma envelope at scale x and cutoff l.
The three terms retain the cutoff mass, constant error, and negative half moment.
Its integral is the lower input for the actual finite Gaussian sum. -/
noncomputable def gaussianRelativeLowerEnvelope (h x l v : ℝ) : ℝ :=
  (1 - h) * Real.sqrt x * Analysis.gaussianGammaCutoffIntegrand l v -
    (1 / (10 * h)) * Analysis.normalizedGaussianWeight v -
    ((21 / (10 * h) + 1839 / 1000) / Real.sqrt x) *
      (Analysis.normalizedGaussianWeight v * Real.exp (-(1 / 2 : ℝ) * v))

/-- For nonnegative cutoff the relative lower envelope is integrable.
Use the cutoff density, Gaussian mass, and negative half exponential moment. -/
theorem integrable_gaussianRelativeLowerEnvelope (h x : ℝ) {l : ℝ} (hl : 0 ≤ l) :
    MeasureTheory.Integrable (gaussianRelativeLowerEnvelope h x l) :=
  (((Analysis.integrable_gaussianGammaCutoffIntegrand hl).const_mul _).sub
        (Analysis.integrable_normalizedGaussianWeight.const_mul _)).sub
    ((Analysis.integrable_normalizedGaussian_mul_exp (-(1 / 2))).const_mul _)

/-- Evaluate the relative envelope by its three Gaussian moments.
The inverse-square-root error gains the exact factor exp(1/16). -/
theorem integral_gaussianRelativeLowerEnvelope (h x : ℝ) {l : ℝ} (hl : 0 ≤ l) :
    (∫ v : ℝ, gaussianRelativeLowerEnvelope h x l v) =
      (1 - h) * Real.sqrt x * (∫ v : ℝ, Analysis.gaussianGammaCutoffIntegrand l v) - 1 / (10 * h) -
        ((21 / (10 * h) + 1839 / 1000) / Real.sqrt x) * Real.exp (1 / 16 : ℝ) := by
  dsimp only [gaussianRelativeLowerEnvelope]
  have hA := (Analysis.integrable_gaussianGammaCutoffIntegrand hl).const_mul ((1 - h) * Real.sqrt x)
  have hB := Analysis.integrable_normalizedGaussianWeight.const_mul (1 / (10 * h))
  have hC :=
    (Analysis.integrable_normalizedGaussian_mul_exp (-(1 / 2))).const_mul
      ((21 / (10 * h) + 1839 / 1000) / Real.sqrt x)
  have hi := MeasureTheory.integral_sub (hA.sub hB) hC
  have hj := MeasureTheory.integral_sub hA hB
  simp only [Pi.sub_apply] at hi hj
  rw [hi, hj, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, Analysis.integral_normalizedGaussianWeight_eq_one,
    Analysis.integral_normalizedGaussian_mul_exp]
  norm_num only [mul_one]

/-- Under RH and relative width in (0,1/2], the actual finite Gaussian sum
has relative main loss h and constant plus inverse-square-root errors.
Average the global Gamma estimate with moving cutoff and fixed finite support.
This removes the quarter-power lower error from subgroup comparisons. -/
theorem gaussian_level_one_sum_lower_relative (hRH : RiemannHypothesis) {h x l : ℝ} (hh : 0 < h)
    (hh1 : h ≤ 1 / 2) (hx : 0 < x) (hl : 0 ≤ l) :
    (1 - h) * Real.sqrt x *
          (∫ u in (0 : ℝ)..l, (gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
        1 / (10 * h) -
        ((21 / (10 * h) + 1839 / 1000) / Real.sqrt x) * Real.exp (1 / 16 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊l * x⌋₊,
        (gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re := by
  rw [gaussian_principal_finite_sum_eq_gamma_average hx, gaussianGamma_cutoff_integral hl]
  have hb (v : ℝ) :
    gaussianRelativeLowerEnvelope h x l v ≤
      Analysis.normalizedGaussianWeight v *
        ∑ n ∈ Finset.Ioc 0 ⌊l * x⌋₊,
          (gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) (x * Real.exp v) n).re := by
    have hm :=
      gamma_level_one_sum_lower_relative hRH hh hh1 (mul_pos hx (Real.exp_pos v))
        (mul_nonneg hl (Real.exp_pos (-v)).le)
    have hc : (l * Real.exp (-v)) * (x * Real.exp v) = l * x := by
      rw [Real.exp_neg]
      field_simp [(Real.exp_pos v).ne']
    rw [hc] at hm
    have hw := mul_le_mul_of_nonneg_left hm (Analysis.normalizedGaussianWeight_pos v).le
    rw [sqrt_gaussian_shift hx] at hw
    have he :
      gaussianRelativeLowerEnvelope h x l v =
        Analysis.normalizedGaussianWeight v *
          ((1 - h) * (Real.sqrt x * Real.exp (v / 2)) * (1 - Real.exp (-(l * Real.exp (-v)))) -
            1 / (10 * h) -
            (21 / (10 * h) + 1839 / 1000) / (Real.sqrt x * Real.exp (v / 2))) := by
      dsimp only [gaussianRelativeLowerEnvelope, Analysis.gaussianGammaCutoffIntegrand]
      rw [show -(1 / 2 : ℝ) * v = -(v / 2) by ring]
      simp only [neg_mul, Real.exp_neg]
      field_simp [(Real.sqrt_pos.mpr hx).ne', (Real.exp_pos (v / 2)).ne', hh.ne']
    exact he.trans_le hw
  have hm :=
    MeasureTheory.integral_mono (integrable_gaussianRelativeLowerEnvelope h x hl)
      (integrable_gaussian_weighted_gamma_finite_sum hx ⌊l * x⌋₊) hb
  rw [integral_gaussianRelativeLowerEnvelope h x hl] at hm
  exact hm

end PseudoPrime.LLS.PaperStatements

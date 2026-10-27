/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GaussianPrincipalMixture
public import PseudoPrime.LLS.MellinKernelPrimitiveSupport

/-! # Explicit principal and cutoff error fourteen for the Gaussian kernel

Exact logarithmic Gaussian averaging transfers the uniform Gamma error thirteen
to error fourteen. Finite cutoff and full principal sums use the actual kernel.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The Gaussian-weighted upper main and error envelope after a scale shift.
Its half and quarter Gaussian moments integrate to the principal main term and error. -/
noncomputable def gaussianPrincipalUpperEnvelope (x v : ℝ) : ℝ :=
  Real.sqrt x * (Analysis.normalizedGaussianWeight v * Real.exp ((1 / 2 : ℝ) * v)) +
    13 * x ^ (1 / 4 : ℝ) * (Analysis.normalizedGaussianWeight v * Real.exp ((1 / 4 : ℝ) * v))

/-- The Gaussian-weighted finite-cutoff lower envelope. The cutoff integrand
retains the actual cutoff mass, while the quarter moment controls the error. -/
noncomputable def gaussianPrincipalLowerEnvelope (x l v : ℝ) : ℝ :=
  Real.sqrt x * Analysis.gaussianGammaCutoffIntegrand l v -
    13 * x ^ (1 / 4 : ℝ) * (Analysis.normalizedGaussianWeight v * Real.exp ((1 / 4 : ℝ) * v))

/-- The upper envelope is integrable for every scale. Its two terms are
constant multiples of the established half and quarter Gaussian moments. -/
theorem integrable_gaussianPrincipalUpperEnvelope (x : ℝ) :
    MeasureTheory.Integrable (gaussianPrincipalUpperEnvelope x) :=
  ((Analysis.integrable_normalizedGaussian_mul_exp (1 / 2)).const_mul _).add
    ((Analysis.integrable_normalizedGaussian_mul_exp (1 / 4)).const_mul _)

/-- The integral of the upper envelope is sqrt(x)exp(1/16) plus
13x^(1/4)exp(1/64). Evaluate the two exact normalized Gaussian moments. -/
theorem integral_gaussianPrincipalUpperEnvelope (x : ℝ) :
    (∫ v : ℝ, gaussianPrincipalUpperEnvelope x v) =
      Real.sqrt x * Real.exp (1 / 16 : ℝ) + 13 * x ^ (1 / 4 : ℝ) * Real.exp (1 / 64 : ℝ) := by
  dsimp only [gaussianPrincipalUpperEnvelope]
  rw [MeasureTheory.integral_add
      ((Analysis.integrable_normalizedGaussian_mul_exp (1 / 2)).const_mul _)
      ((Analysis.integrable_normalizedGaussian_mul_exp (1 / 4)).const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    Analysis.integral_normalizedGaussian_mul_exp, Analysis.integral_normalizedGaussian_mul_exp]
  norm_num only

/-- For every scale and nonnegative cutoff, the lower envelope is integrable.
Use the integrable actual cutoff density and quarter Gaussian moment. -/
theorem integrable_gaussianPrincipalLowerEnvelope (x : ℝ) {l : ℝ} (hl : 0 ≤ l) :
    MeasureTheory.Integrable (gaussianPrincipalLowerEnvelope x l) :=
  ((Analysis.integrable_gaussianGammaCutoffIntegrand hl).const_mul _).sub
    ((Analysis.integrable_normalizedGaussian_mul_exp (1 / 4)).const_mul _)

/-- For nonnegative cutoff, the lower envelope integrates to sqrt(x) times
the actual Gaussian cutoff mass minus 13x^(1/4)exp(1/64). Use integral subtraction
and the exact quarter Gaussian moment. -/
theorem integral_gaussianPrincipalLowerEnvelope (x : ℝ) {l : ℝ} (hl : 0 ≤ l) :
    (∫ v : ℝ, gaussianPrincipalLowerEnvelope x l v) =
      Real.sqrt x * (∫ v : ℝ, Analysis.gaussianGammaCutoffIntegrand l v) -
        13 * x ^ (1 / 4 : ℝ) * Real.exp (1 / 64 : ℝ) := by
  dsimp only [gaussianPrincipalLowerEnvelope]
  rw [MeasureTheory.integral_sub ((Analysis.integrable_gaussianGammaCutoffIntegrand hl).const_mul _)
      ((Analysis.integrable_normalizedGaussian_mul_exp (1 / 4)).const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    Analysis.integral_normalizedGaussian_mul_exp]
  norm_num only

/-- Under RH at every positive scale and natural cutoff, the finite level-one
Gaussian principal sum is at most sqrt(x)exp(1/16)+14x^(1/4). Average the actual
Gamma finite upper bound and certify 13exp(1/64)≤14. No eventual threshold is required. -/
theorem gaussian_level_one_finite_sum_upper_fourteen (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x)
    (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N,
        (gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re) ≤
      Real.sqrt x * Real.exp (1 / 16 : ℝ) + 14 * x ^ (1 / 4 : ℝ) := by
  rw [gaussian_principal_finite_sum_eq_gamma_average hx N]
  have hb (v : ℝ) :
    Analysis.normalizedGaussianWeight v *
        (∑ n ∈ Finset.Ioc 0 N,
          (gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) (x * Real.exp v) n).re) ≤
      gaussianPrincipalUpperEnvelope x v := by
    have h :=
      mul_le_mul_of_nonneg_left
        (gamma_level_one_finite_sum_upper_thirteen hRH (mul_pos hx (Real.exp_pos v)) N)
        (Analysis.normalizedGaussianWeight_pos v).le
    rw [sqrt_gaussian_shift hx, fourth_root_gaussian_shift hx, show v / 2 = (1 / 2 : ℝ) * v by ring,
      show v / 4 = (1 / 4 : ℝ) * v by ring] at h
    exact
      h.trans_eq
        (by
          dsimp only [gaussianPrincipalUpperEnvelope]; ring)
  have h :=
    MeasureTheory.integral_mono (integrable_gaussian_weighted_gamma_finite_sum hx N)
      (integrable_gaussianPrincipalUpperEnvelope x) hb
  rw [integral_gaussianPrincipalUpperEnvelope] at h
  have he :=
    mul_le_mul_of_nonneg_right gaussian_principal_error_factor_le_fourteen
      (Real.rpow_nonneg hx.le (1 / 4))
  nlinarith only [h, he]

/-- Under RH at every positive scale and nonnegative cutoff l, the actual
finite level-one Gaussian sum is at least sqrt(x) times its transform cutoff mass
minus 14x^(1/4). Average Gamma lower bounds at shifted scale and cutoff;
their product retains the original finite index set. This supplies the MR lower input. -/
theorem gaussian_level_one_sum_lower_fourteen (hRH : RiemannHypothesis) {x l : ℝ} (hx : 0 < x)
    (hl : 0 ≤ l) :
    Real.sqrt x * (∫ u in (0 : ℝ)..l, (gaussianGammaMellinKernel.transform u).re / Real.sqrt u) -
        14 * x ^ (1 / 4 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊l * x⌋₊,
        (gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re := by
  rw [gaussian_principal_finite_sum_eq_gamma_average hx, gaussianGamma_cutoff_integral hl]
  have hb (v : ℝ) :
    gaussianPrincipalLowerEnvelope x l v ≤
      Analysis.normalizedGaussianWeight v *
        ∑ n ∈ Finset.Ioc 0 ⌊l * x⌋₊,
          (gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) (x * Real.exp v) n).re := by
    have h :=
      gamma_level_one_sum_lower_thirteen hRH (mul_pos hx (Real.exp_pos v))
        (mul_nonneg hl (Real.exp_pos (-v)).le)
    have hc : (l * Real.exp (-v)) * (x * Real.exp v) = l * x := by
      rw [Real.exp_neg]
      field_simp (discharger := exact (Real.exp_pos v).ne')
    rw [hc] at h
    have hw := mul_le_mul_of_nonneg_left h (Analysis.normalizedGaussianWeight_pos v).le
    rw [sqrt_gaussian_shift hx, fourth_root_gaussian_shift hx,
      show v / 4 = (1 / 4 : ℝ) * v by ring] at hw
    exact
      (show gaussianPrincipalLowerEnvelope x l v = _
            by
            dsimp only [gaussianPrincipalLowerEnvelope, Analysis.gaussianGammaCutoffIntegrand]
            ring_nf).trans_le
        hw
  have h :=
    MeasureTheory.integral_mono (integrable_gaussianPrincipalLowerEnvelope x hl)
      (integrable_gaussian_weighted_gamma_finite_sum hx ⌊l * x⌋₊) hb
  rw [integral_gaussianPrincipalLowerEnvelope x hl] at h
  have he :=
    mul_le_mul_of_nonneg_right gaussian_principal_error_factor_le_fourteen
      (Real.rpow_nonneg hx.le (1 / 4))
  nlinarith only [h, he]

/-- Under RH, the full level-one Gaussian sum has real part at most
sqrt(x)exp(1/16)+14x^(1/4) at every positive scale. Transfer the finite upper bounds
to the absolutely convergent nonnegative series using range partial sums.
This is the numerical principal term in the primitive Gamma comparison. -/
theorem gaussian_level_one_sum_upper_fourteen (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re ≤
      Real.sqrt x * Real.exp (1 / 16 : ℝ) + 14 * x ^ (1 / 4 : ℝ) := by
  have hs := MellinKernel.summable_summand gaussianGammaMellinKernel (1 : DirichletCharacter ℂ 1) hx
  change
    Complex.reCLM (∑' n : ℕ, gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n) ≤ _
  rw [Complex.reCLM.map_tsum hs]
  apply (Complex.reCLM.summable hs).tsum_le_of_sum_range_le
  intro N
  have hzero : (gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x 0).re = 0 := by
    simp only [MellinKernel.summand, ite_true, Complex.zero_re]
  have he :
    (∑ n ∈ Finset.Icc 0 N,
        (gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re) =
      ∑ n ∈ Finset.Ioc 0 N,
        (gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le N), Finset.sum_cons, hzero, zero_add]
  have hsub : Finset.range N ⊆ Finset.Icc 0 N := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le n, (Finset.mem_range.mp hn).le⟩
  calc
    _ ≤
        ∑ n ∈ Finset.Icc 0 N,
          (gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun n _ _ ↦ MellinKernel.principal_summand_re_nonneg gaussianGammaMellinKernel hx n)
    _ = _ := he
    _ ≤ _ := gaussian_level_one_finite_sum_upper_fourteen hRH hx N

/-- Under RH, the primitive source of every nonzero-level principal Gaussian
series has real part at most sqrt(x)exp(1/16)+14x^(1/4), for x>0.
Its summands equal the level-one principal summands; apply the full upper bound.
This is the principal term in the aggregate primitive-character comparison. -/
theorem gaussian_primitive_principal_sum_upper_fourteen (hRH : RiemannHypothesis) {q : ℕ} [NeZero q]
    {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ,
          gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ q).primitiveCharacter x
            n).re ≤
      Real.sqrt x * Real.exp (1 / 16 : ℝ) + 14 * x ^ (1 / 4 : ℝ) := by
  rw [tsum_congr
      (MellinKernel.principal_primitive_summand_eq_level_one gaussianGammaMellinKernel (q := q) x)]
  exact gaussian_level_one_sum_upper_fourteen hRH hx

end PseudoPrime.LLS.PaperStatements

/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaSignedVariationPrincipalBounds
public import PseudoPrime.LLS.GaussianPrincipalBounds

/-! # Constant principal upper errors for Gamma and Gaussian kernels -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under RH, every positive scale and every finite cutoff have principal Gamma
error at most thirteen. Large scales use the signed variation estimate;
scales below one use the existing fourth-root bound. -/
theorem gamma_level_one_finite_sum_upper_constant (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x)
    (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, (gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re) ≤
      Real.sqrt x + 13 := by
  by_cases hx1 : 1 ≤ x
  · have h := exponentialMangoldtSum_upper_signed_variation hRH hx1 N
    have heq := gamma_level_one_sum_eq_exponential (y := (N : ℝ)) hx
    simp only [Nat.floor_natCast] at heq
    rw [heq]
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hx)).mpr
    have hs : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx1
    have hl := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx)
    rw [Real.log_sqrt hx.le] at hl
    rw [add_mul, ← pow_two, Real.sq_sqrt hx.le]
    nlinarith only [h, hs, hl]
  · have h := gamma_level_one_finite_sum_upper_thirteen hRH hx N
    have hp := Real.rpow_le_one hx.le (le_of_not_ge hx1) (by norm_num only : (0 : ℝ) ≤ 1 / 4)
    nlinarith only [h, hp]

/-- Under RH, all Gaussian finite principal sums have a scale-independent
additive error thirteen. Average the constant Gamma error with Gaussian mass one. -/
theorem gaussian_level_one_finite_sum_upper_constant (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x)
    (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N,
        (gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re) ≤
      Real.sqrt x * Real.exp (1 / 16 : ℝ) + 13 := by
  rw [gaussian_principal_finite_sum_eq_gamma_average hx N]
  have hb (v : ℝ) :
    Analysis.normalizedGaussianWeight v *
        (∑ n ∈ Finset.Ioc 0 N,
          (gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) (x * Real.exp v) n).re) ≤
      Real.sqrt x * (Analysis.normalizedGaussianWeight v * Real.exp ((1 / 2 : ℝ) * v)) +
        13 * Analysis.normalizedGaussianWeight v := by
    have h :=
      mul_le_mul_of_nonneg_left
        (gamma_level_one_finite_sum_upper_constant hRH (mul_pos hx (Real.exp_pos v)) N)
        (Analysis.normalizedGaussianWeight_pos v).le
    rw [sqrt_gaussian_shift hx, show v / 2 = (1 / 2 : ℝ) * v by ring] at h
    nlinarith only [h]
  have hi :=
    ((Analysis.integrable_normalizedGaussian_mul_exp (1 / 2)).const_mul (Real.sqrt x)).add
      (Analysis.integrable_normalizedGaussianWeight.const_mul 13)
  have h := MeasureTheory.integral_mono (integrable_gaussian_weighted_gamma_finite_sum hx N) hi hb
  simp only [Pi.add_apply] at h
  rw [MeasureTheory.integral_add
      ((Analysis.integrable_normalizedGaussian_mul_exp (1 / 2)).const_mul (Real.sqrt x))
      (Analysis.integrable_normalizedGaussianWeight.const_mul 13),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    Analysis.integral_normalizedGaussian_mul_exp,
    Analysis.integral_normalizedGaussianWeight_eq_one] at h
  norm_num only at h
  exact h

/-- Under RH, the full level-one Gaussian sum has real part at most
sqrt(x)exp(1/16)+13 at every positive scale. Transfer the finite upper bounds
to the absolutely convergent nonnegative series using range partial sums.
This is the numerical principal term in the primitive Gamma comparison. -/
theorem gaussian_level_one_sum_upper_constant (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re ≤
      Real.sqrt x * Real.exp (1 / 16 : ℝ) + 13 := by
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
    _ ≤ _ := gaussian_level_one_finite_sum_upper_constant hRH hx N

/-- Under RH, the primitive source of every nonzero-level principal Gaussian
series has real part at most sqrt(x)exp(1/16)+13, for x>0.
Its summands equal the level-one principal summands; apply the full upper bound.
This is the principal term in the aggregate primitive-character comparison. -/
theorem gaussian_primitive_principal_sum_upper_constant (hRH : RiemannHypothesis) {q : ℕ} [NeZero q]
    {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ,
          gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ q).primitiveCharacter x
            n).re ≤
      Real.sqrt x * Real.exp (1 / 16 : ℝ) + 13 := by
  rw [tsum_congr
      (MellinKernel.principal_primitive_summand_eq_level_one gaussianGammaMellinKernel (q := q) x)]
  exact gaussian_level_one_sum_upper_constant hRH hx

end PseudoPrime.LLS.PaperStatements

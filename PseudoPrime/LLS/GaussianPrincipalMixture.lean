/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GaussianKernel
public import PseudoPrime.LLS.GammaPrincipalUpperBounds

/-! # Exact Gaussian mixtures of finite principal Gamma sums

At every positive scale, Gaussian principal summands are logarithmic Gaussian
averages of shifted Gamma summands. Absolute integrability justifies finite-sum interchange.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- At positive scale and nonzero index, the real level-one Gamma summand is
the exponential Mangoldt term divided by sqrt(x). Evaluate the actual transform
and cancel its positive square-root factors for the logarithmic smoothing identity. -/
theorem gamma_principal_term_eq_exp_smoothing {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) :
    (gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re =
      Real.exp (-(n : ℝ) / x) * ArithmeticFunction.vonMangoldt n / Real.sqrt x := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hu : 0 < (n : ℝ) / x := div_pos hnpos hx
  simp only [MellinKernel.summand, ite_eq_right hn,
    MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), mul_one, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [gamma_transform_of_function gammaMellinKernel rfl hu, Real.sqrt_div hnpos.le, neg_div]
  field_simp (discharger :=
    first
    | exact (Real.sqrt_pos.mpr hnpos).ne'
    | exact (Real.sqrt_pos.mpr hx).ne')

/-- At positive scale, sqrt(x exp v)=sqrt(x) exp(v/2).
Use the positive real-power product rule to evaluate the main-term Gaussian moment. -/
theorem sqrt_gaussian_shift {x : ℝ} (hx : 0 < x) (v : ℝ) :
    Real.sqrt (x * Real.exp v) = Real.sqrt x * Real.exp (v / 2) := by
  rw [Real.sqrt_eq_rpow, Real.mul_rpow hx.le (Real.exp_pos v).le, ← Real.exp_mul, ←
    Real.sqrt_eq_rpow]
  congr 2
  ring

/-- At positive scale, (x exp v)^(1/4)=x^(1/4)exp(v/4).
Use the positive real-power product rule to evaluate the error-term Gaussian moment. -/
theorem fourth_root_gaussian_shift {x : ℝ} (hx : 0 < x) (v : ℝ) :
    (x * Real.exp v) ^ (1 / 4 : ℝ) = x ^ (1 / 4 : ℝ) * Real.exp (v / 4) := by
  rw [Real.mul_rpow hx.le (Real.exp_pos v).le, ← Real.exp_mul]
  congr 2
  ring

/-- The smoothed error coefficient 13exp(1/64) is at most 14.
A four-term exponential upper certificate gives the explicit principal and cutoff error. -/
theorem gaussian_principal_error_factor_le_fourteen : (13 : ℝ) * Real.exp (1 / 64 : ℝ) ≤ 14 := by
  have h :=
    Real.exp_bound' (x := (1 / 64 : ℝ)) (n := 4) (by norm_num only) (by norm_num only) (by decide)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_succ,
    Nat.factorial_zero, Nat.cast_ofNat] at h
  linarith only [h]

/-- A nonzero level-one Gaussian principal summand is vonMangoldt(n)/sqrt(x)
times the profile-integrand average. Use actual Gaussian inversion and cancel
the positive square-root factors. This connects the arithmetic summand to its mixture. -/
theorem gaussian_principal_term_eq_profile_integral {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) :
    (gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re =
      (ArithmeticFunction.vonMangoldt n / Real.sqrt x) *
        ∫ v : ℝ, Analysis.gaussianGammaProfileIntegrand ((n : ℝ) / x) v := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hu : 0 < (n : ℝ) / x := div_pos hnpos hx
  simp only [MellinKernel.summand, ite_eq_right hn,
    MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), mul_one, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [gaussianGamma_transform hu, Complex.ofReal_re, Analysis.gaussianGammaProfile,
    Real.sqrt_div hnpos.le]
  field_simp (discharger :=
    first
    | exact (Real.sqrt_pos.mpr hnpos).ne'
    | exact (Real.sqrt_pos.mpr hx).ne')

/-- At positive scale and nonzero index, the Gaussian-weighted shifted Gamma
summand equals its exact profile integrand times vonMangoldt(n)/sqrt(x).
Evaluate the Gamma summand and cancel exponentials under the logarithmic scale shift. -/
theorem gaussian_weighted_gamma_term_eq_profile {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) (v : ℝ) :
    Analysis.normalizedGaussianWeight v *
        (gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) (x * Real.exp v) n).re =
      (ArithmeticFunction.vonMangoldt n / Real.sqrt x) *
        Analysis.gaussianGammaProfileIntegrand ((n : ℝ) / x) v := by
  rw [gamma_principal_term_eq_exp_smoothing (mul_pos hx (Real.exp_pos v)) hn,
    sqrt_gaussian_shift hx]
  have he : -(n : ℝ) / (x * Real.exp v) = -((n : ℝ) / x) * Real.exp (-v) := by
    rw [Real.exp_neg]
    field_simp (discharger :=
      first
      | exact hx.ne'
      | exact (Real.exp_pos v).ne')
  rw [he]
  dsimp only [Analysis.gaussianGammaProfileIntegrand]
  rw [show -(1 / 2 : ℝ) * v = -(v / 2) by ring]
  simp only [Real.exp_neg]
  field_simp (discharger :=
    first
    | exact (Real.sqrt_pos.mpr hx).ne'
    | exact (Real.exp_pos (v / 2)).ne')

/-- For a nonzero index and positive scale, the weighted shifted Gamma
summand is integrable. Its exact profile identity supplies the integrable majorant
already established by Gaussian inversion. This justifies termwise averaging. -/
theorem integrable_gaussian_weighted_gamma_term {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) :
    MeasureTheory.Integrable
      (fun v : ℝ ↦
        Analysis.normalizedGaussianWeight v *
          (gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) (x * Real.exp v) n).re) := by
  have hu : 0 ≤ (n : ℝ) / x := div_nonneg (Nat.cast_nonneg n) hx.le
  exact
    ((Analysis.integrable_gaussianGammaProfileIntegrand hu).const_mul
          (ArithmeticFunction.vonMangoldt n / Real.sqrt x)).congr
      (Filter.Eventually.of_forall (fun v ↦ (gaussian_weighted_gamma_term_eq_profile hx hn v).symm))

/-- Every nonzero level-one Gaussian principal summand equals the Gaussian
average of the shifted Gamma summand. Combine the two profile identities and
extract the constant from the integrable average. -/
theorem gaussian_principal_term_eq_gamma_average {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) :
    (gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re =
      ∫ v : ℝ,
        Analysis.normalizedGaussianWeight v *
          (gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) (x * Real.exp v) n).re := by
  rw [gaussian_principal_term_eq_profile_integral hx hn, ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall (fun v ↦ (gaussian_weighted_gamma_term_eq_profile hx hn v).symm)

/-- For positive scale and every natural cutoff, the weighted shifted finite
Gamma principal sum is integrable. Sum the integrable nonzero-index terms. -/
theorem integrable_gaussian_weighted_gamma_finite_sum {x : ℝ} (hx : 0 < x) (N : ℕ) :
    MeasureTheory.Integrable
      (fun v : ℝ ↦
        Analysis.normalizedGaussianWeight v *
          ∑ n ∈ Finset.Ioc 0 N,
            (gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) (x * Real.exp v) n).re) := by
  have h :=
    MeasureTheory.integrable_finsetSum (Finset.Ioc 0 N)
      (fun n hn ↦
        integrable_gaussian_weighted_gamma_term hx (Nat.ne_zero_of_lt (Finset.mem_Ioc.mp hn).1))
  exact h.congr (Filter.Eventually.of_forall (fun v ↦ (Finset.mul_sum _ _ _).symm))

/-- At positive scale and every natural cutoff, the finite Gaussian principal
sum equals the Gaussian average of the shifted finite Gamma sum. Interchange
the finite sum and integral using termwise integrability. This supplies the
actual arithmetic interface for principal and cutoff estimates. -/
theorem gaussian_principal_finite_sum_eq_gamma_average {x : ℝ} (hx : 0 < x) (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N,
        (gaussianGammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re) =
      ∫ v : ℝ,
        Analysis.normalizedGaussianWeight v *
          ∑ n ∈ Finset.Ioc 0 N,
            (gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) (x * Real.exp v) n).re := by
  simp only [Finset.mul_sum]
  rw [MeasureTheory.integral_finsetSum (Finset.Ioc 0 N)
      (fun n hn ↦
        integrable_gaussian_weighted_gamma_term hx (Nat.ne_zero_of_lt (Finset.mem_Ioc.mp hn).1))]
  apply Finset.sum_congr rfl
  intro n hn
  exact gaussian_principal_term_eq_gamma_average hx (Nat.ne_zero_of_lt (Finset.mem_Ioc.mp hn).1)

end PseudoPrime.LLS.PaperStatements

/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassPolynomial
import PseudoPrime.Analysis.CauchyPowerIntegrals

/-! # Fourier reduction for the absolute high Gaussian mass -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The shifted Cauchy power is integrable by dilation of the unit Cauchy power. -/
private theorem integrable_shifted_cauchy {a : ℝ} (ha : 0 < a) {m : ℕ} (hm : 1 ≤ m) :
    MeasureTheory.Integrable (fun t : ℝ ↦ 1 / (a ^ 2 + t ^ 2) ^ m) := by
  have h := (Analysis.integrable_cauchy_power hm).comp_mul_left' (inv_ne_zero ha.ne')
  apply (h.const_mul (1 / (a ^ 2) ^ m)).congr
  apply Filter.Eventually.of_forall
  intro t
  change _ * (1 / (1 + (a⁻¹ * t) ^ 2) ^ m) = _
  have he : a ^ 2 * (1 + (a⁻¹ * t) ^ 2) = a ^ 2 + t ^ 2 := by
    rw [mul_add, mul_one, ← mul_pow, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
  rw [div_mul_div_comm, one_mul, ← mul_pow, he]

/-- Imaginary modulation preserves the norm of a shifted Cauchy power. -/
private theorem norm_exp_div_cauchy (a x t : ℝ) (m : ℕ) :
    ‖Complex.exp ((x * t : ℝ) * Complex.I) / (((a ^ 2 + t ^ 2 : ℝ) : ℂ) ^ m)‖ =
      1 / (a ^ 2 + t ^ 2) ^ m := by
  rw [norm_div, Complex.norm_exp, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (add_nonneg (sq_nonneg a) (sq_nonneg t))]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, mul_zero, zero_mul,
    sub_self, Real.exp_zero]

/-- Each reciprocal power in the Fourier integral is absolutely integrable. -/
private theorem integrable_modulated_cauchy {a : ℝ} (ha : 0 < a) {m : ℕ} (hm : 1 ≤ m) (x : ℝ) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦ Complex.exp ((x * t : ℝ) * Complex.I) / (((a ^ 2 + t ^ 2 : ℝ) : ℂ) ^ m)) := by
  have h := integrable_shifted_cauchy ha hm
  apply h.mono' ?_ (Filter.Eventually.of_forall fun t ↦ (norm_exp_div_cauchy a x t m).le)
  apply Continuous.aestronglyMeasurable
  exact
    (Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul
            continuous_const)).div
      ((Complex.continuous_ofReal.comp (continuous_const.add (continuous_id.pow 2))).pow m)
      (fun t ↦
        pow_ne_zero _
          (Complex.ofReal_ne_zero.mpr (add_pos_of_pos_of_nonneg (pow_pos ha 2) (sq_nonneg t)).ne'))

/-- Fourier integration of the high Gaussian absolute mass is a finite combination
of the modulated Cauchy integrals of orders `K.degree + 2 - j`. -/
public theorem high_gaussian_mass_fourier_sum (K : HighGaussianKernel) (x : ℝ) :
    (∫ t : ℝ,
        (‖∑ j ∈ Finset.range (2 * K.degree + 1),
                (K.expandedCoeff j : ℂ) * Complex.exp (5 * (Complex.I * (t : ℂ))) /
                  (Complex.I * (t : ℂ) + (K.pole : ℂ)) ^ (K.logPower j + 1)‖ :
            ℂ) *
          Complex.exp ((x * t : ℝ) * Complex.I)) =
      ∑ j ∈ Finset.range (K.degree + 1),
        (K.normalization : ℂ) * ((normSqPolynomial K.pole K.polynomial).coeff j : ℂ) *
          (∫ t : ℝ,
            Complex.exp ((x * t : ℝ) * Complex.I) /
              ((((K.pole : ℝ) ^ 2 + t ^ 2 : ℝ) : ℂ) ^ (K.degree + 2 - j))) := by
  have ha := (by norm_num only : (0 : ℝ) < 1 / 2).trans (high_gaussian_pole_gt K)
  let c (j : ℕ) : ℂ := (K.normalization : ℂ) * ((normSqPolynomial K.pole K.polynomial).coeff j : ℂ)
  let g (j : ℕ) (t : ℝ) : ℂ :=
    Complex.exp ((x * t : ℝ) * Complex.I) /
      ((((K.pole : ℝ) ^ 2 + t ^ 2 : ℝ) : ℂ) ^ (K.degree + 2 - j))
  have hg (j : ℕ) (hj : j ∈ Finset.range (K.degree + 1)) :
    MeasureTheory.Integrable (fun t ↦ c j * g j t) := by
    have hj' := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hm : 1 ≤ K.degree + 2 - j :=
      Nat.le_sub_of_add_le
        ((Nat.add_comm 1 j).trans_le
          ((Nat.add_le_add_right hj' 1).trans (Nat.add_le_add_left (by decide : 1 ≤ 2) _)))
    exact (integrable_modulated_cauchy ha hm x).const_mul (c j)
  change _ = ∑ j ∈ Finset.range (K.degree + 1), c j * (∫ t : ℝ, g j t)
  simp only [high_gaussian_norm_reciprocal, Complex.ofReal_sum, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_ratCast, Complex.ofReal_pow, Finset.sum_mul]
  simp_rw [← MeasureTheory.integral_const_mul]
  rw [← MeasureTheory.integral_finsetSum (Finset.range (K.degree + 1)) hg]
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [c, g]
  rw [div_mul_eq_mul_div, mul_div_assoc, Complex.ofReal_mul]

end PseudoPrime.PrimeTestBounds.MillerRabin

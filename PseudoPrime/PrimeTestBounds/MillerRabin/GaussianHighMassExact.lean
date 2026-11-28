/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassIntegral
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighAngleMode
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighKernelCircle
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighKernelData
import Mathlib.Tactic.Ring

/-! # Exact norm integral of the high Gaussian kernels -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Real coefficients of the high kernel in its normalized circle coordinate. -/
private noncomputable def circleCoeff (K : HighGaussianKernel) (j : ℕ) : ℝ :=
  (((coefficientTicks K)[j]?.getD 0 : ℤ) : ℝ) / ((coefficientTicks K).sum : ℝ)

/-- The circle polynomial in the double-angle coordinate is a finite Fourier sum. -/
private theorem circle_poly_angle (K : HighGaussianKernel) (θ : ℝ) :
    K.circlePoly (Complex.exp (2 * (θ : ℂ) * Complex.I)) =
      ∑ j ∈ Finset.range (K.degree + 1),
        (circleCoeff K j : ℂ) * Complex.exp (2 * ((j : ℤ) : ℂ) * Complex.I * (θ : ℂ)) := by
  unfold HighGaussianKernel.circlePoly
  apply Finset.sum_congr rfl
  intro j _
  simp only [circleCoeff, Complex.ofReal_div, Complex.ofReal_intCast]
  rw [← Complex.exp_natCast_mul, Int.cast_natCast]
  congr 2
  ring

/-- On the real angle interval the sine-square weight and pole factor separate. -/
private theorem mass_angle_factor (K : HighGaussianKernel) :
    (∫ θ in Set.Ioo (0 : ℝ) Real.pi,
        (K.normalization : ℝ) * ‖K.circlePoly (Complex.exp (2 * (θ : ℂ) * Complex.I))‖ ^ 2 *
          (Real.sin θ ^ 2 / (K.pole : ℝ) ^ 3)) =
      (K.normalization : ℝ) / (K.pole : ℝ) ^ 3 *
        (∫ θ in (0 : ℝ)..Real.pi,
          Real.sin θ ^ 2 * ‖K.circlePoly (Complex.exp (2 * (θ : ℂ) * Complex.I))‖ ^ 2) := by
  rw [intervalIntegral.integral_of_le Real.pi_pos.le, MeasureTheory.integral_Ioc_eq_integral_Ioo, ←
    MeasureTheory.integral_const_mul]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
  intro θ _
  ring

/-- A linear-size check identifies the two coefficient sums with the private Gram integer. -/
private theorem tick_gram_range (K : HighGaussianKernel) :
    let v := coefficientTicks K
    ((∑ i ∈ Finset.range (K.degree + 1), (v[i]?.getD 0) ^ 2) -
        ∑ i ∈ Finset.range K.degree, (v[i]?.getD 0) * (v[i + 1]?.getD 0)) =
      tickGram v := by
  cases K <;> decide +kernel

/-- The normalization of the circle coefficients divides the Gram integer by the square total. -/
private theorem circle_gram_ratio (K : HighGaussianKernel) :
    ((∑ i ∈ Finset.range (K.degree + 1), circleCoeff K i ^ 2) -
        ∑ i ∈ Finset.range K.degree, circleCoeff K i * circleCoeff K (i + 1)) =
      (tickGram (coefficientTicks K) : ℝ) / ((coefficientTicks K).sum : ℝ) ^ 2 := by
  simp only [circleCoeff, div_pow, div_mul_div_comm, ← pow_two ((coefficientTicks K).sum : ℝ),
    ← Finset.sum_div, ← sub_div, ← Int.cast_pow, ← Int.cast_mul, ← Int.cast_sum, ← Int.cast_sub]
  rw [tick_gram_range]

/-- Cancel the three nonzero scale factors in the Gram normalization. -/
private theorem cancel_gram_normalization {a b g : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hg : g ≠ 0) :
    (3 * a * b / (4 * g)) / a * (Real.pi / 2 * (g / b)) = 3 * Real.pi / 8 := by
  calc
    _ = (3 * Real.pi / (4 * 2)) * (a / a) * (b / b) * (g / g) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by
      rw [div_self ha, div_self hb, div_self hg, mul_one, mul_one, mul_one]
      norm_num only

/-- The manuscript's normalization converts the real circle Gram value to mass `3 * π / 8`. -/
private theorem norm_mul_gram (K : HighGaussianKernel) :
    (K.normalization : ℝ) / (K.pole : ℝ) ^ 3 *
        (Real.pi / 2 * ((tickGram (coefficientTicks K) : ℝ) / ((coefficientTicks K).sum : ℝ) ^ 2)) =
      3 * Real.pi / 8 := by
  have hg : (0 : ℝ) < (tickGram (coefficientTicks K) : ℝ) := Int.cast_pos.mpr (tick_gram_pos K)
  have hp := (by norm_num only : (0 : ℝ) < 1 / 2).trans (high_gaussian_pole_gt K)
  have hs₀ : (coefficientTicks K).sum ≠ 0 := by cases K <;> decide +kernel
  have hs : ((coefficientTicks K).sum : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hs₀
  unfold HighGaussianKernel.normalization
  push_cast only [Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Rat.cast_intCast,
    Rat.cast_ofNat]
  exact cancel_gram_normalization (pow_ne_zero 3 hp.ne') (pow_ne_zero 2 hs) hg.ne'

/-- The norm integral of either high Gaussian shifted-pole kernel is exactly `3 * π / 8`. -/
public theorem high_gaussian_mass_exact (K : HighGaussianKernel) :
    (∫ t : ℝ,
        ‖∑ j ∈ Finset.range (2 * K.degree + 1),
            (K.expandedCoeff j : ℂ) * Complex.exp (5 * (Complex.I * (t : ℂ))) /
              (Complex.I * (t : ℂ) + (K.pole : ℂ)) ^ (K.logPower j + 1)‖) =
      3 * Real.pi / 8 := by
  rw [high_gaussian_mass_angle, mass_angle_factor]
  simp only [circle_poly_angle]
  rw [high_gaussian_real_angle_gram, circle_gram_ratio, norm_mul_gram]

end PseudoPrime.PrimeTestBounds.MillerRabin

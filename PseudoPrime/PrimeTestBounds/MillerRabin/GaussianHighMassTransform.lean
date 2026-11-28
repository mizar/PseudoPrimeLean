/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassFourier
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianOppositePolePolynomial
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassExact
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighKernelData
import Mathlib.Tactic.Ring

/-! # Exponential-polynomial transform of the high Gaussian absolute mass -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The absolute-mass Fourier polynomial of a high Gaussian kernel.
Its coefficients are rational and assembled from the reciprocal-power factors. -/
public noncomputable def highGaussianMassPolynomial (K : HighGaussianKernel) : Polynomial ℚ :=
  ∑ j ∈ Finset.range (K.degree + 1),
    Polynomial.C (K.normalization * (normSqPolynomial K.pole K.polynomial).coeff j) *
      oppositePolePolynomial K.pole (K.degree + 2 - j) (K.degree + 2 - j)

/-- The Fourier transform of the absolute kernel has the exponential times
polynomial form of the manuscript's mass transform. -/
public theorem high_gaussian_mass_transform (K : HighGaussianKernel) (x : ℝ) :
    (∫ t : ℝ,
        (‖∑ j ∈ Finset.range (2 * K.degree + 1),
                (K.expandedCoeff j : ℂ) * Complex.exp (5 * (Complex.I * (t : ℂ))) /
                  (Complex.I * (t : ℂ) + (K.pole : ℂ)) ^ (K.logPower j + 1)‖ :
            ℂ) *
          Complex.exp ((x * t : ℝ) * Complex.I)) =
      ((Real.pi * Real.exp (-(K.pole : ℝ) * |x|) *
            (highGaussianMassPolynomial K).eval₂ (Rat.castHom ℝ) |x| :
          ℝ) :
        ℂ) := by
  have ha : 1 ≤ (K.pole : ℝ) := by
    cases K <;> norm_num only [HighGaussianKernel.pole, Rat.cast_div, Rat.cast_ofNat]
  rw [high_gaussian_mass_fourier_sum]
  simp only [highGaussianMassPolynomial, Polynomial.eval₂_finsetSum, Complex.ofReal_mul,
    Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hm : 1 ≤ K.degree + 2 - j :=
    Nat.le_sub_of_add_le
      ((Nat.add_comm 1 j).trans_le
        ((Nat.add_le_add_right hj' 1).trans (Nat.add_le_add_left (by decide : 1 ≤ 2) _)))
  have hc := cauchy_fourier_polynomial K.pole ha _ hm x
  simp only [Complex.ofReal_mul] at hc
  rw [hc]
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Rat.coe_castHom, Rat.cast_mul,
    Complex.ofReal_mul, Complex.ofReal_ratCast]
  ring

/-- At frequency zero the Fourier polynomial equals the normalized mass coefficient. -/
public theorem high_gaussian_mass_polynomial_zero (K : HighGaussianKernel) :
    (highGaussianMassPolynomial K).eval₂ (Rat.castHom ℝ) 0 = 3 / 8 := by
  have h := high_gaussian_mass_transform K 0
  simp only [zero_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, abs_zero,
    Real.exp_zero] at h
  have hc (f : ℝ → ℝ) : (∫ t : ℝ, (f t : ℂ)) = (((∫ t : ℝ, f t) : ℝ) : ℂ) :=
    integral_ofReal (𝕜 := ℂ)
  rw [hc, high_gaussian_mass_exact] at h
  have hr := Complex.ofReal_injective h
  apply mul_left_cancel₀ Real.pi_ne_zero
  rw [← hr]
  ring

end PseudoPrime.PrimeTestBounds.MillerRabin

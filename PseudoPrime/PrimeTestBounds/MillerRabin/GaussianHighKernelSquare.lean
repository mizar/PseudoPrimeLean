/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighKernelData
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighKernelData
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic

/-! # The square numerator of the high Gaussian kernels -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The pole components reassembled in the manuscript's square form.
The identity applies away from the common pole of the two expressions. -/
public theorem high_gaussian_kernel_sum (K : HighGaussianKernel) {z : ℂ}
    (hz : z + (K.pole : ℂ) ≠ 0) :
    (∑ j ∈ Finset.range (2 * K.degree + 1),
        (K.expandedCoeff j : ℂ) * Complex.exp (5 * z) / (z + (K.pole : ℂ)) ^ (K.logPower j + 1)) =
      (K.normalization : ℂ) * Complex.exp (5 * z) *
          (K.polynomial.eval₂ (Rat.castHom ℂ) (z + (K.pole : ℂ))) ^ 2 /
        (z + (K.pole : ℂ)) ^ (2 * K.degree + 4) := by
  let w := z + (K.pole : ℂ)
  have hd := Polynomial.natDegree_pow_le_of_le 2 (high_gaussian_polynomial_degree K)
  have he := Polynomial.eval₂_eq_sum_range' (Rat.castHom ℂ) (Nat.lt_succ_of_le hd) w
  rw [Polynomial.eval₂_pow] at he
  change
    (∑ j ∈ Finset.range (2 * K.degree + 1),
        (K.expandedCoeff j : ℂ) * Complex.exp (5 * z) / w ^ (K.logPower j + 1)) =
      (K.normalization : ℂ) * Complex.exp (5 * z) * (K.polynomial.eval₂ (Rat.castHom ℂ) w) ^ 2 /
        w ^ (2 * K.degree + 4)
  rw [he, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ 2 * K.degree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hk : K.logPower j + 1 + j = 2 * K.degree + 4 := by
    unfold HighGaussianKernel.logPower
    change (2 * K.degree - j + 4) + j = 2 * K.degree + 4
    rw [Nat.add_right_comm, Nat.sub_add_cancel hj']
  rw [← hk, pow_add w (K.logPower j + 1) j, HighGaussianKernel.expandedCoeff, Rat.cast_mul]
  change
    _ =
      (K.normalization : ℂ) * Complex.exp (5 * z) *
          ((((K.polynomial ^ 2).coeff j : ℚ) : ℂ) * w ^ j) /
        (w ^ (K.logPower j + 1) * w ^ j)
  field_simp [show w ≠ 0 from hz]

/-- On the imaginary axis the modulation has unit norm. The absolute
mass integrand is the squared polynomial norm divided by the pole norm. -/
public theorem high_gaussian_kernel_norm (K : HighGaussianKernel) (t : ℝ) :
    ‖∑ j ∈ Finset.range (2 * K.degree + 1),
          (K.expandedCoeff j : ℂ) * Complex.exp (5 * (Complex.I * (t : ℂ))) /
            (Complex.I * (t : ℂ) + (K.pole : ℂ)) ^ (K.logPower j + 1)‖ =
      (K.normalization : ℝ) *
          ‖K.polynomial.eval₂ (Rat.castHom ℂ) (Complex.I * (t : ℂ) + (K.pole : ℂ))‖ ^ 2 /
        ‖Complex.I * (t : ℂ) + (K.pole : ℂ)‖ ^ (2 * K.degree + 4) := by
  have hρ : (0 : ℝ) < K.pole := (by norm_num only : (0 : ℝ) < 1 / 2).trans (high_gaussian_pole_gt K)
  have hreal : (Complex.I * (t : ℂ) + (K.pole : ℂ)).re = (K.pole : ℝ) := by
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, zero_add, ← Complex.ofReal_ratCast]
  have hz : Complex.I * (t : ℂ) + (K.pole : ℂ) ≠ 0 := by
    intro he
    rw [he, Complex.zero_re] at hreal
    exact hρ.ne' hreal.symm
  have he : ‖Complex.exp (5 * (Complex.I * (t : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.re_ofNat, Complex.im_ofNat, zero_mul, mul_zero, sub_zero, Real.exp_zero]
  rw [high_gaussian_kernel_sum K hz, norm_div, norm_mul, norm_mul, norm_pow, norm_pow,
    Complex.norm_ratCast, abs_of_pos (Rat.cast_pos.mpr (high_gaussian_normalization_pos K)), he,
    mul_one]

end PseudoPrime.PrimeTestBounds.MillerRabin

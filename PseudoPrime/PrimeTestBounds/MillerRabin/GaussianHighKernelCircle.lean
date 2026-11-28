/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighKernelSquare
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighKernelData
import Mathlib.Tactic

/-! # Circle coordinates for the high Gaussian Gram integral -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The normalized compact coefficient polynomial in the circle variable.
Its coefficients are the manuscript's ticks divided by their total. -/
public noncomputable def HighGaussianKernel.circlePoly (K : HighGaussianKernel) (z : ℂ) : ℂ :=
  let v := coefficientTicks K
  ∑ j ∈ Finset.range (K.degree + 1), ((v[j]?.getD 0 : ℤ) : ℂ) / (v.sum : ℂ) * z ^ j

/-- The manuscript's compact polynomial becomes a circle polynomial after
dividing by the pole power. The two extra powers are retained explicitly. -/
public theorem high_gaussian_circle_factor (K : HighGaussianKernel) {w : ℂ} (hw : w ≠ 0) :
    K.polynomial.eval₂ (Rat.castHom ℂ) w / w ^ (K.degree + 2) =
      K.circlePoly ((w - 2 * (K.pole : ℂ)) / w) / w ^ 2 := by
  dsimp only [HighGaussianKernel.polynomial, HighGaussianKernel.circlePoly]
  rw [Polynomial.eval₂_finsetSum, Finset.sum_div, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ K.degree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  let v := coefficientTicks K
  have hcast (q : ℚ) : (Rat.castHom ℂ) q = (q : ℂ) := rfl
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Polynomial.eval₂_sub, hcast, Rat.cast_div, Rat.cast_intCast, Rat.cast_mul, Rat.cast_ofNat]
  rw [div_pow,
    show w ^ (K.degree + 2) = w ^ (K.degree - j) * w ^ j * w ^ 2 by
      rw [← pow_add w (K.degree - j) j, Nat.sub_add_cancel hj', pow_add]]
  field_simp [hw]

/-- The ratio of the two conjugate-length shifts on the vertical line has
unit norm. This is the circle variable used in the Gram integral. -/
public theorem high_gaussian_circle_norm {a t : ℝ} (ha : 0 < a) :
    ‖(Complex.I * (t : ℂ) - (a : ℂ)) / (Complex.I * (t : ℂ) + (a : ℂ))‖ = 1 := by
  have he :
    Complex.normSq (Complex.I * (t : ℂ) - (a : ℂ)) =
      Complex.normSq (Complex.I * (t : ℂ) + (a : ℂ)) := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.sub_re, Complex.add_im, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_mul, one_mul, add_zero, zero_add, sub_zero, zero_sub,
      neg_mul, mul_neg, neg_neg]
  have hd : Complex.I * (t : ℂ) + (a : ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, zero_add, Complex.zero_re] at hr
    exact ha.ne' hr
  rw [norm_div, Complex.norm_def, Complex.norm_def, he,
    div_self
      (by
        rw [← Complex.norm_def]; exact norm_ne_zero_iff.mpr hd)]

/-- Rewrite the absolute kernel mass on the imaginary axis in the circle
coordinate. Only a fourth power remains in the denominator. -/
public theorem high_gaussian_circle_mass (K : HighGaussianKernel) (t : ℝ) :
    let w := Complex.I * (t : ℂ) + (K.pole : ℂ)
    ‖∑ j ∈ Finset.range (2 * K.degree + 1),
          (K.expandedCoeff j : ℂ) * Complex.exp (5 * (Complex.I * (t : ℂ))) /
            w ^ (K.logPower j + 1)‖ =
      (K.normalization : ℝ) * ‖K.circlePoly ((Complex.I * (t : ℂ) - (K.pole : ℂ)) / w)‖ ^ 2 /
        ‖w‖ ^ 4 := by
  intro w
  have hρ := high_gaussian_pole_gt K
  have hw : w ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [w, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, zero_add, Complex.zero_re,
      ← Complex.ofReal_ratCast] at hr
    linarith only [hρ, hr]
  have hcoord : w - 2 * (K.pole : ℂ) = Complex.I * (t : ℂ) - (K.pole : ℂ) := by
    dsimp only [w]
    ring
  have h := congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) (high_gaussian_circle_factor K hw)
  simp only [norm_div, norm_pow, div_pow, ← pow_mul] at h
  have hk : (K.degree + 2) * 2 = 2 * K.degree + 4 := by ring
  rw [hk, hcoord] at h
  change _ = (K.normalization : ℝ) * _ / ‖w‖ ^ 4
  rw [high_gaussian_kernel_norm]
  change
    (K.normalization : ℝ) * ‖K.polynomial.eval₂ (Rat.castHom ℂ) w‖ ^ 2 / ‖w‖ ^ (2 * K.degree + 4) =
      _
  rw [mul_div_assoc, h, ← mul_div_assoc]

end PseudoPrime.PrimeTestBounds.MillerRabin

/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.TwoPoleResolventBounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! # Rational single-pole functions and their proposed nonnegative Mellin profiles

The function and profile below are defined independently. The critical-line identities
are unconditional; they do not by themselves assert Mellin inversion or admissibility.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The function 2a exp(2cz)/(1+2az)^(2m), with totalized values at the pole.
Positive a locates its sole possible pole at -1/(2a); m=2,3 are the proposed
fourth- and sixth-order kernels. This definition does not assume Mellin admissibility. -/
noncomputable def rationalPoleFunction (m : ℕ) (a c : ℝ) (z : ℂ) : ℂ :=
  (2 * a : ℝ) * Complex.exp (2 * (c : ℂ) * z) / (1 + 2 * (a : ℂ) * z) ^ (2 * m)

/-- The real inverse-transform candidate v^(2m-1)exp(-v)/(2m-1)!,
v=(2c-log u)/(2a), on 0<u<=exp(2c), and zero elsewhere. For m>=1,a>0 it is
nonnegative. RationalPoleInversion proves inversion for this profile; admissible-kernel
construction additionally requires the strip and decay conditions. -/
noncomputable def rationalPoleProfile (m : ℕ) (a c u : ℝ) : ℝ :=
  if 0 < u ∧ Real.log u ≤ 2 * c then
    (((2 * c - Real.log u) / (2 * a)) ^ (2 * m - 1) *
      Real.exp (-((2 * c - Real.log u) / (2 * a)))) / ((2 * m - 1).factorial : ℕ)
  else 0

/-- For a>0 the proposed real profile is nonnegative at every argument. Its support
condition makes v nonnegative, and the factorial denominator is positive. This checks
the sign required by the nonnegative Mellin framework, independently of inversion. -/
theorem rationalPoleProfile_nonneg (m : ℕ) {a : ℝ} (ha : 0 < a) (c u : ℝ) :
    0 ≤ rationalPoleProfile m a c u := by
  unfold rationalPoleProfile
  split_ifs with h
  · exact div_nonneg (mul_nonneg (pow_nonneg
      (div_nonneg (sub_nonneg.mpr h.2) (mul_pos (by norm_num only) ha).le) _)
      (Real.exp_pos _).le) (Nat.cast_nonneg _)
  · exact le_refl 0

/-- Beyond exp(2c), the proposed profile is zero. Taking logarithms identifies the
upper support cutoff; no positivity of the pole parameter is needed here. Later
principal-sum estimates can therefore retain a finite upper support endpoint. -/
theorem rationalPoleProfile_eq_zero (m : ℕ) (a c : ℝ) {u : ℝ}
    (hu : Real.exp (2 * c) < u) : rationalPoleProfile m a c u = 0 := by
  have hp := (Real.exp_pos (2 * c)).trans hu
  have hl : 2 * c < Real.log u := (Real.lt_log_iff_exp_lt hp).mpr hu
  exact ite_eq_right (fun h ↦ (not_le_of_gt hl) h.2)

/-- On the imaginary axis and a>0, the exact norm is 2a/(1+(2at)^2)^m.
The phase exponential has norm one and the even denominator power removes its square
root. This identity supplies whole-height rational majorants for both proposed kernels. -/
theorem norm_rationalPoleFunction (m : ℕ) {a c : ℝ} (ha : 0 < a) (t : ℝ) :
    ‖rationalPoleFunction m a c (Complex.I * t)‖ = 2 * a / (1 + (2 * a * t) ^ 2) ^ m := by
  have he : ‖Complex.exp (2 * (c : ℂ) * (Complex.I * t))‖ = 1 := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.ofReal_re, Complex.im_ofNat,
      Complex.ofReal_im, mul_zero, sub_zero, Complex.I_re, zero_mul, Complex.I_im,
      Complex.mul_im, add_zero, Real.exp_zero]
  have hd : ‖1 + 2 * (a : ℂ) * (Complex.I * t)‖ ^ 2 = 1 + (2 * a * t)^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.re_ofNat,
      Complex.ofReal_re, Complex.im_ofNat, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.I_re, zero_mul, Complex.I_im, Complex.mul_im, add_zero, zero_add,
      mul_one, Complex.add_im, Complex.one_im]
    ring
  rw [rationalPoleFunction, norm_div, norm_mul, he, mul_one, norm_pow, pow_mul, hd,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num only) ha)]

end PseudoPrime.Analysis

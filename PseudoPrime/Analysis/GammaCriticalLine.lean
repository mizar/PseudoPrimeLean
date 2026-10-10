/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Tactic

/-! # Gamma norms on the line of real part one half

Euler reflection and conjugation identify the squared norm with a real
hyperbolic cosine. This supplies the absolute integrand for gamma-kernel bounds.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- At real height `t`, reflection sends `1/2+it` to its conjugate.
This identifies the two gamma factors in Euler's formula. -/
theorem one_sub_half_add_I (t : ℝ) :
    1 - ((1 / 2 : ℂ) + Complex.I * t) = starRingEnd ℂ ((1 / 2 : ℂ) + Complex.I * t) := by
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.div_ofNat_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero,
      sub_zero, add_zero, Complex.conj_re]
    norm_num only
  · simp only [Complex.sub_im, Complex.one_im, Complex.add_im, Complex.div_ofNat_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add,
      Complex.conj_im, zero_sub]

/-- The sine in Euler reflection on the half line is the real value
`cosh(πt)`. The addition formula removes the real half-period term. -/
theorem sin_pi_half_add_I (t : ℝ) :
    Complex.sin ((Real.pi : ℂ) * ((1 / 2 : ℂ) + Complex.I * t)) =
      (Real.cosh (Real.pi * t) : ℂ) := by
  have he :
    (Real.pi : ℂ) * ((1 / 2 : ℂ) + Complex.I * t) =
      (Real.pi : ℂ) / 2 + ((Real.pi * t : ℝ) : ℂ) * Complex.I := by
    rw [Complex.ofReal_mul]
    ring
  rw [he, Complex.sin_add_mul_I, Complex.sin_pi_div_two, Complex.cos_pi_div_two, one_mul, zero_mul,
    zero_mul, add_zero, ← Complex.ofReal_cosh]

/-- For every real height, the squared gamma norm on the half line is
`π/cosh(πt)`. Reflection and conjugation give the identity without any
asymptotic estimate. It controls gamma-kernel mass and its numerical bounds. -/
theorem norm_Gamma_half_add_I_sq (t : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)‖ ^ 2 = Real.pi / Real.cosh (Real.pi * t) := by
  have he := Complex.Gamma_mul_Gamma_one_sub ((1 / 2 : ℂ) + Complex.I * t)
  rw [one_sub_half_add_I, Complex.Gamma_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    sin_pi_half_add_I, ← Complex.ofReal_div] at he
  exact Complex.ofReal_injective he

/-- The gamma norm on the half line is the positive square root of
`π/cosh(πt)`. Apply the square-root identity to its squared norm.
This is the real density in gamma-kernel mass integrals. -/
theorem norm_Gamma_half_add_I (t : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)‖ =
      Real.sqrt (Real.pi / Real.cosh (Real.pi * t)) := by
  rw [← norm_Gamma_half_add_I_sq, Real.sqrt_sq (norm_nonneg _)]

/-- The squared gamma norm at height `t` is at most
`2π exp(-|πt|)`. Compare hyperbolic cosine with half the positive
exponential and use the exact reflection identity. This bounds the tail
of the gamma-kernel mass integral. -/
theorem norm_Gamma_half_add_I_sq_le_exp (t : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)‖ ^ 2 ≤
      2 * Real.pi * Real.exp (-|Real.pi * t|) := by
  rw [norm_Gamma_half_add_I_sq]
  apply (div_le_iff₀ (Real.cosh_pos (Real.pi * t))).mpr
  have hc : Real.exp |Real.pi * t| / 2 ≤ Real.cosh (Real.pi * t) := by
    rw [← Real.cosh_abs, Real.cosh_eq]
    linarith only [(Real.exp_pos (-|Real.pi * t|)).le]
  have hm :=
    mul_le_mul_of_nonneg_left hc
      (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) Real.pi_pos.le)
        (Real.exp_pos (-|Real.pi * t|)).le)
  have he : Real.exp (-|Real.pi * t|) * Real.exp |Real.pi * t| = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hz : 2 * Real.pi * Real.exp (-|Real.pi * t|) * (Real.exp |Real.pi * t| / 2) = Real.pi := by
    calc
      _ = Real.pi * (Real.exp (-|Real.pi * t|) * Real.exp |Real.pi * t|) := by ring
      _ = Real.pi := by rw [he, mul_one]
  rw [hz] at hm
  exact hm

/-- At every real height the gamma norm is bounded by an exponential
with rate one half of pi. Squaring reduces the comparison to Euler reflection.
This majorant proves vertical integrability and bounds mass tails. -/
theorem norm_Gamma_half_add_I_le_exp (t : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)‖ ≤
      Real.sqrt (2 * Real.pi) * Real.exp (-|Real.pi * t| / 2) := by
  have hs := norm_Gamma_half_add_I_sq_le_exp t
  have he : (Real.exp (-|Real.pi * t| / 2)) ^ 2 = Real.exp (-|Real.pi * t|) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hb :
    (Real.sqrt (2 * Real.pi) * Real.exp (-|Real.pi * t| / 2)) ^ 2 =
      2 * Real.pi * Real.exp (-|Real.pi * t|) := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg (by norm_num only) Real.pi_pos.le), he]
  have hp := mul_nonneg (Real.sqrt_nonneg (2 * Real.pi)) (Real.exp_pos (-|Real.pi * t| / 2)).le
  nlinarith only [hs, hb, hp, norm_nonneg (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t))]

end PseudoPrime.Analysis

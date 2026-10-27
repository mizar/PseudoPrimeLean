/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaEulerApproximationBounds

/-! # Gamma phase comparison using a finite Euler product -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a complex value, positive real scale and real ordinate.
Claim: multiplication by the imaginary power preserves the norm.
Proof: the power has norm one. Role: keep the Gamma error uniform in the scale. -/
theorem norm_mul_imaginary_power_eq (z : ℂ) {x : ℝ} (hx : 0 < x) (t : ℝ) :
    ‖z * (x : ℂ) ^ (Complex.I * t)‖ = ‖z‖ := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  norm_num only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, Real.rpow_zero, mul_one]

end PseudoPrime.Analysis

namespace PseudoPrime.Analysis

/-- Input: a complex value, its approximation, a positive scale and an ordinate.
Claim: the negative real phase is bounded by the approximate phase plus the norm error.
Proof: split the difference and use norm invariance of imaginary powers.
Role: transfer complex approximation certificates to one-sided spectral estimates. -/
theorem neg_re_phase_le_approx_add_error (a b : ℂ) {x : ℝ} (hx : 0 < x) (t : ℝ) :
    -(a * (x : ℂ) ^ (Complex.I * t)).re ≤ -(b * (x : ℂ) ^ (Complex.I * t)).re + ‖a - b‖ := by
  have he :
    -(a * (x : ℂ) ^ (Complex.I * t)).re =
      -(b * (x : ℂ) ^ (Complex.I * t)).re - ((a - b) * (x : ℂ) ^ (Complex.I * t)).re := by
    rw [sub_mul, Complex.sub_re]
    ring
  rw [he, sub_eq_add_neg]
  have hb :=
    (neg_le_abs (((a - b) * (x : ℂ) ^ (Complex.I * t)).re)).trans (Complex.abs_re_le_norm _)
  rw [norm_mul_imaginary_power_eq (a - b) hx t] at hb
  exact add_le_add_right hb _

/-- Input: a positive scale, real ordinate and nonzero Euler order.
Claim: the finite Euler phase plus sqrt(pi)/(2*n) bounds the Gamma phase above.
Proof: combine the uniform complex error with the signed-phase comparison.
Role: replace a Gamma phase premise by a finite elementary expression. -/
theorem neg_re_Gamma_phase_le_GammaSeq {x : ℝ} (hx : 0 < x) (t : ℝ) {n : ℕ} (hn : n ≠ 0) :
    -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re ≤
      -(Complex.GammaSeq ((1 / 2 : ℂ) + Complex.I * t) n * (x : ℂ) ^ (Complex.I * t)).re +
        Real.sqrt Real.pi / (2 * n) := by
  exact
    (neg_re_phase_le_approx_add_error (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t))
          (Complex.GammaSeq ((1 / 2 : ℂ) + Complex.I * t) n) hx t).trans
      (add_le_add_right (norm_Gamma_half_sub_GammaSeq_le t hn) _)

end PseudoPrime.Analysis

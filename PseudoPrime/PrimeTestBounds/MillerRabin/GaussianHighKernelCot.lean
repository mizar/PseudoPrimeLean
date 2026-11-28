/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-! # Cotangent coordinates for the high Gaussian mass -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For nonzero sine and nonzero scale, the Cayley coordinate of the
scaled cotangent is the point of the unit circle at twice the angle. -/
public theorem high_gaussian_cot_circle {a θ : ℝ} (ha : a ≠ 0) (hθ : Real.sin θ ≠ 0) :
    (Complex.I * (↑(a * Real.cot θ) : ℂ) - (a : ℂ)) /
        (Complex.I * (↑(a * Real.cot θ) : ℂ) + (a : ℂ)) =
      Complex.exp ((2 * (θ : ℂ)) * Complex.I) := by
  let S := (Real.sin θ : ℂ)
  let C := (Real.cos θ : ℂ)
  have hS : S ≠ 0 := Complex.ofReal_ne_zero.mpr hθ
  have hA : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have hunit : S ^ 2 + C ^ 2 = 1 := by
    simpa only [S, C, Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_one] using
      congrArg Complex.ofReal (Real.sin_sq_add_cos_sq θ)
  have hprod : (C - S * Complex.I) * (C + S * Complex.I) = 1 := by
    calc
      _ = S ^ 2 + C ^ 2 := by linear_combination -S ^ 2 * Complex.I_sq
      _ = 1 := hunit
  have hd :
    Complex.I * (a : ℂ) * (C / S) + (a : ℂ) = ((a : ℂ) * Complex.I / S) * (C - S * Complex.I) := by
    field_simp [hS]
    linear_combination S * Complex.I_sq
  have hn :
    Complex.I * (a : ℂ) * (C / S) - (a : ℂ) = ((a : ℂ) * Complex.I / S) * (C + S * Complex.I) := by
    field_simp [hS]
    linear_combination -S * Complex.I_sq
  rw [Real.cot_eq_cos_div_sin, Complex.ofReal_mul, Complex.ofReal_div, ← mul_assoc, hd, hn]
  rw [mul_div_mul_left _ _ (div_ne_zero (mul_ne_zero hA Complex.I_ne_zero) hS)]
  have hden : C - S * Complex.I ≠ 0 := by
    intro h
    rw [h, zero_mul] at hprod
    exact zero_ne_one hprod
  rw [show ((2 : ℂ) * (θ : ℂ)) * Complex.I = (θ : ℂ) * Complex.I + (θ : ℂ) * Complex.I from by ring,
    Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  change (C + S * Complex.I) / (C - S * Complex.I) = (C + S * Complex.I) * (C + S * Complex.I)
  apply (div_eq_iff hden).mpr
  rw [mul_assoc, mul_comm (C + S * Complex.I) (C - S * Complex.I), hprod, mul_one]

/-- The derivative of the scaled cotangent on the open integration interval. -/
public theorem high_gaussian_cot_deriv (a : ℝ) {θ : ℝ} (hθ : Real.sin θ ≠ 0) :
    HasDerivAt (fun u ↦ a * Real.cot u) (-a / Real.sin θ ^ 2) θ := by
  have h := ((Real.hasDerivAt_cos θ).div (Real.hasDerivAt_sin θ) hθ).const_mul a
  have he :
    a * ((-Real.sin θ * Real.sin θ - Real.cos θ * Real.cos θ) / Real.sin θ ^ 2) =
      -a / Real.sin θ ^ 2 := by
    rw [← mul_div_assoc,
      show -Real.sin θ * Real.sin θ - Real.cos θ * Real.cos θ = -1 from by
        nlinarith only [Real.sin_sq_add_cos_sq θ],
      mul_neg_one]
  simpa only [Real.cot_eq_cos_div_sin, Pi.div_apply, he] using h

/-- The inverse fourth-power mass and the absolute cotangent Jacobian
combine to the sine-squared weight in the manuscript's Gram integral. -/
public theorem high_gaussian_cot_jacobian {a θ : ℝ} (ha : 0 < a) (hθ : Real.sin θ ≠ 0) :
    a / Real.sin θ ^ 2 / ‖Complex.I * (↑(a * Real.cot θ) : ℂ) + (a : ℂ)‖ ^ 4 =
      Real.sin θ ^ 2 / a ^ 3 := by
  have hs : ‖Complex.I * (↑(a * Real.cot θ) : ℂ) + (a : ℂ)‖ ^ 2 = a ^ 2 / Real.sin θ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, one_mul, sub_zero,
      zero_add, add_zero, Real.cot_eq_cos_div_sin]
    field_simp [hθ]
    linear_combination Real.sin_sq_add_cos_sq θ
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hs]
  field_simp [hθ, ha.ne']

end PseudoPrime.PrimeTestBounds.MillerRabin

/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriangleShiftedArithmetic
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriangleShiftedGamma

/-! # Reciprocal gamma phases in the translated triangle formula -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Opposite Mellin phases add to twice the real cosine at a positive scale. -/
private theorem triangle_phase_pair {x : ℝ} (hx : 0 < x) (t : ℝ) :
    (x : ℂ) ^ (Complex.I * t) + ((x⁻¹ : ℝ) : ℂ) ^ (Complex.I * t) =
      (2 : ℂ) * (Real.cos (Real.log x * t) : ℂ) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (inv_pos.mpr hx).ne'), ←
    Complex.ofReal_log hx.le, ← Complex.ofReal_log (inv_pos.mpr hx).le, Real.log_inv,
    Complex.ofReal_neg, Complex.ofReal_cos, Complex.cos]
  push_cast
  ring_nf

/-- Adding the two central gamma integrals at reciprocal scales extracts the
cosine transform of the real part, with normalization one over pi. -/
theorem triangle_gamma_pair_re {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) :
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 5 / 4)
    let F (t : ℝ) := logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) * K.function (Complex.I * t)
    let G (y : ℝ) := ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, F t * (y : ℂ) ^ (Complex.I * t)
    (G x + G x⁻¹).re = (∫ t : ℝ, (F t).re * Real.cos (Real.log x * t)) / Real.pi := by
  intro K F G
  let A (y t : ℝ) := F t * (y : ℂ) ^ (Complex.I * t)
  have hA {y : ℝ} (hy : 0 < y) : MeasureTheory.Integrable (A y) := by
    have h :=
      LLS.PaperStatements.MellinKernel.integrable_gammaFactor_power_line K χ (c := 0) (x := y)
        (by norm_num only)
        (by
          change (0 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
        (by norm_num only) hy
    simpa only [A, F, Complex.ofReal_zero, zero_add, mul_assoc] using h
  have hs := (hA hx).add (hA (inv_pos.mpr hx))
  have he (t : ℝ) : (A x t + A x⁻¹ t).re = 2 * ((F t).re * Real.cos (Real.log x * t)) := by
    dsimp only [A]
    rw [← mul_add, triangle_phase_pair hx, ← mul_assoc]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    change ((F t).re * 2 - (F t).im * 0) * _ = _
    ring
  change
    (((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, A x t) +
          ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, A x⁻¹ t)).re =
      _
  rw [← mul_add, ← MeasureTheory.integral_add (hA hx) (hA (inv_pos.mpr hx))]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    show (∫ t : ℝ, A x t + A x⁻¹ t).re = (∫ t : ℝ, (A x t + A x⁻¹ t).re) from (integral_re hs).symm]
  simp_rw [he]
  rw [MeasureTheory.integral_const_mul]
  ring

/-- At the translated window center the real gamma pair costs less than 1/250
after normalization, by the cosine identity and the even-character integral bound. -/
theorem triangle_gamma_pair_bound {q : ℕ} {χ : DirichletCharacter ℂ q} (hev : χ.Even) {r : ℝ}
    (hr : 287 ≤ r) :
    let x := Real.exp (2 * Real.log r + 5 / 2)
    let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < 5 / 4)
    let G (y : ℝ) :=
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ,
          logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
            (K.function (Complex.I * t) * (y : ℂ) ^ (Complex.I * t))
    (2 / 5) * |(G x + G x⁻¹).re| < 1 / 250 := by
  intro x K G
  have he := triangle_gamma_pair_re χ (Real.exp_pos (2 * Real.log r + 5 / 2))
  dsimp only at he
  simp only [mul_assoc, Real.log_exp] at he
  change (2 / 5) * |((_) + (_ : ℂ)).re| < _
  rw [he, abs_div, abs_of_pos Real.pi_pos, ← mul_div_assoc]
  exact triangle_translated_gamma_bound hev hr

end PseudoPrime.PrimeTestBounds.MillerRabin

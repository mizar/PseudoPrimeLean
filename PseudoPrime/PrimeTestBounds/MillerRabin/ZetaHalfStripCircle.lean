/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaHalfStrip

/-! # Zeta strip bound in a form suitable for Jensen circles -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- If the squared norms differ by at most 12 and the denominator is at
least `d > 0`, their ratio is at most `exp (6 / d^2)`. Apply the square-root
and exponential upper bounds to the squared ratio. -/
private theorem strip_norm_ratio {A B d : ℝ} (hA : 0 ≤ A) (hd : 0 < d) (hdB : d ≤ B)
    (hdiff : A ^ 2 ≤ B ^ 2 + 12) : A / B ≤ Real.exp (6 / d ^ 2) := by
  have hB : 0 < B := lt_of_lt_of_le hd hdB
  have hd2 : 0 < d ^ 2 := pow_pos hd _
  have hB2 : 0 < B ^ 2 := pow_pos hB _
  have hpow : d ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hd.le hdB 2
  have hinv := one_div_le_one_div_of_le hd2 hpow
  have hsq : (A / B) ^ 2 ≤ 1 + 12 / d ^ 2 := by
    rw [div_pow]
    calc
      A ^ 2 / B ^ 2 ≤ (B ^ 2 + 12) / B ^ 2 := div_le_div_of_nonneg_right hdiff hB2.le
      _ = 1 + 12 / B ^ 2 := by rw [add_div, div_self hB2.ne']
      _ ≤ 1 + 12 / d ^ 2 := by
        simp only [one_div] at hinv
        simp only [div_eq_mul_inv]
        linarith only [hinv]
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (div_nonneg hA hB.le)] at hsqrt
  have hx : -1 ≤ 12 / d ^ 2 := by
    have hp : 0 ≤ 12 / d ^ 2 := div_nonneg (by norm_num only) hd2.le
    linarith only [hp]
  have hroot := Real.sqrt_one_add_le hx
  have he := Real.add_one_le_exp (6 / d ^ 2)
  have heq : 1 + (12 / d ^ 2) / 2 = 6 / d ^ 2 + 1 := by ring
  linarith only [hsqrt, hroot, he, heq]

/-- For a point in the closed strip at distance at least `d > 0` from the
pole, zeta has norm at most `(4/5) * ‖s+2‖ * exp (6/d^2)`. This form keeps
the pole-distance dependence needed to bound the left Jensen semicircle. -/
theorem norm_zeta_le_strip_exp {s : ℂ} {d : ℝ} (hlo : (-(1 / 2) : ℝ) ≤ s.re) (hhi : s.re ≤ 3 / 2)
    (hd : 0 < d) (hden : d ≤ ‖s - 1‖) :
    ‖riemannZeta s‖ ≤ (4 / 5 : ℝ) * ‖s + 2‖ * Real.exp (6 / d ^ 2) := by
  have hne : s ≠ 1 := by
    intro h
    rw [h, sub_self, norm_zero] at hden
    linarith only [hd, hden]
  have h1 := Complex.sq_norm (s - 1)
  have h2 := Complex.sq_norm (s + 2)
  rw [Complex.normSq_apply] at h1 h2
  have hre : (2 : ℂ).re = 2 := rfl
  have him : (2 : ℂ).im = 0 := rfl
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.one_re,
    Complex.one_im, hre, him, sub_zero, add_zero] at h1 h2
  have hdiff : ‖s + 2‖ ^ 2 ≤ ‖s - 1‖ ^ 2 + 12 := by nlinarith only [h1, h2, hhi]
  have hratio := strip_norm_ratio (norm_nonneg (s + 2)) hd hden hdiff
  have hm :=
    mul_le_mul_of_nonneg_left hratio
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4 / 5) (norm_nonneg (s + 2)))
  have hz := AnalyticNumberTheory.RiemannZeta.norm_zeta_le_strip hlo hhi hne
  have heq :
    (4 / 5 : ℝ) * ‖s + 2‖ ^ 2 / ‖s - 1‖ = ((4 / 5 : ℝ) * ‖s + 2‖) * (‖s + 2‖ / ‖s - 1‖) := by ring
  rw [heq] at hz
  exact hz.trans hm

/-- If `T ≥ 17` and a point in the strip has absolute ordinate between
`T - 2` and `T + 2`, then `‖ζ(s)‖ ≤ T * exp (6 / (T - 2)^2)`. The norm
of `s + 2` is at most `T + 3`, and the pole is at least `T - 2` away. -/
theorem norm_zeta_le_height {s : ℂ} {T : ℝ} (hT : 17 ≤ T) (hlo : (-(1 / 2) : ℝ) ≤ s.re)
    (hhi : s.re ≤ 3 / 2) (hmin : T - 2 ≤ |s.im|) (hmax : |s.im| ≤ T + 2) :
    ‖riemannZeta s‖ ≤ T * Real.exp (6 / (T - 2) ^ 2) := by
  have hd : 0 < T - 2 := by linarith only [hT]
  have him : (s - 1).im = s.im := by simp only [Complex.sub_im, Complex.one_im, sub_zero]
  have hden : T - 2 ≤ ‖s - 1‖ := by
    have h := Complex.abs_im_le_norm (s - 1)
    rw [him] at h
    exact hmin.trans h
  have hsq := Complex.sq_norm (s + 2)
  rw [Complex.normSq_apply] at hsq
  have hre : (2 : ℂ).re = 2 := rfl
  have him' : (2 : ℂ).im = 0 := rfl
  simp only [Complex.add_re, Complex.add_im, hre, him', add_zero] at hsq
  have hr : (s.re + 2) ^ 2 ≤ (7 / 2 : ℝ) ^ 2 := by nlinarith only [hlo, hhi]
  have hi : s.im ^ 2 ≤ (T + 2) ^ 2 := by
    have ha := abs_nonneg s.im
    have hab := abs_le.mp hmax
    nlinarith only [hT, ha, hmax, hab.1, hab.2, sq_abs s.im]
  have hpoly : (7 / 2 : ℝ) ^ 2 + (T + 2) ^ 2 ≤ (T + 3) ^ 2 := by nlinarith only [hT]
  have hnorm : ‖s + 2‖ ≤ T + 3 := by nlinarith only [hsq, hr, hi, hpoly, norm_nonneg (s + 2), hT]
  have hscalar : (4 / 5 : ℝ) * ‖s + 2‖ ≤ T := by linarith only [hnorm, hT]
  have hmain := norm_zeta_le_strip_exp hlo hhi hd hden
  have hm := mul_le_mul_of_nonneg_right hscalar (Real.exp_pos (6 / (T - 2) ^ 2)).le
  exact hmain.trans hm

end PseudoPrime.PrimeTestBounds.MillerRabin

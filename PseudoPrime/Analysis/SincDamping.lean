/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.SineMajorant
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Damped chord bound for the integrated zero term -/

public section

namespace PseudoPrime.Analysis

/-- The radial loss and the damped phase coefficient of the integrated zero term
are bounded by the additive smoothing width. -/
theorem sinc_damping_coefficients {η : ℝ} (hη : 0 ≤ η) :
    1 - Real.exp (-3 * η / 2) ≤ 3 / 2 * (1 - Real.exp (-η)) ∧
      η * Real.exp (-3 * η / 2) ≤ 1 - Real.exp (-η) := by
  let u := Real.exp (-η / 2)
  have h2 : u ^ 2 = Real.exp (-η) := by
    rw [← Real.exp_natCast_mul]; congr 1; ring
  have h3 : u ^ 3 = Real.exp (-3 * η / 2) := by
    rw [← Real.exp_natCast_mul]; congr 1; ring
  have hpoly :=
    mul_nonneg (sq_nonneg (1 - u)) (by linarith only [(Real.exp_pos (-η / 2))] : 0 ≤ 2 * u + 1)
  have hrad : Real.exp (-3 * η / 2) ≤ Real.exp (-η) := Real.exp_le_exp.mpr (by linarith only [hη])
  have ht := mul_le_mul_of_nonneg_right (Real.add_one_le_exp η) (Real.exp_pos (-η)).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at ht
  constructor
  · rw [← h2, ← h3]
    nlinarith only [hpoly]
  · linarith only [ht, mul_le_mul_of_nonneg_left hrad hη]

/-- Splitting the radial and angular increments retains the damping factor on the
chord. The angular increment is exactly twice the sine of the half angle. -/
theorem norm_damped_chord_le (θ r : ℝ) (hr : 0 ≤ r) (hu : r ≤ 1) :
    ‖1 - (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ ≤ 1 - r + r * (2 * |Real.sin (θ / 2)|) := by
  let w := Complex.exp (Complex.I * (θ : ℂ))
  have he : 1 - (r : ℂ) * w = ((1 - r : ℝ) : ℂ) + (r : ℂ) * (1 - w) := by
    rw [Complex.ofReal_sub, Complex.ofReal_one]
    ring
  change ‖1 - (r : ℂ) * w‖ ≤ _
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hr, abs_of_nonneg (sub_nonneg.mpr hu), norm_sub_rev]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 2)]

/-- For a positive absolute ordinate the normalized damped zero term is bounded by the
sinc weight divided by the ordinate plus the inverse-square radial correction. -/
theorem damped_chord_div_le_sinc {η y : ℝ} (hη : 0 < η) (hy : 0 < y) :
    ‖1 - (Real.exp (-3 * η / 2) : ℂ) * Complex.exp (Complex.I * ((η * y : ℝ) : ℂ))‖ /
        ((1 - Real.exp (-η)) * y ^ 2) ≤
      sincWeight (η / 2 * y) / y + (3 / 2) / y ^ 2 := by
  let r := Real.exp (-3 * η / 2)
  let d := 1 - Real.exp (-η)
  let z := η / 2 * y
  have hz : 0 < z := mul_pos (half_pos hη) hy
  have hd : 0 < d := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hη))
  have hk := (div_le_iff₀ hz).mp (abs_sin_div_le_sincWeight hz)
  have hk0 := (div_nonneg (abs_nonneg _) hz.le).trans (abs_sin_div_le_sincWeight hz)
  have hc := sinc_damping_coefficients hη.le
  have h :=
    norm_damped_chord_le (η * y) r (Real.exp_pos _).le
      (Real.exp_le_one_iff.mpr (by linarith only [hη]))
  rw [show η * y / 2 = z by
      dsimp only [z]; ring] at h
  have hs := mul_le_mul_of_nonneg_left hk (Real.exp_pos (-3 * η / 2)).le
  have ht := mul_le_mul_of_nonneg_right hc.2 (mul_nonneg hy.le hk0)
  apply (div_le_iff₀ (mul_pos hd (sq_pos_of_pos hy))).mpr
  have he :
    (sincWeight z / y + (3 / 2) / y ^ 2) * (d * y ^ 2) = d * y * sincWeight z + 3 / 2 * d := by
    field_simp [hy.ne']
  rw [he]
  dsimp only [d, r, z] at *
  nlinarith only [h, hs, ht, hc.1]

/-- Reflecting the phase preserves the length of a damped chord with real radius. -/
private theorem damped_chord_reflect (r u : ℝ) :
    ‖1 - (r : ℂ) * Complex.exp (Complex.I * ((-u : ℝ) : ℂ))‖ =
      ‖1 - (r : ℂ) * Complex.exp (Complex.I * (u : ℂ))‖ := by
  rw [← Complex.norm_conj (1 - (r : ℂ) * Complex.exp (Complex.I * (u : ℂ)))]
  simp only [map_sub, map_one, map_mul, ← Complex.exp_conj, Complex.conj_I, Complex.conj_ofReal,
    Complex.ofReal_neg, neg_mul, mul_neg]

/-- On the critical line the normalized exponential factor for either sign of
the ordinate obeys the sinc bound with the full integrated-formula denominator. -/
theorem critical_chord_le {η : ℝ} (hη : 0 < η) {ρ : ℂ} (hr : ρ.re = 1 / 2) (hy : 0 < |ρ.im|) :
    ‖1 - Complex.exp ((-η : ℝ) * (ρ + 1))‖ / ((1 - Real.exp (-η)) * ‖ρ * (ρ + 1)‖) ≤
      sincWeight (η / 2 * |ρ.im|) / |ρ.im| + (3 / 2) / |ρ.im| ^ 2 := by
  have he :
    ((-η : ℝ) : ℂ) * (ρ + 1) = ((-3 * η / 2 : ℝ) : ℂ) + Complex.I * ((-(η * ρ.im) : ℝ) : ℂ) := by
    apply Complex.ext <;>
      simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im, hr] <;>
      ring
  rw [he, Complex.exp_add, ← Complex.ofReal_exp]
  have hf :
    ‖1 - (Real.exp (-3 * η / 2) : ℂ) * Complex.exp (Complex.I * ((-(η * ρ.im) : ℝ) : ℂ))‖ =
      ‖1 - (Real.exp (-3 * η / 2) : ℂ) * Complex.exp (Complex.I * ((η * |ρ.im| : ℝ) : ℂ))‖ := by
    rcases le_total 0 ρ.im with h | h
    · rw [abs_of_nonneg h, damped_chord_reflect]
    · rw [abs_of_nonpos h, mul_neg]
  rw [hf]
  have hn := Complex.abs_im_le_norm (ρ + 1)
  simp only [Complex.add_im, Complex.one_im, add_zero] at hn
  have hd : |ρ.im| ^ 2 ≤ ‖ρ * (ρ + 1)‖ := by
    rw [sq, norm_mul]
    exact mul_le_mul (Complex.abs_im_le_norm _) hn hy.le (norm_nonneg _)
  have hp := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hη))
  exact
    (div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos hp (sq_pos_of_pos hy))
          (mul_le_mul_of_nonneg_left hd hp.le)).trans
      (damped_chord_div_le_sinc hη hy)

/-- The actual difference of endpoint powers at positive height x and x exp(-η)
is bounded by the damped sinc estimate after factoring out the endpoint power. -/
theorem critical_power_diff_le {x η : ℝ} (hx : 0 < x) (hη : 0 < η) {ρ : ℂ} (hr : ρ.re = 1 / 2)
    (hy : 0 < |ρ.im|) :
    ‖((x : ℂ) ^ (ρ + 1) - ((x * Real.exp (-η) : ℝ) : ℂ) ^ (ρ + 1)) / (ρ * (ρ + 1))‖ ≤
      x ^ (3 / 2 : ℝ) * (1 - Real.exp (-η)) *
        (sincWeight (η / 2 * |ρ.im|) / |ρ.im| + (3 / 2) / |ρ.im| ^ 2) := by
  have hp : ((Real.exp (-η) : ℝ) : ℂ) ^ (ρ + 1) = Complex.exp ((-η : ℝ) * (ρ + 1)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'), ←
      Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
  have hn : ‖(x : ℂ) ^ (ρ + 1)‖ = x ^ (3 / 2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.add_re, hr, Complex.one_re]
    norm_num only
  rw [Complex.ofReal_mul, Complex.ofReal_mul_cpow hx.le, hp, ← mul_one_sub, norm_div, norm_mul, hn]
  have hd := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hη))
  have h := critical_chord_le hη hr hy
  rw [mul_comm (1 - Real.exp (-η)), ← div_div, div_le_iff₀ hd] at h
  simpa only [mul_div_assoc, mul_assoc, mul_comm (1 - Real.exp (-η))] using
    mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hx.le (3 / 2 : ℝ))

end PseudoPrime.Analysis

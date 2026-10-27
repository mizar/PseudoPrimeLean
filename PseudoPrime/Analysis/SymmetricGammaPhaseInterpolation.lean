/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FiniteSignedPhaseTransport
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Quadratic cost for symmetric logarithmic Gamma-phase interpolation -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For every real argument, the first five nonnegative cosh-series terms
form an octic lower bound. Compare the finite partial sum with the convergent series.
This supports a second-height Gamma envelope without a numerical grid. -/
theorem cosh_ge_octic (z : ℝ) :
    1 + z ^ 2 / 2 + z ^ 4 / 24 + z ^ 6 / 720 + z ^ 8 / 40320 ≤ Real.cosh z := by
  have hn (n : ℕ) : 0 ≤ z ^ (2 * n) / ((2 * n).factorial : ℝ) := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg z) n
  have h := Summable.sum_le_tsum (Finset.range 5) (fun n _ ↦ hn n) (Real.hasSum_cosh z).summable
  rw [(Real.hasSum_cosh z).tsum_eq] at h
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, Nat.factorial] at h
  nlinarith only [h]

/-- For a complex value and symmetric real phase shifts, bound its negative
real part by the average at the two shifts plus norm(z)*d^2/2. Expand the real
parts and use the global quadratic cosine bound. This cancels first-order phase motion. -/
theorem negative_re_le_symmetric_phase_average (z : ℂ) (d : ℝ) :
    -z.re ≤
      (-(z * Complex.exp ((d : ℂ) * Complex.I)).re -
            (z * Complex.exp (((-d : ℝ) : ℂ) * Complex.I)).re) /
          2 +
        ‖z‖ * d ^ 2 / 2 := by
  have hc : 0 ≤ 1 - Real.cos d := sub_nonneg.mpr (Real.cos_le_one d)
  have hb : 1 - Real.cos d ≤ d ^ 2 / 2 := by linarith only [Real.one_sub_sq_div_two_le_cos (x := d)]
  have hr : -z.re ≤ ‖z‖ := (neg_le_abs z.re).trans (Complex.abs_re_le_norm z)
  have h1 := mul_le_mul_of_nonneg_right hr hc
  have h2 := mul_le_mul_of_nonneg_left hb (norm_nonneg z)
  simp only [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_neg,
    Real.sin_neg]
  nlinarith only [h1, h2]

/-- For every height, bound t^4*(1+t^2)^2 by (25/4)*cosh(pi*t).
Use the octic series and pi>3 with nonnegative even powers. This supplies the
polynomial denominator for the second-height Gamma norm bound. -/
theorem cosh_pi_mul_ge_second_height_polynomial (t : ℝ) :
    t ^ 4 * (1 + t ^ 2) ^ 2 ≤ (25 / 4 : ℝ) * Real.cosh (Real.pi * t) := by
  have h := cosh_ge_octic (Real.pi * t)
  rw [mul_pow, mul_pow, mul_pow, mul_pow] at h
  have hp (k : ℕ) : (3 : ℝ) ^ (2 * k) * t ^ (2 * k) ≤ Real.pi ^ (2 * k) * t ^ (2 * k) :=
    mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 3) Real.pi_gt_three.le (2 * k))
      (by
        rw [pow_mul]; exact pow_nonneg (sq_nonneg t) k)
  have h2 := hp 1
  have h4 := hp 2
  have h6 := hp 3
  have h8 := hp 4
  norm_num only at h2 h4 h6 h8
  nlinarith only [h, h2, h4, h6, h8, sq_nonneg t, pow_nonneg (sq_nonneg t) 2,
    pow_nonneg (sq_nonneg t) 3, pow_nonneg (sq_nonneg t) 4]

/-- For every real height, t^2*norm(Gamma(1/2+i*t))<=5/(1+t^2).
Combine the exact critical-line norm, pi<4 and the octic cosh bound.
This controls the quadratic error in symmetric logarithmic interpolation. -/
theorem gammaHalf_second_height_le_five_resolvent (t : ℝ) :
    t ^ 2 * ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)‖ ≤ 5 / (1 + t ^ 2) := by
  have hp := cosh_pi_mul_ge_second_height_polynomial t
  have hw :=
    mul_le_mul_of_nonneg_right Real.pi_lt_four.le
      (mul_nonneg (pow_nonneg (sq_nonneg t) 2) (sq_nonneg (1 + t ^ 2)))
  have hnum : Real.pi * t ^ 4 * (1 + t ^ 2) ^ 2 ≤ 25 * Real.cosh (Real.pi * t) := by
    nlinarith only [hw, hp]
  have hs : (t ^ 2 * ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)‖ * (1 + t ^ 2)) ^ 2 ≤ 25 := by
    rw [mul_pow, mul_pow, norm_Gamma_half_add_I_sq]
    convert (div_le_iff₀ (Real.cosh_pos (Real.pi * t))).mpr hnum using 1
    ring
  apply (le_div_iff₀ (by nlinarith only [sq_nonneg t] : (0 : ℝ) < 1 + t ^ 2)).mpr
  nlinarith only [hs]

/-- For any center logarithm r, shift d and real height, the negative Gamma
phase at r is bounded by its average at r-d and r+d plus 5*d^2/(2*(1+t^2)).
Factor the unit center phase and apply the second-height envelope. This is a
whole-height midpoint estimate with no height cutoff. -/
theorem gammaHalf_negative_phase_le_midpoint (r d t : ℝ) :
    -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) *
            Complex.exp (Complex.I * ((t * r : ℝ) : ℂ))).re ≤
      (-(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) *
                  Complex.exp (Complex.I * ((t * (r - d) : ℝ) : ℂ))).re -
            (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) *
                Complex.exp (Complex.I * ((t * (r + d) : ℝ) : ℂ))).re) /
          2 +
        5 * d ^ 2 / (2 * (1 + t ^ 2)) := by
  let G := Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)
  let z := G * Complex.exp (Complex.I * ((t * r : ℝ) : ℂ))
  have h := negative_re_le_symmetric_phase_average z (t * d)
  have hn : ‖z‖ = ‖G‖ := by
    dsimp only [z]
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
  have hplus :
    z * Complex.exp (((t * d : ℝ) : ℂ) * Complex.I) =
      G * Complex.exp (Complex.I * ((t * (r + d) : ℝ) : ℂ)) := by
    dsimp only [z]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    simp only [Complex.ofReal_mul, Complex.ofReal_add]
    ring
  have hminus :
    z * Complex.exp (((-(t * d) : ℝ) : ℂ) * Complex.I) =
      G * Complex.exp (Complex.I * ((t * (r - d) : ℝ) : ℂ)) := by
    dsimp only [z]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_neg]
    ring
  rw [hn, hplus, hminus] at h
  have hb := mul_le_mul_of_nonneg_right (gammaHalf_second_height_le_five_resolvent t) (sq_nonneg d)
  have he : ‖G‖ * (t * d) ^ 2 / 2 ≤ 5 * d ^ 2 / (2 * (1 + t ^ 2)) := by
    calc
      _ = (t ^ 2 * ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)‖ * d ^ 2) / 2 := by
        dsimp only [G]
        ring
      _ ≤ (5 / (1 + t ^ 2) * d ^ 2) / 2 := div_le_div_of_nonneg_right hb (by norm_num only)
      _ = _ := by rw [div_mul_eq_mul_div, div_div, mul_comm (1 + t ^ 2) 2]
  dsimp only [z, G] at h
  dsimp only [G] at he
  linarith only [h, he]

/-- For a positive scale and rational shift d, suppose one finite rational
resolvent majorizes both logarithmic endpoints. Its extension with delta=5*d^2/4
majorizes the actual Gamma phase at the center. Apply the midpoint estimate and
identify the added node exactly. This yields quadratic rather than linear scale cost. -/
theorem gammaHalf_phase_majorant_of_symmetric_anchors {x : ℝ} (hx : 0 < x) (l : List (ℚ × ℚ))
    (d : ℚ)
    (hminus :
      ∀ t : ℝ,
        -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) *
                Complex.exp (Complex.I * ((t * (Real.log x - d) : ℝ) : ℂ))).re ≤
          finiteSignedResolvent l t)
    (hplus :
      ∀ t : ℝ,
        -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) *
                Complex.exp (Complex.I * ((t * (Real.log x + d) : ℝ) : ℂ))).re ≤
          finiteSignedResolvent l t)
    (t : ℝ) :
    -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re ≤
      finiteSignedResolvent (logarithmicPhaseExtension l ((5 / 4) * d ^ 2)) t := by
  have hm := gammaHalf_negative_phase_le_midpoint (Real.log x) d t
  have h1 := hminus t
  have h2 := hplus t
  rw [imaginary_power_eq_phase hx, finiteSignedResolvent_logarithmicPhaseExtension]
  norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]
  rw [div_mul_eq_div_div] at hm
  have he : 2 * (5 / 4 * (d : ℝ) ^ 2) / (1 + t ^ 2) = 5 * (d : ℝ) ^ 2 / 2 / (1 + t ^ 2) := by ring
  rw [he]
  linarith only [hm, h1, h2]

end PseudoPrime.Analysis

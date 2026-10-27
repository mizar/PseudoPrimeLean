/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorNumericalBounds

/-! # Explicit complex gamma-factor bounds on the central line

Digamma's shifted half-plane bound gives a numerical linear envelope at every height.
The estimate controls the full complex norm for both character parities.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For GammaReal on 1/2≤Re s≤3/2, the full complex logarithmic derivative
has norm at most 10+|Im s|. Shift digamma to a positive half-plane and use
the numerical error bound eight. This controls the central archimedean contour. -/
theorem norm_logDeriv_GammaReal_le_linear {s : ℂ} (hl : 1 / 2 ≤ s.re) (hu : s.re ≤ 3 / 2) :
    ‖logDeriv Complex.Gammaℝ s‖ ≤ 10 + |s.im| := by
  have hp : 0 < s.re := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1 / 2) hl
  have hr : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    simpa only [Complex.ofReal_zero, add_zero] using
      half_add_ne_neg_nat_of_re_pos hp (a := 0) le_rfl
  have hz : (1 / 4 : ℝ) ≤ (s / 2).re := by
    rw [Complex.div_ofNat_re]
    linarith only [hl]
  have hd := Gamma.norm_digamma_le_linear_of_re_ge (by norm_num only : (0 : ℝ) < 1 / 4) hz
  norm_num only at hd
  have hn := Complex.norm_le_abs_re_add_abs_im (s / 2)
  simp only [Complex.div_ofNat_re, Complex.div_ofNat_im, abs_div, abs_of_nonneg hp.le,
    abs_of_pos (by norm_num only : (0 : ℝ) < 2)] at hn
  have hlog := Real.log_le_sub_one_of_pos Real.pi_pos
  have hnlog : ‖Complex.log (Real.pi : ℂ)‖ ≤ 3 := by
    rw [← Complex.ofReal_log Real.pi_pos.le, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith only [Real.pi_gt_three] : 1 ≤ Real.pi))]
    linarith only [hlog, Real.pi_lt_four]
  rw [logDeriv_Gammaℝ_of_half_ne_neg_nat hr]
  have hnorm := norm_add_le (-(Complex.log (Real.pi : ℂ)) / 2) (Complex.digamma (s / 2) / 2)
  simp only [norm_div, norm_neg, Complex.norm_two] at hnorm
  nlinarith only [hnorm, hd, hn, hnlog, hu, Real.pi_lt_four, Gamma.digammaLogErrorBound_le_eight,
    abs_nonneg s.im]

/-- On Re s=1/2, every character's gamma factor has logarithmic derivative
norm at most 10+|Im s|, uniformly in modulus and parity. Even and odd characters
reduce to GammaReal at real parts 1/2 and 3/2. This explicit full norm estimate
can be combined with fixed Gamma-kernel decay without an unknown compact bound. -/
theorem norm_logDeriv_gammaFactor_central_le_linear {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : s.re = 1 / 2) : ‖logDeriv χ.gammaFactor s‖ ≤ 10 + |s.im| := by
  have hp : 0 < s.re := by
    rw [hs]; norm_num only
  have hf : (1 : DirichletCharacter ℂ 1).gammaFactor = Complex.Gammaℝ := by
    funext z
    exact principal_modulus_one_even.gammaFactor_def z
  rcases logDeriv_gammaFactor_eq_one_or_one_shift χ hp with he | he
  · rw [he, hf]
    exact
      norm_logDeriv_GammaReal_le_linear (by rw [hs])
        (by
          rw [hs]; norm_num only)
  · rw [he, hf]
    have hr : (s + 1).re = 3 / 2 := by
      rw [Complex.add_re, Complex.one_re, hs]
      norm_num only
    have hb :=
      norm_logDeriv_GammaReal_le_linear (s := s + 1)
        (by
          rw [hr]; norm_num only)
        (by rw [hr])
    simpa only [Complex.add_im, Complex.one_im, add_zero] using hb

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction

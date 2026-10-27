/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorNumericalBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.CompletedVerticalGrowth
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogDerivativeNumericalBounds

/-! # Numerical completed logarithmic derivatives on reflected fixed lines

The ordinary inverse-gap estimate and a full gamma-factor norm bound control
the right line 17/16. The primitive functional equation reflects it to -1/16.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- On 1/2≤Re s≤3, GammaReal's full logarithmic derivative norm is at most
11+|Im s|. Shift digamma by one and use its explicit half-plane error bound.
The strip contains both parity arguments on the reflected fixed Mellin line. -/
private theorem norm_logDeriv_GammaReal_strip_le_eleven {s : ℂ} (hl : 1 / 2 ≤ s.re)
    (hu : s.re ≤ 3) : ‖logDeriv Complex.Gammaℝ s‖ ≤ 11 + |s.im| := by
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

/-- At real part 17/16, every character's gamma-factor logarithmic derivative
has norm at most 11+|Im s|. Parity reduces the bound to GammaReal on a fixed strip.
This supplies a numerical archimedean term for reflecting the left Mellin line. -/
theorem norm_logDeriv_gammaFactor_seventeen_sixteenths_le {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : s.re = 17 / 16) : ‖logDeriv χ.gammaFactor s‖ ≤ 11 + |s.im| := by
  have hp : 0 < s.re := by
    rw [hs]; norm_num only
  have hf : (1 : DirichletCharacter ℂ 1).gammaFactor = Complex.Gammaℝ := by
    funext z
    exact principal_modulus_one_even.gammaFactor_def z
  rcases logDeriv_gammaFactor_eq_one_or_one_shift χ hp with he | he
  · rw [he, hf]
    exact
      norm_logDeriv_GammaReal_strip_le_eleven
        (by
          rw [hs]; norm_num only)
        (by
          rw [hs]; norm_num only)
  · rw [he, hf]
    have hr : (s + 1).re = 33 / 16 := by
      rw [Complex.add_re, Complex.one_re, hs]
      norm_num only
    have hb :=
      norm_logDeriv_GammaReal_strip_le_eleven (s := s + 1)
        (by
          rw [hr]; norm_num only)
        (by
          rw [hr]; norm_num only)
    simpa only [Complex.add_im, Complex.one_im, add_zero] using hb

/-- For a nonprincipal character on Re s=17/16, the completed logarithmic
derivative has norm at most 283+|t|. The ordinary inverse-gap bound gives 272
and the gamma factor contributes 11+|t|. No RH assumption is needed.
This is the quantitative right-line input to the primitive functional equation. -/
theorem norm_logDeriv_completed_seventeen_sixteenths_le {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) (t : ℝ) :
    ‖logDeriv χ.completedLFunction (((17 / 16 : ℝ) : ℂ) + Complex.I * t)‖ ≤ 283 + |t| := by
  let s : ℂ := ((17 / 16 : ℝ) : ℂ) + Complex.I * t
  have hr : s.re = 17 / 16 := by
    simp only [s, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  have hi : s.im = t := by
    simp only [s, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, one_mul, zero_mul, zero_add]
  have hr1 : 1 ≤ s.re := by
    rw [hr]; norm_num only
  have hp : 0 < s.re := zero_lt_one.trans_le hr1
  have he :=
    logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular hne
      (completedLFunction_ne_zero_of_one_le_re hne hr1) (gammaFactor_ne_zero_of_re_pos χ hp)
      (analyticAt_gammaFactor_of_re_pos χ hp).differentiableAt
  have ho := norm_logDeriv_le_inv_gap χ (by norm_num only : (1 : ℝ) < 17 / 16) t
  norm_num only at ho
  rw [mul_comm (t : ℂ) Complex.I] at ho
  have hg := norm_logDeriv_gammaFactor_seventeen_sixteenths_le χ hr
  rw [hi] at hg
  have hc :
    logDeriv χ.completedLFunction s = logDeriv χ.LFunction s + logDeriv χ.gammaFactor s := by
    rw [he]; ring
  change ‖logDeriv χ.completedLFunction s‖ ≤ _
  rw [hc]
  have hn := norm_add_le (logDeriv χ.LFunction s) (logDeriv χ.gammaFactor s)
  nlinarith only [hn, ho, hg]

/-- For a primitive nonprincipal character with nonprincipal inverse, the
completed logarithmic derivative on Re s=-1/16 is bounded by norm(log q)+283+|t|.
Reflect to Re s=17/16 and isolate the conductor logarithm.
The estimate supplies a fixed numerical constant on the Gamma kernel's left line. -/
theorem norm_logDeriv_completed_neg_one_sixteenth_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (t : ℝ) :
    ‖logDeriv χ.completedLFunction (((-1 / 16 : ℝ) : ℂ) + Complex.I * t)‖ ≤
      ‖Complex.log (q : ℂ)‖ + 283 + |t| := by
  let s : ℂ := ((17 / 16 : ℝ) : ℂ) + Complex.I * ((-t : ℝ) : ℂ)
  have hr : 1 ≤ s.re := by
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
    norm_num only
  have he :=
    completedLFunction_logDeriv_functionalEquation_at hp hne
      (completedLFunction_ne_zero_of_one_le_re hinv hr)
  have hs_eq : 1 - s = ((-1 / 16 : ℝ) : ℂ) + Complex.I * t := by
    dsimp only [s]
    simp only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  rw [hs_eq] at he
  have hn := norm_add_le (Complex.log (q : ℂ)) (logDeriv χ⁻¹.completedLFunction s)
  rw [← he, norm_neg] at hn
  have hb := norm_logDeriv_completed_seventeen_sixteenths_le hinv (-t)
  rw [abs_neg] at hb
  exact hn.trans (by linarith only [hb])

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction

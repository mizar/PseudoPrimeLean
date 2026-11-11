/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Gamma.Conjugation
public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-! # Gamma factor on the left boundary of the zeta strip -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- On `Re s = -1/2`, the two Gamma factors in the completed zeta functional
equation differ in norm by `‖s/2‖`. Conjugation and the Gamma recurrence
give the exact identity, including at zero imaginary part. -/
theorem norm_gamma_left_factors {s : ℂ} (hs : s.re = -(1 / 2 : ℝ)) :
    ‖Complex.Gamma ((1 - s) / 2)‖ = ‖s / 2‖ * ‖Complex.Gamma (s / 2)‖ := by
  have hne : s / 2 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.div_ofNat_re, Complex.zero_re] at hre
    linarith only [hs, hre]
  have heq : (1 - s) / 2 = (starRingEnd ℂ) (s / 2) + 1 := by
    apply Complex.ext
    · simp only [Complex.div_ofNat_re, Complex.sub_re, Complex.one_re, Complex.conj_re,
        Complex.add_re]
      linarith only [hs]
    · simp only [Complex.div_ofNat_im, Complex.sub_im, Complex.one_im, Complex.conj_im,
        Complex.add_im, zero_sub, add_zero]
      ring
  rw [heq, Complex.Gamma_add_one _ ((map_ne_zero (starRingEnd ℂ)).2 hne), Complex.Gamma_conj,
    norm_mul]
  simp only [Complex.norm_conj]

/-- On `Re s = -1/2`, the denominator Gamma factor in the completed zeta
functional equation is nonzero. Its argument has real part `-1/4`, so it
cannot be a nonpositive integer. -/
theorem gamma_left_ne_zero {s : ℂ} (hs : s.re = -(1 / 2 : ℝ)) : Complex.Gamma (s / 2) ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro n hn
  have hre := congrArg Complex.re hn
  simp only [Complex.div_ofNat_re, Complex.neg_re, Complex.natCast_re] at hre
  rcases Nat.eq_zero_or_pos n with h | h
  · rw [h] at hre
    norm_num only [Nat.cast_zero, neg_zero] at hre
    linarith only [hs, hre]
  · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast h
    linarith only [hs, hre, h1]

/-- On `Re s = -1/2`, the norms of the completed-zeta Gamma factors have the
exact ratio `‖s‖ / (2π)`. Gamma conjugation and recurrence control the Gamma
part, while the real part of the exponent gives one reciprocal power of π. -/
theorem norm_gammaReal_left_factors {s : ℂ} (hs : s.re = -(1 / 2 : ℝ)) :
    ‖Complex.Gammaℝ (1 - s)‖ = (‖s‖ / (2 * Real.pi)) * ‖Complex.Gammaℝ s‖ := by
  rw [Complex.Gammaℝ, Complex.Gammaℝ, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, norm_gamma_left_factors hs]
  have hleft : (-(1 - s) / 2).re = -(3 / 4 : ℝ) := by
    simp only [Complex.div_ofNat_re, Complex.neg_re, Complex.sub_re, Complex.one_re]
    linarith only [hs]
  have hright : (-s / 2).re = (1 / 4 : ℝ) := by
    simp only [Complex.div_ofNat_re, Complex.neg_re]
    linarith only [hs]
  rw [hleft, hright]
  have hpi : Real.pi ^ (-(3 / 4 : ℝ)) = Real.pi ^ (1 / 4 : ℝ) / Real.pi := by
    have hp := Real.rpow_sub Real.pi_pos (1 / 4 : ℝ) 1
    rw [Real.rpow_one] at hp
    norm_num only at hp ⊢
    exact hp
  rw [hpi, norm_div, Complex.norm_ofNat]
  ring

/-- On `Re s = -1/2`, the functional equation gives the exact ratio of zeta
norms `‖ζ(s)‖ = ‖s‖ / (2π) * ‖ζ(1-s)‖`. The Gamma factors are nonzero on
this line, so their norm identity can be cancelled. -/
theorem norm_zeta_left_reflection {s : ℂ} (hs : s.re = -(1 / 2 : ℝ)) :
    ‖riemannZeta s‖ = (‖s‖ / (2 * Real.pi)) * ‖riemannZeta (1 - s)‖ := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs
    norm_num only at hs
  have h1s0 : 1 - s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hre
    linarith only [hs, hre]
  have hga : Complex.Gammaℝ s ≠ 0 := by
    rw [Complex.Gammaℝ]
    apply mul_ne_zero ?_ (gamma_left_ne_zero hs)
    apply norm_ne_zero_iff.mp
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    exact ne_of_gt (Real.rpow_pos_of_pos Real.pi_pos _)
  have hgb : Complex.Gammaℝ (1 - s) ≠ 0 := by
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp only [Complex.sub_re, Complex.one_re]
    linarith only [hs]
  have hz : Complex.Gammaℝ s * riemannZeta s = Complex.Gammaℝ (1 - s) * riemannZeta (1 - s) := by
    rw [riemannZeta_def_of_ne_zero hs0, riemannZeta_def_of_ne_zero h1s0,
      completedRiemannZeta_one_sub, mul_div_cancel₀ _ hga, mul_div_cancel₀ _ hgb]
  have hn := congrArg norm hz
  rw [norm_mul, norm_mul, norm_gammaReal_left_factors hs] at hn
  have hg : 0 < ‖Complex.Gammaℝ s‖ := norm_pos_iff.mpr hga
  have heq :
    ‖Complex.Gammaℝ s‖ * ‖riemannZeta s‖ =
      ‖Complex.Gammaℝ s‖ * ((‖s‖ / (2 * Real.pi)) * ‖riemannZeta (1 - s)‖) := by
    nlinarith only [hn]
  exact (mul_left_cancel₀ (ne_of_gt hg)) heq

end PseudoPrime.AnalyticNumberTheory.RiemannZeta

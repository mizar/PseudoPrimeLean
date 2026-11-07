/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleTripleMass
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaPrincipalEulerBudget

/-! # Gamma estimates at the refined sixth-pole point -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The real digamma value at `79/100` is strictly below `-443/500`.
The first eight positive terms of the reciprocal-difference series and the
lower bound for Euler's constant give a rational certificate. This bounds
the undifferentiated even Gamma contribution in the refined zero formula. -/
theorem refined_digamma_point_lt :
    (Complex.digamma ((79 / 100 : ℝ) : ℂ)).re < -(443 / 500 : ℝ) := by
  have h :=
    AnalyticNumberTheory.Gamma.real_digamma_difference_ge_prefix (a := 79 / 100) (r := 1)
      (by norm_num only) (by norm_num only) 8
  norm_num only [Complex.ofReal_one, Complex.digamma_one, Complex.neg_re, Complex.ofReal_re,
    Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at h
  have he := Real.one_half_lt_eulerMascheroniConstant
  linarith only [h, he]

/-- For an even character, the real Gamma logarithmic derivative at the
refined ordinary point `79/50` is below `-943/1000`. The half-argument
formula, the certified digamma bound and `1 ≤ log π` preserve its negative
sign. This is the zeroth-order term of the refined Gamma correction. -/
theorem refined_gamma_even_point_lt {q : ℕ} {χ : DirichletCharacter ℂ q} (he : χ.Even) :
    (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + 27 / 25 : ℝ) : ℂ)).re < -(943 / 1000 : ℝ) := by
  have h :=
    AnalyticNumberTheory.DirichletLFunction.re_gammaFactor_even he (σ := (1 / 2 : ℝ) + 27 / 25)
      (by norm_num only)
  have hc : (((1 / 2 : ℝ) + 27 / 25) / 2 : ℝ) = 79 / 100 := by norm_num only
  rw [hc] at h
  have hp := AnalyticNumberTheory.Gamma.real_log_pi_ge_one
  have hd := refined_digamma_point_lt
  linarith only [h, hp, hd]

end PseudoPrime.PrimeTestBounds.MillerRabin

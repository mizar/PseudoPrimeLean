/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.LogarithmicMellinInversion
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.Basic

/-!
# Shifted logarithmic Perron integrals for Dirichlet characters

The finite logarithmic sum on a line shifted by sigma is expressed using the logarithmic
derivative of the Dirichlet L-function. No zero hypothesis is required for this right-edge
identity; shifted residue evaluation is a separate step.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For any complex character of nonzero level, real x and sigma and complex s, define
the logarithmic Perron kernel -L'(sigma+s)/L(sigma+s) times x^s/s^2, using totalized
division and powers. For x > 0 and a nonprincipal character with sigma >= 1, its
origin regularization gives the residue coefficient before integrating in sigma. -/
noncomputable def shiftedLogContourKernel {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x σ : ℝ)
    (s : ℂ) : ℂ :=
  -deriv χ.LFunction ((σ : ℂ) + s) / χ.LFunction ((σ : ℂ) + s) * (x : ℂ) ^ s / s ^ 2

/-- For x>0, sigma>=1, and tau>0, the finite character-Mangoldt sum weighted by
n^(-sigma) log(x/n) equals the normalized integral on Re s=tau.
Mellin inversion and absolute convergence identify the series with the logarithmic derivative.
This supplies the right edge for the shifted contour formula underlying logarithmic L-values. -/
theorem shifted_logarithmic_sum_eq_integral {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {x σ τ : ℝ} (hx : 0 < x) (hσ : 1 ≤ σ) (hτ : 0 < τ) :
    General.logarithmicWeightedSum
        (General.shiftedLSeriesCoefficient
          (fun n ↦ χ (n : ZMod N) * (ArithmeticFunction.vonMangoldt n : ℂ)) σ)
        x =
      (2 * Real.pi : ℝ)⁻¹ • ∫ y : ℝ, shiftedLogContourKernel χ x σ ((τ : ℂ) + y * Complex.I) := by
  have hστ : 1 < σ + τ := by linarith only [hσ, hτ]
  have hsum :=
    χ.LSeriesSummable_twist_vonMangoldt
      (show 1 < ((σ + τ : ℝ) : ℂ).re by simpa only [Complex.ofReal_re] using hστ)
  have hsum' :
    LSeriesSummable (fun n ↦ χ (n : ZMod N) * (ArithmeticFunction.vonMangoldt n : ℂ))
      ((σ + τ : ℝ) : ℂ) :=
    hsum
  have ha' : χ ((0 : ℕ) : ZMod N) * (ArithmeticFunction.vonMangoldt 0 : ℂ) = 0 := by
    rw [ArithmeticFunction.map_zero, Complex.ofReal_zero, mul_zero]
  rw [General.logarithmicWeightedSum_shifted_eq_integral_LSeries _ ha' σ hx hτ hsum']
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  have hs : 1 < (((σ + τ : ℝ) : ℂ) + y * Complex.I).re := by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
      mul_zero, zero_mul, sub_zero, add_zero] using hστ
  rw [lSeries_twist_vonMangoldt_eq_neg_logDeriv_dirichletLFunction_of_one_lt_re χ hs]
  simp only [shiftedLogContourKernel, Complex.ofReal_add, add_assoc]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction

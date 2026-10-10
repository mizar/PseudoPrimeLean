/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.ReciprocalMellinInversion
public import PseudoPrime.LLS.Extensions.MangoldtSeries

/-!
# Arithmetic reciprocal Mellin inversion for general L-functions

The absolutely convergent Mangoldt series for `-L'/L` gives the finite sum with weight
`Λ(n)/n * (1 - n/x)` by reciprocal Mellin inversion on `Re s = 1 + τ`.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- The general L-function's smoothed reciprocal sum is the generic smoothed sum whose
coefficients are `a_f(n) Λ(n)` shifted by `n^(-1)`. Rewrite real weights and complex powers
termwise. No admissibility assumption is needed; this identifies the input to Mellin inversion. -/
theorem reciprocalWeightedSum_eq_shifted (f : GeneralLFunction) (x : ℝ) :
    f.reciprocalWeightedSum x =
      AnalyticNumberTheory.General.reciprocalWeightedSum
        (AnalyticNumberTheory.General.shiftedLSeriesCoefficient f.mangoldtSeriesCoefficient 1)
        x := by
  unfold reciprocalWeightedSum AnalyticNumberTheory.General.reciprocalWeightedSum
  apply Finset.sum_congr rfl
  intro n _
  simp only [AnalyticNumberTheory.General.shiftedLSeriesCoefficient, mangoldtSeriesCoefficient,
    Complex.ofReal_one, Complex.cpow_neg, Complex.cpow_one, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_one]
  ring

/-- For admissible data and positive `x,τ`, the smoothed reciprocal sum equals the normalized
vertical integral of `-L'/L(1 + τ + iy)` with kernel `x^z / (z (z + 1))`.
Absolute Mangoldt-series convergence and reciprocal Mellin inversion give the identity.
This is the arithmetic side of the generalized reciprocal explicit formula. -/
theorem reciprocalWeightedSum_eq_integral_logDeriv (f : GeneralLFunction) (hf : f.IsAdmissible)
    {x τ : ℝ} (hx : 0 < x) (hτ : 0 < τ) :
    f.reciprocalWeightedSum x =
      (2 * Real.pi : ℝ)⁻¹ •
        ∫ y : ℝ,
          -logDeriv f.L (((1 + τ : ℝ) : ℂ) + y * Complex.I) *
            (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
            (((τ : ℂ) + y * Complex.I) * ((τ : ℂ) + y * Complex.I + 1)) := by
  have hστ : 1 < 1 + τ := lt_add_of_pos_right 1 hτ
  have hzero : f.mangoldtSeriesCoefficient 0 = 0 := by
    rw [mangoldtSeriesCoefficient, ArithmeticFunction.map_zero, Complex.ofReal_zero, mul_zero]
  rw [reciprocalWeightedSum_eq_shifted,
    AnalyticNumberTheory.General.reciprocalWeightedSum_shifted_eq_integral_LSeries
      f.mangoldtSeriesCoefficient hzero 1 hx hτ
      (LSeriesSummable_mangoldtSeriesCoefficient f hf
        (by
          simpa only [Complex.ofReal_re] using hστ
          ))]
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  have hr : 1 < (((1 + τ : ℝ) : ℂ) + y * Complex.I).re := by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_self, add_zero] using hστ
  rw [logDeriv_ordinary_eq_neg_mangoldtSeries f hf hr, neg_neg]

/-- For admissible data and positive `x,τ`, the ordinary reciprocal Mellin integrand
on `Re s = 1 + τ` is integrable. Apply shifted coefficient-series integrability and the
negative Mangoldt-series identity for `L'/L`. This permits subtracting the completion
factor in the completed reciprocal integral. -/
theorem integrable_reciprocalMellin_logDeriv (f : GeneralLFunction) (hf : f.IsAdmissible)
    {x τ : ℝ} (hx : 0 < x) (hτ : 0 < τ) :
    MeasureTheory.Integrable (fun y : ℝ ↦
      -logDeriv f.L (((1 + τ : ℝ) : ℂ) + y * Complex.I) *
        (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
        (((τ : ℂ) + y * Complex.I) * ((τ : ℂ) + y * Complex.I + 1))) := by
  have hs : 1 < 1 + τ := lt_add_of_pos_right 1 hτ
  have hz : f.mangoldtSeriesCoefficient 0 = 0 := by
    rw [mangoldtSeriesCoefficient, ArithmeticFunction.map_zero, Complex.ofReal_zero, mul_zero]
  have hi := AnalyticNumberTheory.General.integrable_reciprocalMellin_shiftedLSeries
    f.mangoldtSeriesCoefficient hz 1 hx hτ
    (LSeriesSummable_mangoldtSeriesCoefficient f hf (by
      simpa only [Complex.ofReal_re] using hs
      ))
  apply hi.congr
  filter_upwards with y
  have hr : 1 < (((1 + τ : ℝ) : ℂ) + y * Complex.I).re := by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_self, add_zero] using hs
  rw [logDeriv_ordinary_eq_neg_mangoldtSeries f hf hr, neg_neg]

end PseudoPrime.LLS.Extensions.GeneralLFunction

/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.MellinTestInversion
public import PseudoPrime.Analysis.IntegralSeries
public import Mathlib.NumberTheory.LSeries.Deriv

/-!
# Coefficient series in compact-test Mellin integrals

Absolute convergence supplies a summable L1 majorant. Mellin inversion then
evaluates the individual coefficients and the full arithmetic sum.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- The n-th coefficient L-series term multiplied by a complex weight along
the vertical line of real part sigma. Index zero is totalized to zero by
LSeries.term. This family is integrated termwise to evaluate the arithmetic
side of a Mellin explicit formula. -/
noncomputable def mellinLSeriesTerm (a : ℕ → ℂ) (W : ℂ → ℂ) (σ : ℝ) (n : ℕ) (T : ℝ) : ℂ :=
  LSeries.term a ((σ : ℂ) + T * Complex.I) n * W ((σ : ℂ) + T * Complex.I)

/-- For any coefficient sequence and weight, the vertical weighted term norm
equals the real-line L-series term norm times the weight norm. The modulus
of the imaginary complex power is one. This supplies a height-independent
coefficient majorant for Tonelli and termwise integration. -/
theorem norm_mellinLSeriesTerm (a : ℕ → ℂ) (W : ℂ → ℂ) (σ : ℝ) (n : ℕ) (T : ℝ) :
    ‖mellinLSeriesTerm a W σ n T‖ = ‖LSeries.term a (σ : ℂ) n‖ * ‖W ((σ : ℂ) + T * Complex.I)‖ := by
  simp only [mellinLSeriesTerm, norm_mul, LSeries.norm_term_eq, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
    add_zero]

/-- For a vertically integrable complex weight, each weighted L-series term
is integrable on that line. The coefficient term is continuous and its norm
is constant in height; multiply the weight's integrable norm by that constant.
This is the individual-integrability premise for exchanging the series and integral. -/
theorem integrable_mellinLSeriesTerm (a : ℕ → ℂ) (W : ℂ → ℂ) (σ : ℝ)
    (hw : Complex.VerticalIntegrable W σ) (n : ℕ) :
    MeasureTheory.Integrable (mellinLSeriesTerm a W σ n) := by
  have hterm : Continuous (fun T : ℝ ↦ LSeries.term a ((σ : ℂ) + T * Complex.I) n) :=
    (continuous_iff_continuousAt.mpr (fun s ↦ (LSeries.hasDerivAt_term a n s).continuousAt)).comp
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
  apply
    (hw.norm.const_mul ‖LSeries.term a (σ : ℂ) n‖).mono'
      (hterm.aestronglyMeasurable.mul hw.aestronglyMeasurable)
  exact MeasureTheory.ae_of_all _ fun T ↦ (norm_mellinLSeriesTerm a W σ n T).le

/-- Absolute convergence of the coefficient L-series at sigma makes the
integrated norms of its weighted vertical terms summable. Each integral
factors as the coefficient term norm times the weight's integrated norm.
The conclusion uses the total Bochner integral; vertical integrability is
supplied separately when applying the integral-exchange theorem. -/
theorem summable_integral_norm_mellinLSeriesTerm (a : ℕ → ℂ) (W : ℂ → ℂ) (σ : ℝ)
    (hs : LSeriesSummable a (σ : ℂ)) :
    Summable (fun n : ℕ ↦ ∫ T : ℝ, ‖mellinLSeriesTerm a W σ n T‖) := by
  apply (hs.norm.mul_right (∫ T : ℝ, ‖W ((σ : ℂ) + T * Complex.I)‖)).congr
  intro n
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  exact MeasureTheory.ae_of_all _ fun T ↦ (norm_mellinLSeriesTerm a W σ n T).symm

/-- For an absolutely convergent coefficient L-series and a vertically integrable
weight, the vertical integral of their product equals the sum of individual
term integrals. The constant-amplitude majorant makes the integrated norms
summable, so the Bochner integral commutes with the coefficient sum.
This is the analytic interchange used before Mellin inversion. -/
theorem integral_LSeries_mellin_eq_tsum (a : ℕ → ℂ) (W : ℂ → ℂ) (σ : ℝ)
    (hs : LSeriesSummable a (σ : ℂ)) (hw : Complex.VerticalIntegrable W σ) :
    (∫ T : ℝ, LSeries a ((σ : ℂ) + T * Complex.I) * W ((σ : ℂ) + T * Complex.I)) =
      ∑' n : ℕ, ∫ T : ℝ, mellinLSeriesTerm a W σ n T := by
  have he :=
    (MeasureTheory.hasSum_integral_of_summable_integral_norm (integrable_mellinLSeriesTerm a W σ hw)
        (summable_integral_norm_mellinLSeriesTerm a W σ hs)).tsum_eq
  rw [he]
  apply MeasureTheory.integral_congr_ae
  exact MeasureTheory.ae_of_all _ fun T ↦ by simp only [mellinLSeriesTerm, tsum_mul_right, LSeries]

/-- For a coefficient sequence vanishing at zero and an even smooth compact
logarithmic test, each weighted arithmetic coefficient equals its normalized
vertical L-series term integral. Positive indices follow from the proved
Mellin inversion; the index-zero contribution vanishes. The normalization
is 1/(2*pi). This evaluates each term of the arithmetic side. -/
theorem logarithmicTestWeight_coefficient_eq_term_integral (a : ℕ → ℂ) (ha : a 0 = 0) (g : ℝ → ℂ)
    (he : ∀ u : ℝ, g (-u) = g u) (hc : HasCompactSupport g) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (σ : ℝ)
    (n : ℕ) :
    a n * logarithmicTestWeight g n =
      (1 / (2 * Real.pi) : ℝ) •
        (∫ T : ℝ, mellinLSeriesTerm a (mellin (logarithmicTestWeight g)) σ n T) := by
  by_cases hn : n = 0
  · subst n
    simp only [ha, zero_mul, mellinLSeriesTerm, LSeries.term_zero, MeasureTheory.integral_zero,
      smul_zero]
  · have hi :
      (∫ T : ℝ, mellinLSeriesTerm a (mellin (logarithmicTestWeight g)) σ n T) =
        a n *
          (∫ T : ℝ,
            (n : ℂ) ^ (-((σ : ℂ) + T * Complex.I)) *
              mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      exact
        MeasureTheory.ae_of_all _ fun T ↦ by
          rw [mellinLSeriesTerm, LSeries.term_def₀ ha]
          ring
    rw [hi, ←
      mellinInv_mellin_logarithmicTestWeight g he hc hg σ
        (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)),
      mellinInv]
    simp only [smul_eq_mul, Complex.real_smul, Complex.ofReal_natCast]
    ring

/-- For a coefficient sequence vanishing at zero, absolute L-series convergence
on a vertical line and an even smooth compact logarithmic test give the
arithmetic weighted sum as the normalized integral of the L-series times
the test's Mellin transform. Apply termwise inversion and the proved integral
exchange. No independent Mellin inversion or integral-interchange premise
is required. This supplies the arithmetic evaluation in the explicit formula. -/
theorem logarithmicTestWeight_tsum_eq_integral_LSeries (a : ℕ → ℂ) (ha : a 0 = 0) (g : ℝ → ℂ)
    (he : ∀ u : ℝ, g (-u) = g u) (hc : HasCompactSupport g) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (σ : ℝ)
    (hs : LSeriesSummable a (σ : ℂ)) :
    (∑' n : ℕ, a n * logarithmicTestWeight g n) =
      (1 / (2 * Real.pi) : ℝ) •
        (∫ T : ℝ,
          LSeries a ((σ : ℂ) + T * Complex.I) *
            mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) := by
  rw [tsum_congr (logarithmicTestWeight_coefficient_eq_term_integral a ha g he hc hg σ),
    tsum_const_smul'']
  rw [integral_LSeries_mellin_eq_tsum a _ σ hs
      (verticalIntegrable_mellin_logarithmicTestWeight g he hc hg σ)]

/-- An absolutely convergent L-series multiplied by a vertically integrable
weight is integrable on that line. Summable integrated term norms give
integrability of the pointwise series, whose sum is the L-series product.
This justifies whole-line arithmetic integrals independently of their evaluation. -/
theorem integrable_LSeries_mellin (a : ℕ → ℂ) (W : ℂ → ℂ) (σ : ℝ) (hs : LSeriesSummable a (σ : ℂ))
    (hw : Complex.VerticalIntegrable W σ) :
    MeasureTheory.Integrable
      (fun T : ℝ ↦ LSeries a ((σ : ℂ) + T * Complex.I) * W ((σ : ℂ) + T * Complex.I)) := by
  apply
    (PseudoPrime.Analysis.integrable_tsum_of_summable_integral_norm (mellinLSeriesTerm a W σ)
        (integrable_mellinLSeriesTerm a W σ hw)
        (summable_integral_norm_mellinLSeriesTerm a W σ hs)).congr
  exact MeasureTheory.ae_of_all _ fun T ↦ by simp only [mellinLSeriesTerm, tsum_mul_right, LSeries]

/-- For coefficients vanishing at zero with absolutely convergent L-series,
the arithmetic values against an even smooth compact logarithmic test form
a summable family. Summability of the term integrals and termwise Mellin
inversion establish this directly. This supplies the convergence needed
when combining the original and dual arithmetic sums. -/
theorem summable_logarithmicTestWeight_coefficients (a : ℕ → ℂ) (ha : a 0 = 0) (g : ℝ → ℂ)
    (he : ∀ u : ℝ, g (-u) = g u) (hc : HasCompactSupport g) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (σ : ℝ)
    (hs : LSeriesSummable a (σ : ℂ)) : Summable (fun n : ℕ ↦ a n * logarithmicTestWeight g n) := by
  have hh :=
    (MeasureTheory.hasSum_integral_of_summable_integral_norm
        (integrable_mellinLSeriesTerm a _ σ
          (verticalIntegrable_mellin_logarithmicTestWeight g he hc hg σ))
        (summable_integral_norm_mellinLSeriesTerm a _ σ hs)).summable
  exact
    (hh.const_smul (1 / (2 * Real.pi) : ℝ)).congr
      (fun n ↦ (logarithmicTestWeight_coefficient_eq_term_integral a ha g he hc hg σ n).symm)

/-- If an ordinary logarithmic derivative equals the negative coefficient
L-series on an absolutely convergent vertical line, an even smooth compact
logarithmic test gives its arithmetic sum as the negative normalized
logarithmic-derivative integral. Apply the proved L-series evaluation and
retain the minus sign. The input series identity must still be derived
from Euler-product data; this theorem does not assume an explicit formula. -/
theorem logarithmicTestWeight_tsum_eq_neg_logDeriv_integral (L : ℂ → ℂ) (a : ℕ → ℂ) (ha : a 0 = 0)
    (g : ℝ → ℂ) (he : ∀ u : ℝ, g (-u) = g u) (hc : HasCompactSupport g)
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (σ : ℝ) (hs : LSeriesSummable a (σ : ℂ))
    (hlog : ∀ T : ℝ, logDeriv L ((σ : ℂ) + T * Complex.I) = -LSeries a ((σ : ℂ) + T * Complex.I)) :
    (∑' n : ℕ, a n * logarithmicTestWeight g n) =
      -(1 / (2 * Real.pi) : ℝ) •
        (∫ T : ℝ,
          logDeriv L ((σ : ℂ) + T * Complex.I) *
            mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) := by
  have hi :
    (∫ T : ℝ,
        logDeriv L ((σ : ℂ) + T * Complex.I) *
          mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) =
      -(∫ T : ℝ,
          LSeries a ((σ : ℂ) + T * Complex.I) *
            mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) := by
    simp only [hlog, neg_mul, MeasureTheory.integral_neg]
  rw [hi, neg_smul, smul_neg, neg_neg]
  exact logarithmicTestWeight_tsum_eq_integral_LSeries a ha g he hc hg σ hs

end PseudoPrime.AnalyticNumberTheory.General

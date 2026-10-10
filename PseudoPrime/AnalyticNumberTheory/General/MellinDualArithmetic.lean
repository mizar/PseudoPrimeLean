/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.MellinLSeriesIntegration
public import PseudoPrime.NumberTheory.LSeriesConjugation

/-!
# Arithmetic sums for a test function and dual coefficients

Mellin inversion expresses the sum of original and conjugate coefficients
through two right-line integrals. The dual integral retains the reflected height.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- For an even smooth compactly supported test function and an absolutely
convergent coefficient series with zero constant term, the paired arithmetic
sum equals the two Mellin integrals for the original and dual series.
Conjugation gives convergence of the dual series, and termwise inversion
evaluates both sums. This is the arithmetic pair in the explicit formula. -/
theorem logarithmicTestWeight_paired_tsum_eq_integral_LSeries (a : ℕ → ℂ) (ha : a 0 = 0) (g : ℝ → ℂ)
    (he : ∀ u : ℝ, g (-u) = g u) (hc : HasCompactSupport g) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (σ : ℝ)
    (hs : LSeriesSummable a (σ : ℂ)) :
    (∑' n : ℕ, (a n + star (a n)) * logarithmicTestWeight g n) =
      (1 / (2 * Real.pi) : ℝ) •
        ((∫ T : ℝ,
            LSeries a ((σ : ℂ) + T * Complex.I) *
              mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) +
          (∫ T : ℝ,
            star (LSeries a ((σ : ℂ) + (-T) * Complex.I)) *
              mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I))) := by
  have hsa : LSeriesSummable (fun n ↦ star (a n)) (σ : ℂ) := by
    apply PseudoPrime.NumberTheory.lSeriesSummable_star
    simpa only [Complex.star_def, Complex.conj_ofReal] using hs
  have ha0 : (fun n ↦ star (a n)) 0 = 0 := by
    dsimp only
    rw [ha, star_zero]
  have haS := summable_logarithmicTestWeight_coefficients a ha g he hc hg σ hs
  have hbS := summable_logarithmicTestWeight_coefficients _ ha0 g he hc hg σ hsa
  have hi :
    (∫ T : ℝ,
        LSeries (fun n ↦ star (a n)) ((σ : ℂ) + T * Complex.I) *
          mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) =
      (∫ T : ℝ,
        star (LSeries a ((σ : ℂ) + (-T) * Complex.I)) *
          mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) := by
    apply MeasureTheory.integral_congr_ae
    exact
      MeasureTheory.ae_of_all _ fun T ↦ by
        dsimp only
        rw [PseudoPrime.NumberTheory.lSeries_star]
        have hp : star ((σ : ℂ) + T * Complex.I) = (σ : ℂ) + (-T) * Complex.I := by
          simp only [Complex.star_def, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
          ring
        rw [hp]
  rw [tsum_congr (fun n ↦ add_mul (a n) (star (a n)) (logarithmicTestWeight g n)), haS.tsum_add hbS,
    logarithmicTestWeight_tsum_eq_integral_LSeries a ha g he hc hg σ hs,
    logarithmicTestWeight_tsum_eq_integral_LSeries _ ha0 g he hc hg σ hsa, hi, smul_add]

/-- A negative L-series identity for the ordinary logarithmic derivative on an
absolutely convergent line evaluates the paired arithmetic sum as the negative
normalized sum of original and reflected conjugate logarithmic-derivative integrals.
Apply the paired Mellin evaluation and preserve both minus signs. The Euler-product
derivation of the input logarithmic-derivative identity remains a separate step. -/
theorem logarithmicTestWeight_paired_tsum_eq_neg_logDeriv_integrals (L : ℂ → ℂ) (a : ℕ → ℂ)
    (ha : a 0 = 0) (g : ℝ → ℂ) (he : ∀ u : ℝ, g (-u) = g u) (hc : HasCompactSupport g)
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (σ : ℝ) (hs : LSeriesSummable a (σ : ℂ))
    (hlog : ∀ T : ℝ, logDeriv L ((σ : ℂ) + T * Complex.I) = -LSeries a ((σ : ℂ) + T * Complex.I)) :
    (∑' n : ℕ, (a n + star (a n)) * logarithmicTestWeight g n) =
      -(1 / (2 * Real.pi) : ℝ) •
        ((∫ T : ℝ,
            logDeriv L ((σ : ℂ) + T * Complex.I) *
              mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) +
          (∫ T : ℝ,
            star (logDeriv L ((σ : ℂ) + (-T) * Complex.I)) *
              mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I))) := by
  have hi :
    (∫ T : ℝ,
        logDeriv L ((σ : ℂ) + T * Complex.I) *
          mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) =
      -(∫ T : ℝ,
          LSeries a ((σ : ℂ) + T * Complex.I) *
            mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) := by
    simp only [hlog, neg_mul, MeasureTheory.integral_neg]
  have hj :
    (∫ T : ℝ,
        star (logDeriv L ((σ : ℂ) + (-T) * Complex.I)) *
          mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) =
      -(∫ T : ℝ,
          star (LSeries a ((σ : ℂ) + (-T) * Complex.I)) *
            mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) := by
    have hh :
      ∀ T : ℝ,
        logDeriv L ((σ : ℂ) + -(T * Complex.I)) = -LSeries a ((σ : ℂ) + -(T * Complex.I)) := by
      intro T
      simpa only [Complex.ofReal_neg, neg_mul] using hlog (-T)
    simp only [hh, star_neg, neg_mul, MeasureTheory.integral_neg]
  rw [hi, hj, ← neg_add, neg_smul, smul_neg, neg_neg]
  exact logarithmicTestWeight_paired_tsum_eq_integral_LSeries a ha g he hc hg σ hs

/-- Absolute convergence of the original coefficient series also makes its
paired logarithmic-test values summable. Conjugation supplies the dual
convergence, and adding the two summable families proves the claim.
This allows removal of the zero index in the explicit formula. -/
theorem summable_logarithmicTestWeight_paired_coefficients (a : ℕ → ℂ) (ha : a 0 = 0) (g : ℝ → ℂ)
    (he : ∀ u : ℝ, g (-u) = g u) (hc : HasCompactSupport g) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (σ : ℝ)
    (hs : LSeriesSummable a (σ : ℂ)) :
    Summable (fun n : ℕ ↦ (a n + star (a n)) * logarithmicTestWeight g n) := by
  have hb : LSeriesSummable (fun n ↦ star (a n)) (σ : ℂ) := by
    apply PseudoPrime.NumberTheory.lSeriesSummable_star
    simpa only [Complex.star_def, Complex.conj_ofReal] using hs
  have hb0 : (fun n ↦ star (a n)) 0 = 0 := by
    dsimp only
    rw [ha, star_zero]
  exact
    ((summable_logarithmicTestWeight_coefficients a ha g he hc hg σ hs).add
          (summable_logarithmicTestWeight_coefficients _ hb0 g he hc hg σ hb)).congr
      (fun n ↦ (add_mul _ _ _).symm)

/-- A summable paired logarithmic-test series with zero constant coefficient
equals the positive-index arithmetic sum weighted by g(log n)/sqrt n.
Remove index zero, then evaluate the logarithmic test at each positive integer.
This matches the arithmetic expression in the Fourier explicit formula. -/
theorem logarithmicTestWeight_paired_tsum_eq_sqrt_sum (a : ℕ → ℂ) (ha : a 0 = 0) (g : ℝ → ℂ)
    (hs : Summable (fun n : ℕ ↦ (a n + star (a n)) * logarithmicTestWeight g n)) :
    (∑' n : ℕ, (a n + star (a n)) * logarithmicTestWeight g n) =
      ∑' n : ℕ,
        (a (n + 1) + star (a (n + 1))) * g (Real.log (n + 1)) / (Real.sqrt (n + 1) : ℂ) := by
  rw [hs.tsum_eq_zero_add]
  simp only [ha, star_zero, zero_add, zero_mul]
  apply tsum_congr
  intro n
  rw [logarithmicTestWeight_eq_div_sqrt g (Nat.cast_pos.mpr (Nat.succ_pos n))]
  simp only [mul_div_assoc, Nat.cast_succ]

/-- For an even smooth compact test, absolute coefficient convergence and a
negative L-series formula for the ordinary logarithmic derivative give the
positive-index arithmetic sum as two normalized right-line integrals.
The dual integral uses the conjugate value at reflected height. Combine the
proved paired integral evaluation with the square-root form of the test.
The coefficient-series identity remains an explicit input, to be derived
from the Euler product for the target L-function. -/
theorem paired_sqrt_sum_eq_neg_logDeriv_integrals (L : ℂ → ℂ) (a : ℕ → ℂ) (ha : a 0 = 0) (g : ℝ → ℂ)
    (he : ∀ u : ℝ, g (-u) = g u) (hc : HasCompactSupport g) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (σ : ℝ)
    (hs : LSeriesSummable a (σ : ℂ))
    (hlog : ∀ T : ℝ, logDeriv L ((σ : ℂ) + T * Complex.I) = -LSeries a ((σ : ℂ) + T * Complex.I)) :
    (∑' n : ℕ, (a (n + 1) + star (a (n + 1))) * g (Real.log (n + 1)) / (Real.sqrt (n + 1) : ℂ)) =
      -(1 / (2 * Real.pi) : ℝ) •
        ((∫ T : ℝ,
            logDeriv L ((σ : ℂ) + T * Complex.I) *
              mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) +
          (∫ T : ℝ,
            star (logDeriv L ((σ : ℂ) + (-T) * Complex.I)) *
              mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I))) := by
  rw [←
    logarithmicTestWeight_paired_tsum_eq_sqrt_sum a ha g
      (summable_logarithmicTestWeight_paired_coefficients a ha g he hc hg σ hs)]
  exact logarithmicTestWeight_paired_tsum_eq_neg_logDeriv_integrals L a ha g he hc hg σ hs hlog

end PseudoPrime.AnalyticNumberTheory.General

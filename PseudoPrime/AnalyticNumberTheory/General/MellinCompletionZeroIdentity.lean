/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.MellinZeroIntegral
public import PseudoPrime.AnalyticNumberTheory.General.MellinCompletionIntegrals

/-!
# Completion-zero and arithmetic Mellin identities

Combine the actual completion-zero formula with the evaluated arithmetic pair.
Functional reflection and coefficient convergence also supply integrability
of both ordinary and dual terms, allowing the difference inside the integrals.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- For an entire function with a nonzero conjugate functional-equation factor,
and an even test, integrability of the left completed logarithmic integral
implies integrability of its reflected conjugate right integral. Change height
to its negative and apply functional reflection and Mellin symmetry.
This discharges dual convergence in the completed zero formula. -/
theorem integrable_reflected_logDeriv_mellin_of_left {F : ℂ → ℂ} {ε : ℂ} (hε : ε ≠ 0)
    (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hF : Differentiable ℂ F) (g : ℝ → ℂ)
    (he : ∀ u : ℝ, g (-u) = g u)
    (hi :
      MeasureTheory.Integrable
        (fun T : ℝ ↦
          logDeriv F (((-1 : ℝ) : ℂ) + T * Complex.I) *
            mellin (logarithmicTestWeight g) (((-1 : ℝ) : ℂ) + T * Complex.I))) :
    MeasureTheory.Integrable
      (fun T : ℝ ↦
        star (logDeriv F (((2 : ℝ) : ℂ) + (-T) * Complex.I)) *
          mellin (logarithmicTestWeight g) (((2 : ℝ) : ℂ) + T * Complex.I)) := by
  apply hi.neg.comp_neg.congr
  exact
    MeasureTheory.ae_of_all _ fun T ↦ by
      dsimp only [Pi.neg_apply]
      have hr :
        1 - star (((-1 : ℝ) : ℂ) + (-T : ℝ) * Complex.I) = (((2 : ℝ) : ℂ) + (-T) * Complex.I) := by
        simp only [Complex.star_def, map_add, map_mul, map_neg, map_one, Complex.conj_ofReal,
          Complex.conj_I, Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_ofNat]
        ring
      have ht : (((-1 : ℝ) : ℂ) + (-T : ℝ) * Complex.I) = 1 - (((2 : ℝ) : ℂ) + T * Complex.I) := by
        simp only [Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_ofNat]
        ring
      rw [logDeriv_eq_neg_conjugateReflection hε hfe (hF _), hr, ht,
        mellin_logarithmicTestWeight_one_sub g he, neg_mul, neg_neg]

/-- Absolute coefficient convergence, a vertically integrable weight and the
negative L-series formula for the ordinary logarithmic derivative imply
integrability of both the original and reflected conjugate weighted derivatives.
Use termwise integral convergence for the original and conjugate coefficients.
This permits subtraction of arithmetic terms inside the completion integrals. -/
theorem integrable_paired_logDeriv_mellin_of_LSeries (L : ℂ → ℂ) (a : ℕ → ℂ) (σ : ℝ) (W : ℂ → ℂ)
    (hs : LSeriesSummable a (σ : ℂ)) (hw : Complex.VerticalIntegrable W σ)
    (hlog : ∀ T : ℝ, logDeriv L ((σ : ℂ) + T * Complex.I) = -LSeries a ((σ : ℂ) + T * Complex.I)) :
    MeasureTheory.Integrable
        (fun T : ℝ ↦ logDeriv L ((σ : ℂ) + T * Complex.I) * W ((σ : ℂ) + T * Complex.I)) ∧
      MeasureTheory.Integrable
        (fun T : ℝ ↦
          star (logDeriv L ((σ : ℂ) + (-T) * Complex.I)) * W ((σ : ℂ) + T * Complex.I)) := by
  have hb : LSeriesSummable (fun n ↦ star (a n)) (σ : ℂ) := by
    apply PseudoPrime.NumberTheory.lSeriesSummable_star
    simpa only [Complex.star_def, Complex.conj_ofReal] using hs
  constructor
  · apply (integrable_LSeries_mellin a W σ hs hw).neg.congr
    exact
      MeasureTheory.ae_of_all _ fun T ↦ by
        dsimp only [Pi.neg_apply]
        rw [hlog, neg_mul]
  · apply (integrable_LSeries_mellin (fun n ↦ star (a n)) W σ hb hw).neg.congr
    exact
      MeasureTheory.ae_of_all _ fun T ↦ by
        dsimp only [Pi.neg_apply]
        rw [PseudoPrime.NumberTheory.lSeries_star]
        have hp : star ((σ : ℂ) + T * Complex.I) = (σ : ℂ) + (-T : ℝ) * Complex.I := by
          simp only [Complex.star_def, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I,
            Complex.ofReal_neg]
          ring
        have hh :
          logDeriv L ((σ : ℂ) + (-T) * Complex.I) = -LSeries a ((σ : ℂ) + (-T) * Complex.I) := by
          simpa only [Complex.ofReal_neg] using hlog (-T)
        rw [hp, Complex.ofReal_neg, hh, star_neg]
        simp only [neg_mul]

/-- For entire order-one regularized completion data with conjugate functional
equation and nonvanishing on the right, an even smooth compact test has its
weighted zero sum plus the positive-index arithmetic sum equal to the normalized
difference of the paired completed and ordinary logarithmic integrals.
Coefficient bounds and the reference-line identity establish the zero formula;
absolute convergence and the right-line coefficient identity evaluate arithmetic.
This retains the completion factors for their separate evaluation. -/
theorem mellin_zero_sum_add_arithmetic_eq_integral_difference {F L : ℂ → ℂ} {ε : ℂ} {q d : ℕ}
    (hq : 1 ≤ q) (k : ℤ) (κ : Fin d → ℂ) (hκ : ∀ j, -1 < (κ j).re)
    (hreg :
      ∀ z,
        z ≠ 0 →
          z ≠ 1 → F z = (z * (1 - z)) ^ k * ((q : ℂ) ^ (z / 2) * archimedeanGammaFactor κ z * L z))
    (hε : ε ≠ 0) (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hright : ∀ s, 1 < s.re → F s ≠ 0)
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ (d : ℝ) * n * Real.log n)
    (hL : ∀ T : ℝ, L (((3 : ℝ) : ℂ) + T * Complex.I) ≠ 0)
    (hdL : ∀ T : ℝ, DifferentiableAt ℂ L (((3 : ℝ) : ℂ) + T * Complex.I))
    (hlog :
      ∀ T : ℝ,
        logDeriv L (((3 : ℝ) : ℂ) + T * Complex.I) = -LSeries a (((3 : ℝ) : ℂ) + T * Complex.I))
    (g : ℝ → ℂ) (he : ∀ u : ℝ, g (-u) = g u) (hc : HasCompactSupport g)
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (ha0 : a 0 = 0) (hs2 : LSeriesSummable a (2 : ℂ))
    (hlog2 :
      ∀ T : ℝ,
        logDeriv L (((2 : ℝ) : ℂ) + T * Complex.I) = -LSeries a (((2 : ℝ) : ℂ) + T * Complex.I)) :
    (∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℂ) * mellin (logarithmicTestWeight g) ρ) +
        (∑' n : ℕ,
          (a (n + 1) + star (a (n + 1))) * g (Real.log (n + 1)) / (Real.sqrt (n + 1) : ℂ)) =
      (1 / (2 * Real.pi) : ℝ) •
        (((∫ T : ℝ,
              logDeriv F (((2 : ℝ) : ℂ) + T * Complex.I) *
                mellin (logarithmicTestWeight g) (((2 : ℝ) : ℂ) + T * Complex.I)) +
            (∫ T : ℝ,
              star (logDeriv F (((2 : ℝ) : ℂ) + (-T) * Complex.I)) *
                mellin (logarithmicTestWeight g) (((2 : ℝ) : ℂ) + T * Complex.I))) -
          ((∫ T : ℝ,
              logDeriv L (((2 : ℝ) : ℂ) + T * Complex.I) *
                mellin (logarithmicTestWeight g) (((2 : ℝ) : ℂ) + T * Complex.I)) +
            (∫ T : ℝ,
              star (logDeriv L (((2 : ℝ) : ℂ) + (-T) * Complex.I)) *
                mellin (logarithmicTestWeight g) (((2 : ℝ) : ℂ) + T * Complex.I)))) := by
  rw [mellin_zero_sum_eq_reflected_right_integrals_of_completion hq k κ hκ hreg hε hfe hright hF h0
      horder ha hL hdL hlog g he hc hg,
    paired_sqrt_sum_eq_neg_logDeriv_integrals L a ha0 g he hc hg 2 hs2 hlog2]
  simp only [Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

/-- Under the same completion and coefficient hypotheses, the zero sum plus
arithmetic sum equals the paired integral of the difference between completed
and ordinary logarithmic derivatives. Derive convergence of the completed dual
term by functional reflection and of the ordinary dual term by conjugating
coefficients. The proved integrated identities and integral subtraction then
place both differences inside the integrals. The remaining integrands are the
endpoint, conductor and gamma contributions of the completion. -/
theorem mellin_zero_sum_add_arithmetic_eq_integrated_difference {F L : ℂ → ℂ} {ε : ℂ} {q d : ℕ}
    (hq : 1 ≤ q) (k : ℤ) (κ : Fin d → ℂ) (hκ : ∀ j, -1 < (κ j).re)
    (hreg :
      ∀ z,
        z ≠ 0 →
          z ≠ 1 → F z = (z * (1 - z)) ^ k * ((q : ℂ) ^ (z / 2) * archimedeanGammaFactor κ z * L z))
    (hε : ε ≠ 0) (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hright : ∀ s, 1 < s.re → F s ≠ 0)
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ (d : ℝ) * n * Real.log n)
    (hL : ∀ T : ℝ, L (((3 : ℝ) : ℂ) + T * Complex.I) ≠ 0)
    (hdL : ∀ T : ℝ, DifferentiableAt ℂ L (((3 : ℝ) : ℂ) + T * Complex.I))
    (hlog :
      ∀ T : ℝ,
        logDeriv L (((3 : ℝ) : ℂ) + T * Complex.I) = -LSeries a (((3 : ℝ) : ℂ) + T * Complex.I))
    (g : ℝ → ℂ) (he : ∀ u : ℝ, g (-u) = g u) (hc : HasCompactSupport g)
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (ha0 : a 0 = 0) (hs2 : LSeriesSummable a (2 : ℂ))
    (hlog2 :
      ∀ T : ℝ,
        logDeriv L (((2 : ℝ) : ℂ) + T * Complex.I) = -LSeries a (((2 : ℝ) : ℂ) + T * Complex.I)) :
    (∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℂ) * mellin (logarithmicTestWeight g) ρ) +
        (∑' n : ℕ,
          (a (n + 1) + star (a (n + 1))) * g (Real.log (n + 1)) / (Real.sqrt (n + 1) : ℂ)) =
      (1 / (2 * Real.pi) : ℝ) •
        ((∫ T : ℝ,
            (logDeriv F (((2 : ℝ) : ℂ) + T * Complex.I) -
                logDeriv L (((2 : ℝ) : ℂ) + T * Complex.I)) *
              mellin (logarithmicTestWeight g) (((2 : ℝ) : ℂ) + T * Complex.I)) +
          (∫ T : ℝ,
            (star (logDeriv F (((2 : ℝ) : ℂ) + (-T) * Complex.I)) -
                star (logDeriv L (((2 : ℝ) : ℂ) + (-T) * Complex.I))) *
              mellin (logarithmicTestWeight g) (((2 : ℝ) : ℂ) + T * Complex.I))) := by
  obtain ⟨hFr, hFl⟩ :=
    integrable_outer_logDeriv_mellin_of_completion hq k κ hκ hreg hε hfe hright hF h0 horder ha hL
      hdL hlog g he hc hg
  have hFd := integrable_reflected_logDeriv_mellin_of_left hε hfe hF g he hFl
  obtain ⟨hLr, hLd⟩ :=
    integrable_paired_logDeriv_mellin_of_LSeries L a 2 (mellin (logarithmicTestWeight g)) hs2
      (verticalIntegrable_mellin_logarithmicTestWeight g he hc hg 2) hlog2
  simp only [sub_mul, MeasureTheory.integral_sub hFr hLr, MeasureTheory.integral_sub hFd hLd]
  rw [mellin_zero_sum_add_arithmetic_eq_integral_difference hq k κ hκ hreg hε hfe hright hF h0
      horder ha hL hdL hlog g he hc hg ha0 hs2 hlog2]
  congr 1
  abel

/-- For an entire regularized completion nonzero in the right half-plane,
positive natural conductor and admissible gamma shifts, the difference
between completed and ordinary logarithmic derivatives is exactly the
endpoint, conductor and gamma contribution. Recover ordinary differentiability
and nonvanishing from the completion product, then apply its logarithmic rule.
This identifies the remaining integrands without extra ordinary-factor premises. -/
theorem logDeriv_sub_eq_completionNonArithmetic_of_right {F L : ℂ → ℂ} {q d : ℕ} (hq : 1 ≤ q)
    (k : ℤ) (κ : Fin d → ℂ) (hκ : ∀ j, -1 < (κ j).re)
    (hreg :
      ∀ z,
        z ≠ 0 →
          z ≠ 1 → F z = (z * (1 - z)) ^ k * ((q : ℂ) ^ (z / 2) * archimedeanGammaFactor κ z * L z))
    (hF : Differentiable ℂ F) (hright : ∀ s, 1 < s.re → F s ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    logDeriv F s - logDeriv L s =
      completionNonArithmeticLogDerivative q k (archimedeanGammaFactor κ) s := by
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hq)
  have hs0 : s ≠ 0 := ne_of_apply_ne Complex.re (ne_of_gt (zero_lt_one.trans hs))
  have hs1 : s ≠ 1 := ne_of_apply_ne Complex.re (ne_of_gt hs)
  have hG := archimedeanGammaFactor_ne_zero hs hκ
  have hdG := differentiableAt_archimedeanGammaFactor hs hκ
  have hL := ne_zero_of_regularizedCompletion k hreg hs0 hs1 (hright s hs)
  have hdL := differentiableAt_of_regularizedCompletion hqC k hreg hs0 hs1 hG (hF s) hdG
  rw [logDeriv_regularizedCompletion hqC k hreg hs0 hs1 hG hL hdG hdL]
  dsimp only [completionNonArithmeticLogDerivative]
  ring

/-- For the proved order-one completion and convergent coefficient data, an even
smooth compact test has zero sum plus arithmetic sum equal to the paired
non-arithmetic completion integrals. Substitute the right-half-plane
completion decomposition into the proved integrated difference, retaining
the reflected conjugate dual term. This isolates endpoint, conductor and
gamma terms for evaluating the general explicit formula. -/
theorem mellin_zero_sum_add_arithmetic_eq_nonArithmetic_integrals {F L : ℂ → ℂ} {ε : ℂ} {q d : ℕ}
    (hq : 1 ≤ q) (k : ℤ) (κ : Fin d → ℂ) (hκ : ∀ j, -1 < (κ j).re)
    (hreg :
      ∀ z,
        z ≠ 0 →
          z ≠ 1 → F z = (z * (1 - z)) ^ k * ((q : ℂ) ^ (z / 2) * archimedeanGammaFactor κ z * L z))
    (hε : ε ≠ 0) (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hright : ∀ s, 1 < s.re → F s ≠ 0)
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ (d : ℝ) * n * Real.log n)
    (hL : ∀ T : ℝ, L (((3 : ℝ) : ℂ) + T * Complex.I) ≠ 0)
    (hdL : ∀ T : ℝ, DifferentiableAt ℂ L (((3 : ℝ) : ℂ) + T * Complex.I))
    (hlog :
      ∀ T : ℝ,
        logDeriv L (((3 : ℝ) : ℂ) + T * Complex.I) = -LSeries a (((3 : ℝ) : ℂ) + T * Complex.I))
    (g : ℝ → ℂ) (he : ∀ u : ℝ, g (-u) = g u) (hc : HasCompactSupport g)
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (ha0 : a 0 = 0) (hs2 : LSeriesSummable a (2 : ℂ))
    (hlog2 :
      ∀ T : ℝ,
        logDeriv L (((2 : ℝ) : ℂ) + T * Complex.I) = -LSeries a (((2 : ℝ) : ℂ) + T * Complex.I)) :
    (∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℂ) * mellin (logarithmicTestWeight g) ρ) +
        (∑' n : ℕ,
          (a (n + 1) + star (a (n + 1))) * g (Real.log (n + 1)) / (Real.sqrt (n + 1) : ℂ)) =
      (1 / (2 * Real.pi) : ℝ) •
        ((∫ T : ℝ,
            completionNonArithmeticLogDerivative q k (archimedeanGammaFactor κ)
                (((2 : ℝ) : ℂ) + T * Complex.I) *
              mellin (logarithmicTestWeight g) (((2 : ℝ) : ℂ) + T * Complex.I)) +
          (∫ T : ℝ,
            star
                (completionNonArithmeticLogDerivative q k (archimedeanGammaFactor κ)
                  (((2 : ℝ) : ℂ) + (-T) * Complex.I)) *
              mellin (logarithmicTestWeight g) (((2 : ℝ) : ℂ) + T * Complex.I))) := by
  rw [mellin_zero_sum_add_arithmetic_eq_integrated_difference hq k κ hκ hreg hε hfe hright hF h0
      horder ha hL hdL hlog g he hc hg ha0 hs2 hlog2]
  have hre : ∀ T : ℝ, 1 < ((((2 : ℝ) : ℂ) + T * Complex.I)).re := by
    intro T
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    norm_num only
  congr 1
  apply congrArg₂ (fun x y : ℂ ↦ x + y)
  · apply MeasureTheory.integral_congr_ae
    exact
      MeasureTheory.ae_of_all _ fun T ↦ by
        dsimp only
        rw [logDeriv_sub_eq_completionNonArithmetic_of_right hq k κ hκ hreg hF hright (hre T)]
  · apply MeasureTheory.integral_congr_ae
    exact
      MeasureTheory.ae_of_all _ fun T ↦ by
        dsimp only
        have hs : 1 < ((((2 : ℝ) : ℂ) + (-T) * Complex.I)).re := by
          simpa only [Complex.ofReal_neg] using hre (-T)
        rw [← star_sub,
          logDeriv_sub_eq_completionNonArithmetic_of_right hq k κ hκ hreg hF hright hs]

/-- For the entire order-one completion and convergent coefficient data,
both the original and reflected dual non-arithmetic Mellin integrands are
integrable. Subtract ordinary from completed logarithmic integrands and
identify the result by the completion product. Functional reflection and
conjugate coefficient convergence supply dual integrability.
This permits removing conductor terms from the completed explicit identity. -/
theorem integrable_paired_nonArithmetic_of_completion {F L : ℂ → ℂ} {ε : ℂ} {q d : ℕ} (hq : 1 ≤ q)
    (k : ℤ) (κ : Fin d → ℂ) (hκ : ∀ j, -1 < (κ j).re)
    (hreg :
      ∀ z,
        z ≠ 0 →
          z ≠ 1 → F z = (z * (1 - z)) ^ k * ((q : ℂ) ^ (z / 2) * archimedeanGammaFactor κ z * L z))
    (hε : ε ≠ 0) (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hright : ∀ s, 1 < s.re → F s ≠ 0)
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ (d : ℝ) * n * Real.log n)
    (hL : ∀ T : ℝ, L (((3 : ℝ) : ℂ) + T * Complex.I) ≠ 0)
    (hdL : ∀ T : ℝ, DifferentiableAt ℂ L (((3 : ℝ) : ℂ) + T * Complex.I))
    (hlog :
      ∀ T : ℝ,
        logDeriv L (((3 : ℝ) : ℂ) + T * Complex.I) = -LSeries a (((3 : ℝ) : ℂ) + T * Complex.I))
    (g : ℝ → ℂ) (he : ∀ u : ℝ, g (-u) = g u) (hc : HasCompactSupport g)
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (hs2 : LSeriesSummable a (2 : ℂ))
    (hlog2 :
      ∀ T : ℝ,
        logDeriv L (((2 : ℝ) : ℂ) + T * Complex.I) = -LSeries a (((2 : ℝ) : ℂ) + T * Complex.I)) :
    MeasureTheory.Integrable
        (fun T : ℝ ↦
          completionNonArithmeticLogDerivative q k (archimedeanGammaFactor κ)
              (((2 : ℝ) : ℂ) + T * Complex.I) *
            mellin (logarithmicTestWeight g) (((2 : ℝ) : ℂ) + T * Complex.I)) ∧
      MeasureTheory.Integrable
        (fun T : ℝ ↦
          star
              (completionNonArithmeticLogDerivative q k (archimedeanGammaFactor κ)
                (((2 : ℝ) : ℂ) + (-T) * Complex.I)) *
            mellin (logarithmicTestWeight g) (((2 : ℝ) : ℂ) + T * Complex.I)) := by
  obtain ⟨hFr, hFl⟩ :=
    integrable_outer_logDeriv_mellin_of_completion hq k κ hκ hreg hε hfe hright hF h0 horder ha hL
      hdL hlog g he hc hg
  have hFd := integrable_reflected_logDeriv_mellin_of_left hε hfe hF g he hFl
  obtain ⟨hLr, hLd⟩ :=
    integrable_paired_logDeriv_mellin_of_LSeries L a 2 (mellin (logarithmicTestWeight g)) hs2
      (verticalIntegrable_mellin_logarithmicTestWeight g he hc hg 2) hlog2
  have hre : ∀ T : ℝ, 1 < ((((2 : ℝ) : ℂ) + T * Complex.I)).re := by
    intro T
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    norm_num only
  constructor
  · apply (hFr.sub hLr).congr
    exact
      MeasureTheory.ae_of_all _ fun T ↦ by
        dsimp only [Pi.sub_apply]
        rw [← sub_mul,
          logDeriv_sub_eq_completionNonArithmetic_of_right hq k κ hκ hreg hF hright (hre T)]
  · apply (hFd.sub hLd).congr
    exact
      MeasureTheory.ae_of_all _ fun T ↦ by
        dsimp only [Pi.sub_apply]
        have hs : 1 < ((((2 : ℝ) : ℂ) + (-T) * Complex.I)).re := by
          simpa only [Complex.ofReal_neg] using hre (-T)
        rw [← sub_mul, ← star_sub,
          logDeriv_sub_eq_completionNonArithmetic_of_right hq k κ hκ hreg hF hright hs]

/-- For the proved completion and coefficient hypotheses, the zero sum plus
the positive-index arithmetic sum equals log(q)*g(0) plus the paired completion
remainder integrals with log(q)/2 subtracted. Derive both non-arithmetic
integrability statements, subtract and evaluate their constants by Mellin
inversion, and use reality of the natural conductor logarithm.
The remainders contain only endpoint regularization and gamma terms,
which must still be evaluated to obtain the general explicit formula. -/
theorem mellin_zero_sum_add_arithmetic_eq_conductor_add_remainder {F L : ℂ → ℂ} {ε : ℂ} {q d : ℕ}
    (hq : 1 ≤ q) (k : ℤ) (κ : Fin d → ℂ) (hκ : ∀ j, -1 < (κ j).re)
    (hreg :
      ∀ z,
        z ≠ 0 →
          z ≠ 1 → F z = (z * (1 - z)) ^ k * ((q : ℂ) ^ (z / 2) * archimedeanGammaFactor κ z * L z))
    (hε : ε ≠ 0) (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hright : ∀ s, 1 < s.re → F s ≠ 0)
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ (d : ℝ) * n * Real.log n)
    (hL : ∀ T : ℝ, L (((3 : ℝ) : ℂ) + T * Complex.I) ≠ 0)
    (hdL : ∀ T : ℝ, DifferentiableAt ℂ L (((3 : ℝ) : ℂ) + T * Complex.I))
    (hlog :
      ∀ T : ℝ,
        logDeriv L (((3 : ℝ) : ℂ) + T * Complex.I) = -LSeries a (((3 : ℝ) : ℂ) + T * Complex.I))
    (g : ℝ → ℂ) (he : ∀ u : ℝ, g (-u) = g u) (hc : HasCompactSupport g)
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (ha0 : a 0 = 0) (hs2 : LSeriesSummable a (2 : ℂ))
    (hlog2 :
      ∀ T : ℝ,
        logDeriv L (((2 : ℝ) : ℂ) + T * Complex.I) = -LSeries a (((2 : ℝ) : ℂ) + T * Complex.I)) :
    (∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℂ) * mellin (logarithmicTestWeight g) ρ) +
        (∑' n : ℕ,
          (a (n + 1) + star (a (n + 1))) * g (Real.log (n + 1)) / (Real.sqrt (n + 1) : ℂ)) =
      ((Real.log q : ℝ) : ℂ) * g 0 +
        (1 / (2 * Real.pi) : ℝ) •
          ((∫ T : ℝ,
              (completionNonArithmeticLogDerivative q k (archimedeanGammaFactor κ)
                    (((2 : ℝ) : ℂ) + T * Complex.I) -
                  Complex.log (q : ℂ) / 2) *
                mellin (logarithmicTestWeight g) (((2 : ℝ) : ℂ) + T * Complex.I)) +
            (∫ T : ℝ,
              star
                  (completionNonArithmeticLogDerivative q k (archimedeanGammaFactor κ)
                      (((2 : ℝ) : ℂ) + (-T) * Complex.I) -
                    Complex.log (q : ℂ) / 2) *
                mellin (logarithmicTestWeight g) (((2 : ℝ) : ℂ) + T * Complex.I))) := by
  obtain ⟨hi, hd⟩ :=
    integrable_paired_nonArithmetic_of_completion hq k κ hκ hreg hε hfe hright hF h0 horder ha hL
      hdL hlog g he hc hg hs2 hlog2
  rw [mellin_zero_sum_add_arithmetic_eq_nonArithmetic_integrals hq k κ hκ hreg hε hfe hright hF h0
      horder ha hL hdL hlog g he hc hg ha0 hs2 hlog2,
    normalized_integral_paired_eq_const_add_remainder
      (completionNonArithmeticLogDerivative q k (archimedeanGammaFactor κ))
      (Complex.log (q : ℂ) / 2) g he hc hg 2 hi hd]
  have hqlog : Complex.log (q : ℂ) = ((Real.log q : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using (Complex.ofReal_log (Nat.cast_nonneg q)).symm
  rw [hqlog]
  simp only [Complex.star_def, map_div₀, Complex.conj_ofReal, map_ofNat]
  ring

end PseudoPrime.AnalyticNumberTheory.General

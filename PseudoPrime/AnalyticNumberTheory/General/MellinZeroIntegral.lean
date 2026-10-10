/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.MellinVerticalIntegrals
public import PseudoPrime.AnalyticNumberTheory.General.MellinContourZeroLimit
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Whole-line Mellin integrals for the weighted zero sum

The finite residue limit becomes a whole-line integral identity. Reflection
places both contributions on the right line; their arithmetic evaluation
and archimedean terms remain separate.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- For general completion data with an entire order-one regularization nonzero
at zero, admissible gamma shifts, conjugate functional equation and
right-half-plane nonvanishing, the compact-test multiplicity-weighted zero sum
equals the right-minus-left logarithmic Mellin integrals divided by 2*pi.
Coefficient bounds and the reference-line series supply all contour growth
estimates. The finite residue limit and the whole-line integral limit coincide
by uniqueness; no contour identity or convergence premise remains.
This is the zero-side identity before evaluating the ordinary L and gamma factors. -/
theorem mellin_zero_sum_eq_vertical_integral_difference_of_completion {F L : ℂ → ℂ} {ε : ℂ}
    {q d : ℕ} (hq : 1 ≤ q) (k : ℤ) (κ : Fin d → ℂ) (hκ : ∀ j, -1 < (κ j).re)
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
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) :
    (∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℂ) * mellin (logarithmicTestWeight g) ρ) =
      ((∫ T : ℝ,
            logDeriv F (((2 : ℝ) : ℂ) + T * Complex.I) *
              mellin (logarithmicTestWeight g) (((2 : ℝ) : ℂ) + T * Complex.I)) -
          (∫ T : ℝ,
            logDeriv F (((-1 : ℝ) : ℂ) + T * Complex.I) *
              mellin (logarithmicTestWeight g) (((-1 : ℝ) : ℂ) + T * Complex.I))) /
        (2 * Real.pi : ℂ) := by
  obtain ⟨hr, hl⟩ :=
    integrable_outer_logDeriv_mellin_of_completion hq k κ hκ hreg hε hfe hright hF h0 horder ha hL
      hdL hlog g he hc hg
  obtain ⟨U, B, hu, hb, ht⟩ :=
    exists_mellin_vertical_difference_of_completion hq k κ hκ hreg hε hfe hright hF h0 horder ha hL
      hdL hlog g he hc hg
  have hi :=
    (MeasureTheory.intervalIntegral_tendsto_integral hr hb hu).sub
      (MeasureTheory.intervalIntegral_tendsto_integral hl hb hu)
  have heq := tendsto_nhds_unique ht hi
  have hp : (2 * Real.pi : ℂ) ≠ 0 := by
    apply mul_ne_zero (by norm_num only)
    exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  apply (eq_div_iff hp).mpr
  exact (mul_comm _ _).trans heq

/-- For an even logarithmic test, its Mellin transform is invariant under
s mapping to 1-s. The corresponding complex Fourier frequencies are opposite,
and the Fourier-Laplace transform of an even function is even.
This identity reflects the Mellin weight when moving the left contour line. -/
theorem mellin_logarithmicTestWeight_one_sub (g : ℝ → ℂ) (he : ∀ u : ℝ, g (-u) = g u) (s : ℂ) :
    mellin (logarithmicTestWeight g) (1 - s) = mellin (logarithmicTestWeight g) s := by
  rw [mellin_logarithmicTestWeight_eq_fourierLaplace g he,
    mellin_logarithmicTestWeight_eq_fourierLaplace g he]
  have hf : mellinFourierFrequency (1 - s) = -mellinFourierFrequency s := by
    apply Complex.ext
    · simp only [mellinFourierFrequency_re, Complex.sub_im, Complex.one_im, zero_sub,
        Complex.neg_re, neg_div]
    · rw [mellinFourierFrequency_im, Complex.sub_re, Complex.one_re, Complex.neg_im,
        mellinFourierFrequency_im]
      ring
  rw [hf, fourierLaplace_neg g he]

/-- For an entire function with a nonzero conjugate functional equation constant,
the left logarithmic Mellin integral of an even test is minus the reflected
conjugate integral on real part two. Reflect the logarithmic derivative and
the Mellin weight, then change T to -T. The conjugate term retains the
negative height, as required for the dual completed function.
This moves the zero-side identity entirely to the right half-plane. -/
theorem left_vertical_integral_eq_neg_reflected {F : ℂ → ℂ} {ε : ℂ} (hε : ε ≠ 0)
    (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hF : Differentiable ℂ F) (g : ℝ → ℂ)
    (he : ∀ u : ℝ, g (-u) = g u) :
    (∫ T : ℝ,
        logDeriv F (((-1 : ℝ) : ℂ) + T * Complex.I) *
          mellin (logarithmicTestWeight g) (((-1 : ℝ) : ℂ) + T * Complex.I)) =
      -(∫ T : ℝ,
          star (logDeriv F (((2 : ℝ) : ℂ) + (-T) * Complex.I)) *
            mellin (logarithmicTestWeight g) (((2 : ℝ) : ℂ) + T * Complex.I)) := by
  rw [← MeasureTheory.integral_neg]
  rw [←
    MeasureTheory.integral_neg_eq_self
      (fun T : ℝ ↦
        -(star (logDeriv F (((2 : ℝ) : ℂ) + (-T) * Complex.I)) *
            mellin (logarithmicTestWeight g) (((2 : ℝ) : ℂ) + T * Complex.I)))
      MeasureTheory.volume]
  apply MeasureTheory.integral_congr_ae
  exact
    MeasureTheory.ae_of_all _ fun T ↦ by
      dsimp only
      simp only [Complex.ofReal_neg, Complex.ofReal_one, neg_neg]
      have hreflection :
        1 - star (((-1 : ℝ) : ℂ) + T * Complex.I) = (((2 : ℝ) : ℂ) + T * Complex.I) := by
        simp only [Complex.star_def, map_add, map_mul, map_neg, map_one, Complex.conj_ofReal,
          Complex.conj_I, Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_ofNat]
        ring
      have htest : (((-1 : ℝ) : ℂ) + T * Complex.I) = 1 - (((2 : ℝ) : ℂ) + (-T) * Complex.I) := by
        simp only [Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_ofNat]
        ring
      have hm :
        mellin (logarithmicTestWeight g) (((-1 : ℝ) : ℂ) + T * Complex.I) =
          mellin (logarithmicTestWeight g) (((2 : ℝ) : ℂ) + (-T) * Complex.I) := by
        rw [htest, mellin_logarithmicTestWeight_one_sub g he]
      simp only [Complex.ofReal_neg, Complex.ofReal_one] at hreflection hm
      rw [logDeriv_eq_neg_conjugateReflection hε hfe (hF _), hreflection, hm, neg_mul]

/-- For general completion data with entire order-one regularization nonzero
at zero, admissible gamma shifts, conjugate functional equation and
right-half-plane nonvanishing, an even smooth compact test has its
multiplicity-weighted zero sum equal to the sum of the original and reflected
conjugate right-line logarithmic Mellin integrals divided by 2*pi.
Arithmetic coefficient bounds and the reference-line series discharge growth
and convergence. Combine the actual residue-limit identity with reflection.
Both integrals are now in the right half-plane for subsequent arithmetic
and archimedean evaluation. -/
theorem mellin_zero_sum_eq_reflected_right_integrals_of_completion {F L : ℂ → ℂ} {ε : ℂ} {q d : ℕ}
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
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) :
    (∑' ρ : ℂ, (analyticOrderNatAt F ρ : ℂ) * mellin (logarithmicTestWeight g) ρ) =
      ((∫ T : ℝ,
            logDeriv F (((2 : ℝ) : ℂ) + T * Complex.I) *
              mellin (logarithmicTestWeight g) (((2 : ℝ) : ℂ) + T * Complex.I)) +
          (∫ T : ℝ,
            star (logDeriv F (((2 : ℝ) : ℂ) + (-T) * Complex.I)) *
              mellin (logarithmicTestWeight g) (((2 : ℝ) : ℂ) + T * Complex.I))) /
        (2 * Real.pi : ℂ) := by
  rw [mellin_zero_sum_eq_vertical_integral_difference_of_completion hq k κ hκ hreg hε hfe hright hF
      h0 horder ha hL hdL hlog g he hc hg,
    left_vertical_integral_eq_neg_reflected hε hfe hF g he, sub_neg_eq_add]

end PseudoPrime.AnalyticNumberTheory.General

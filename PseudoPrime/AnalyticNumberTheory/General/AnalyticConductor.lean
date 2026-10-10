/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.ArchimedeanGammaFactor

/-!
# Analytic conductor and local zero multiplicity

The reflected resolvent estimate gives a logarithmic conductor bound without
assuming a Riemann hypothesis. Endpoint orders are kept explicit.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- The analytic conductor is q times the product of norm(s+kappa_j)+3.
The positive shifts keep every archimedean factor nonzero. It measures the
height dependence of the local zero count for general complex parameters. -/
noncomputable def analyticConductor {d : ℕ} (q : ℕ) (κ : Fin d → ℂ) (s : ℂ) : ℝ :=
  (q : ℝ) * ∏ j : Fin d, (‖s + κ j‖ + 3)

/-- For a positive natural conductor, its logarithm splits into the conductor
logarithm and the finite sum of archimedean logarithms. Positivity justifies
the product logarithm; the identity is used in the local counting bound. -/
theorem log_analyticConductor {d : ℕ} (q : ℕ) (hq : 1 ≤ q) (κ : Fin d → ℂ) (s : ℂ) :
    Real.log (analyticConductor q κ s) = Real.log q + ∑ j : Fin d, Real.log (‖s + κ j‖ + 3) := by
  have hp : ∀ j : Fin d, 0 < ‖s + κ j‖ + 3 := fun j ↦ by linarith only [norm_nonneg (s + κ j)]
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hq))
  rw [analyticConductor, Real.log_mul hq0 (Finset.prod_pos (fun j _ ↦ hp j)).ne',
    Real.log_prod (fun j _ ↦ (hp j).ne')]

/-- An entire regularized completion of order at most one, with its functional
equation and no zeros to the right of the critical strip, has its multiplicity
in a height window bounded by the analytic conductor at real part three.
The coefficient bound and logarithmic derivative series identity control the
arithmetic term; the uniform digamma estimate controls the gamma term.
The endpoint correction remains explicit as 20 times the absolute order. -/
theorem localZeroCount_le_log_analyticConductor_at_three {F L : ℂ → ℂ} {ε : ℂ} {q d : ℕ}
    (hq : 1 ≤ q) (k : ℤ) (κ : Fin d → ℂ) (hκ : ∀ j, -1 < (κ j).re)
    (hreg :
      ∀ z,
        z ≠ 0 →
          z ≠ 1 → F z = (z * (1 - z)) ^ k * ((q : ℂ) ^ (z / 2) * archimedeanGammaFactor κ z * L z))
    (hε : ε ≠ 0) (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hright : ∀ s, 1 < s.re → F s ≠ 0)
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ (d : ℝ) * n * Real.log n) (T : ℝ)
    (hL : L (((3 : ℝ) : ℂ) + T * Complex.I) ≠ 0)
    (hdL : DifferentiableAt ℂ L (((3 : ℝ) : ℂ) + T * Complex.I))
    (hlog :
      logDeriv L (((3 : ℝ) : ℂ) + T * Complex.I) = -LSeries a (((3 : ℝ) : ℂ) + T * Complex.I)) :
    (∑' ρ : ℂ, localZeroMultiplicity F T ρ) ≤
      20 * |(k : ℝ)| + 5 * Real.log (analyticConductor q κ (((3 : ℝ) : ℂ) + T * Complex.I)) +
        (d : ℝ) *
          (5 * (‖Complex.log (Real.pi : ℂ)‖ + Real.pi + Gamma.digammaLogErrorBound) +
            10 * ∑' n : ℕ, Real.log n / (n : ℝ) ^ 2) := by
  have hs3 : ((((3 : ℝ) : ℂ) + T * Complex.I)).re = 3 := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero]
    norm_num only
  have hs : 1 < ((((3 : ℝ) : ℂ) + T * Complex.I)).re := by
    rw [hs3]; norm_num only
  have hc :=
    localZeroCount_le_completedProductBound hq k hreg hε hfe hright hF h0 horder ha T
      (archimedeanGammaFactor_ne_zero hs hκ) hL (differentiableAt_archimedeanGammaFactor hs hκ) hdL
      hlog
  have hg := norm_logDeriv_archimedeanGammaFactor_at_three_le hs3 hκ
  have hb :=
    hc.trans
      (mul_le_mul_of_nonneg_left (add_le_add (add_le_add le_rfl hg) le_rfl)
        (by norm_num only : (0 : ℝ) ≤ 10))
  convert hb using 1
  rw [log_analyticConductor q hq κ]
  ring

/-- Moving the argument three units right increases the logarithmic analytic
conductor by at most degree times log two. The triangle inequality bounds
each positive factor by twice its original value. This transfers the local
zero count from real part three to the imaginary axis. -/
theorem log_analyticConductor_add_three_le {d : ℕ} (q : ℕ) (hq : 1 ≤ q) (κ : Fin d → ℂ) (s : ℂ) :
    Real.log (analyticConductor q κ (s + 3)) ≤
      Real.log (analyticConductor q κ s) + (d : ℝ) * Real.log 2 := by
  have hb : ∀ j : Fin d, Real.log (‖s + 3 + κ j‖ + 3) ≤ Real.log 2 + Real.log (‖s + κ j‖ + 3) := by
    intro j
    have hp : 0 < ‖s + κ j‖ + 3 := by linarith only [norm_nonneg (s + κ j)]
    have hp' : 0 < ‖s + 3 + κ j‖ + 3 := by linarith only [norm_nonneg (s + 3 + κ j)]
    have hn : ‖s + 3 + κ j‖ ≤ ‖s + κ j‖ + 3 := by
      rw [show s + 3 + κ j = (s + κ j) + 3 from by ring]
      simpa only [Complex.norm_ofNat] using norm_add_le (s + κ j) (3 : ℂ)
    have hh : ‖s + 3 + κ j‖ + 3 ≤ 2 * (‖s + κ j‖ + 3) := by
      linarith only [hn, norm_nonneg (s + κ j)]
    have hl := Real.log_le_log hp' hh
    rw [Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) hp.ne'] at hl
    exact hl
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hb j)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hs
  rw [log_analyticConductor q hq κ, log_analyticConductor q hq κ]
  linarith only [hs]

/-- Under the analytic completion and arithmetic series hypotheses, the sum
of zero multiplicities in a height window is bounded by five times the
logarithmic analytic conductor on the imaginary axis, an explicit endpoint
correction, and a constant times the degree. The proof shifts the conductor
bound at real part three. The endpoint term is retained, so this is a bound
for fixed completion data rather than an assertion of an absolute constant
independent of the endpoint order. -/
theorem localZeroCount_le_log_analyticConductor {F L : ℂ → ℂ} {ε : ℂ} {q d : ℕ} (hq : 1 ≤ q) (k : ℤ)
    (κ : Fin d → ℂ) (hκ : ∀ j, -1 < (κ j).re)
    (hreg :
      ∀ z,
        z ≠ 0 →
          z ≠ 1 → F z = (z * (1 - z)) ^ k * ((q : ℂ) ^ (z / 2) * archimedeanGammaFactor κ z * L z))
    (hε : ε ≠ 0) (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hright : ∀ s, 1 < s.re → F s ≠ 0)
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ (d : ℝ) * n * Real.log n) (T : ℝ)
    (hL : L (((3 : ℝ) : ℂ) + T * Complex.I) ≠ 0)
    (hdL : DifferentiableAt ℂ L (((3 : ℝ) : ℂ) + T * Complex.I))
    (hlog :
      logDeriv L (((3 : ℝ) : ℂ) + T * Complex.I) = -LSeries a (((3 : ℝ) : ℂ) + T * Complex.I)) :
    (∑' ρ : ℂ, localZeroMultiplicity F T ρ) ≤
      20 * |(k : ℝ)| + 5 * Real.log (analyticConductor q κ ((T : ℂ) * Complex.I)) +
        (d : ℝ) *
          (5 * Real.log 2 +
            5 * (‖Complex.log (Real.pi : ℂ)‖ + Real.pi + Gamma.digammaLogErrorBound) +
            10 * ∑' n : ℕ, Real.log n / (n : ℝ) ^ 2) := by
  have hb :=
    localZeroCount_le_log_analyticConductor_at_three hq k κ hκ hreg hε hfe hright hF h0 horder ha T
      hL hdL hlog
  have ht := log_analyticConductor_add_three_le q hq κ ((T : ℂ) * Complex.I)
  rw [show ((T : ℂ) * Complex.I + 3) = (((3 : ℝ) : ℂ) + T * Complex.I) from by
      change (T : ℂ) * Complex.I + (3 : ℂ) = (3 : ℂ) + (T : ℂ) * Complex.I
      exact add_comm _ _] at ht
  nlinarith only [hb, ht]

/-- For a completion with positive natural conductor, gamma parameters of
real part greater than minus one, and a logarithmic derivative Dirichlet series
whose coefficients are bounded by degree times n log n, its logarithmic
derivative at real part three is bounded by half the logarithmic analytic
conductor, explicit endpoint order, and a constant times the degree. Combine
the arithmetic majorant and uniform digamma bound, then split the product
logarithm. This bounds the full norm needed in nearby-pole contour estimates. -/
theorem norm_logDeriv_le_log_analyticConductor_at_three {F L : ℂ → ℂ} {q d : ℕ} (hq : 1 ≤ q) (k : ℤ)
    (κ : Fin d → ℂ) (hκ : ∀ j, -1 < (κ j).re)
    (hreg :
      ∀ z,
        z ≠ 0 →
          z ≠ 1 → F z = (z * (1 - z)) ^ k * ((q : ℂ) ^ (z / 2) * archimedeanGammaFactor κ z * L z))
    {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ (d : ℝ) * n * Real.log n) {s : ℂ} (hs3 : s.re = 3) (hL : L s ≠ 0)
    (hdL : DifferentiableAt ℂ L s) (hlog : logDeriv L s = -LSeries a s) :
    ‖logDeriv F s‖ ≤
      2 * |(k : ℝ)| + Real.log (analyticConductor q κ s) / 2 +
        (d : ℝ) *
          ((‖Complex.log (Real.pi : ℂ)‖ + Real.pi + Gamma.digammaLogErrorBound) / 2 +
            ∑' n : ℕ, Real.log n / (n : ℝ) ^ 2) := by
  have hs : 1 < s.re := by
    rw [hs3]; norm_num only
  have hc :=
    norm_logDeriv_regularizedCompletion_at_three_le hq k hreg ha hs3
      (archimedeanGammaFactor_ne_zero hs hκ) hL (differentiableAt_archimedeanGammaFactor hs hκ) hdL
      hlog
  have hg := norm_logDeriv_archimedeanGammaFactor_at_three_le hs3 hκ
  have hb := hc.trans (add_le_add (add_le_add le_rfl hg) le_rfl)
  convert hb using 1
  rw [log_analyticConductor q hq κ]
  ring

end PseudoPrime.AnalyticNumberTheory.General

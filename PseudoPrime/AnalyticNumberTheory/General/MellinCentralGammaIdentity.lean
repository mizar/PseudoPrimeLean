/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.MellinCompletionGammaIdentity
public import PseudoPrime.AnalyticNumberTheory.General.MellinGammaContours

/-!
# Completed Mellin explicit identity with central gamma integrals

For nonnegative-real gamma shifts, move both gamma contributions from real
part two to the critical line without additional convergence hypotheses.
The zero sum still uses the entire regularized completion.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- For an entire order-one regularized completion with the stated functional
equation, nonnegative-real gamma shifts and coefficient-series identities,
an even smooth compact test gives the completed zero sum plus arithmetic sum
as conductor and endpoint contributions plus both central-line gamma integrals.
Apply the right-line completion identity and the original and dual residue-free
line shifts. This supplies the central gamma term used by LLS; conversion to
ordinary L-function zeros and the source pole normalization remain separate. -/
theorem mellin_zero_sum_add_arithmetic_eq_conductor_endpoints_central_gamma {F L : ℂ → ℂ} {ε : ℂ}
    {q d : ℕ} (hq : 1 ≤ q) (k : ℤ) (κ : Fin d → ℂ) (hκ : ∀ j, 0 ≤ (κ j).re)
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
      ((Real.log q : ℝ) : ℂ) * g 0 + (2 * (k : ℂ)) * mellin (logarithmicTestWeight g) 1 +
        (1 / (2 * Real.pi) : ℝ) •
          ((∫ T : ℝ,
              logDeriv (archimedeanGammaFactor κ) (((1 / 2 : ℝ) : ℂ) + T * Complex.I) *
                mellin (logarithmicTestWeight g) (((1 / 2 : ℝ) : ℂ) + T * Complex.I)) +
            (∫ T : ℝ,
              star (logDeriv (archimedeanGammaFactor κ) (((1 / 2 : ℝ) : ℂ) + (-T) * Complex.I)) *
                mellin (logarithmicTestWeight g) (((1 / 2 : ℝ) : ℂ) + T * Complex.I))) := by
  have hh :=
    mellin_zero_sum_add_arithmetic_eq_conductor_endpoints_gamma hq k κ
      (fun j ↦ lt_of_lt_of_le neg_one_lt_zero (hκ j)) hreg hε hfe hright hF h0 horder ha hL hdL hlog
      g he hc hg ha0 hs2 hlog2
  rw [mellin_archimedeanGamma_vertical_integral_eq_of_smooth_nonneg κ hκ (1 / 2) 2
      (by norm_num only) (by norm_num only) g he hc hg,
    mellin_reflected_archimedeanGamma_vertical_integral_eq_of_smooth_nonneg κ hκ (1 / 2) 2
      (by norm_num only) (by norm_num only) g he hc hg] at hh
  exact hh

end PseudoPrime.AnalyticNumberTheory.General

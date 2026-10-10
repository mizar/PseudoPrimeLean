/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.MellinCompletionZeroIdentity
public import PseudoPrime.AnalyticNumberTheory.General.MellinEndpointIntegrals

/-!
# Endpoint removal in the completed Mellin explicit identity

The original and reflected endpoint kernels have equal integrals.
Removing their sum leaves the conductor term and the two gamma integrals,
whose integrability follows from the already established completion identity.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- For arbitrary completion parameters and argument, subtracting half the conductor
logarithm leaves the integer endpoint kernel plus the gamma logarithmic derivative.
Expand the completion remainder and cancel the constant. This identifies the terms
whose Mellin integrals must be evaluated in the explicit formula. -/
theorem completion_remainder_eq_endpoint_add_gamma (q : ℂ) (k : ℤ) (G : ℂ → ℂ) (s : ℂ) :
    completionNonArithmeticLogDerivative q k G s - Complex.log q / 2 =
      (k : ℂ) * (1 / s + 1 / (s - 1)) + logDeriv G s := by
  rw [completionNonArithmeticLogDerivative]
  ring

/-- For arbitrary completion parameters on a real line, conjugating the remainder at
negative height leaves the original integer endpoint kernel and the reflected gamma
derivative. Use the remainder identity and conjugation of the endpoint kernel.
This retains the height reflection in the dual gamma contribution. -/
theorem star_reflected_completion_remainder (q : ℂ) (k : ℤ) (G : ℂ → ℂ) (σ T : ℝ) :
    star
        (completionNonArithmeticLogDerivative q k G ((σ : ℂ) + (-T) * Complex.I) -
          Complex.log q / 2) =
      (k : ℂ) * (1 / ((σ : ℂ) + T * Complex.I) + 1 / (((σ : ℂ) + T * Complex.I) - 1)) +
        star (logDeriv G ((σ : ℂ) + (-T) * Complex.I)) := by
  rw [completion_remainder_eq_endpoint_add_gamma, star_add, star_reflected_endpoint_kernel]

/-- For an even smooth compact test on a real line above one, integrability of the
non-arithmetic completion integrand implies integrability of the gamma integrand.
Subtract the integrable conductor and endpoint integrands, then cancel their terms.
This derives gamma integrability without an additional analytic premise. -/
theorem integrable_gamma_mellin_of_nonArithmetic (q : ℂ) (k : ℤ) (G : ℂ → ℂ) (g : ℝ → ℂ)
    (he : ∀ u : ℝ, g (-u) = g u) (hc : HasCompactSupport g) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (σ : ℝ)
    (hs : 1 < σ)
    (hi :
      MeasureTheory.Integrable
        (fun T : ℝ ↦
          completionNonArithmeticLogDerivative q k G ((σ : ℂ) + T * Complex.I) *
            mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I))) :
    MeasureTheory.Integrable
      (fun T : ℝ ↦
        logDeriv G ((σ : ℂ) + T * Complex.I) *
          mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) := by
  have hconst :=
    (verticalIntegrable_mellin_logarithmicTestWeight g he hc hg σ).const_mul (Complex.log q / 2)
  have hend := integrable_regularization_endpoint_mellin k g he hc hg σ hs
  apply ((hi.sub hconst).sub hend).congr
  exact
    MeasureTheory.ae_of_all _ fun T ↦ by
      dsimp only [Pi.sub_apply, completionNonArithmeticLogDerivative]
      ring

/-- For an even smooth compact test on a real line above one, integrability of the
reflected non-arithmetic integrand implies integrability of the reflected gamma
integrand. Subtract the conjugated conductor and the invariant endpoint kernel.
This provides the dual integral needed after endpoint removal. -/
theorem integrable_reflected_gamma_mellin_of_nonArithmetic (q : ℂ) (k : ℤ) (G : ℂ → ℂ) (g : ℝ → ℂ)
    (he : ∀ u : ℝ, g (-u) = g u) (hc : HasCompactSupport g) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (σ : ℝ)
    (hs : 1 < σ)
    (hd :
      MeasureTheory.Integrable
        (fun T : ℝ ↦
          star (completionNonArithmeticLogDerivative q k G ((σ : ℂ) + (-T) * Complex.I)) *
            mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I))) :
    MeasureTheory.Integrable
      (fun T : ℝ ↦
        star (logDeriv G ((σ : ℂ) + (-T) * Complex.I)) *
          mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) := by
  have hconst :=
    (verticalIntegrable_mellin_logarithmicTestWeight g he hc hg σ).const_mul
      (star (Complex.log q / 2))
  have hend := integrable_regularization_endpoint_mellin k g he hc hg σ hs
  apply ((hd.sub hconst).sub hend).congr
  exact
    MeasureTheory.ae_of_all _ fun T ↦ by
      dsimp only [Pi.sub_apply]
      rw [← sub_mul, ← star_sub, star_reflected_completion_remainder]
      ring

/-- For an even smooth compact test on a real line above one with integrable gamma
integrand, the conductor-free completion integral splits into endpoint and gamma
integrals. The endpoint integrability theorem permits integral linearity; the
pointwise completion identity identifies the integrands. -/
theorem integral_completion_remainder_eq_endpoint_add_gamma (q : ℂ) (k : ℤ) (G : ℂ → ℂ) (g : ℝ → ℂ)
    (he : ∀ u : ℝ, g (-u) = g u) (hc : HasCompactSupport g) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (σ : ℝ)
    (hs : 1 < σ)
    (hiG :
      MeasureTheory.Integrable
        (fun T : ℝ ↦
          logDeriv G ((σ : ℂ) + T * Complex.I) *
            mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I))) :
    (∫ T : ℝ,
        (completionNonArithmeticLogDerivative q k G ((σ : ℂ) + T * Complex.I) - Complex.log q / 2) *
          mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) =
      (∫ T : ℝ,
          ((k : ℂ) * (1 / ((σ : ℂ) + T * Complex.I) + 1 / (((σ : ℂ) + T * Complex.I) - 1))) *
            mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) +
        (∫ T : ℝ,
          logDeriv G ((σ : ℂ) + T * Complex.I) *
            mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) := by
  rw [←
    MeasureTheory.integral_add (integrable_regularization_endpoint_mellin k g he hc hg σ hs) hiG]
  apply MeasureTheory.integral_congr_ae
  exact
    MeasureTheory.ae_of_all _ fun T ↦ by
      dsimp only
      rw [completion_remainder_eq_endpoint_add_gamma, add_mul]

/-- For an even smooth compact test on a real line above one with integrable reflected
gamma integrand, the reflected conductor-free completion integral splits into the
original endpoint integral and the reflected gamma integral. Use conjugation of the
endpoint kernel and integral linearity. This evaluates the dual remainder. -/
theorem integral_reflected_completion_remainder_eq_endpoint_add_gamma (q : ℂ) (k : ℤ) (G : ℂ → ℂ)
    (g : ℝ → ℂ) (he : ∀ u : ℝ, g (-u) = g u) (hc : HasCompactSupport g)
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (σ : ℝ) (hs : 1 < σ)
    (hiG :
      MeasureTheory.Integrable
        (fun T : ℝ ↦
          star (logDeriv G ((σ : ℂ) + (-T) * Complex.I)) *
            mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I))) :
    (∫ T : ℝ,
        star
            (completionNonArithmeticLogDerivative q k G ((σ : ℂ) + (-T) * Complex.I) -
              Complex.log q / 2) *
          mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) =
      (∫ T : ℝ,
          ((k : ℂ) * (1 / ((σ : ℂ) + T * Complex.I) + 1 / (((σ : ℂ) + T * Complex.I) - 1))) *
            mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) +
        (∫ T : ℝ,
          star (logDeriv G ((σ : ℂ) + (-T) * Complex.I)) *
            mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) := by
  rw [←
    MeasureTheory.integral_add (integrable_regularization_endpoint_mellin k g he hc hg σ hs) hiG]
  apply MeasureTheory.integral_congr_ae
  exact
    MeasureTheory.ae_of_all _ fun T ↦ by
      dsimp only
      rw [star_reflected_completion_remainder, add_mul]

/-- For an even smooth compact test on a real line above one and integrable original
and reflected non-arithmetic integrands, the conductor-free pair equals
2*k*Mellin(phi)(1) plus the paired gamma integrals. Derive gamma integrability,
split both remainders, and evaluate the endpoint kernel. This removes all rational
endpoint integrals before shifting the gamma contour. -/
theorem normalized_paired_completion_remainder_eq_endpoints_add_gamma (q : ℂ) (k : ℤ) (G : ℂ → ℂ)
    (g : ℝ → ℂ) (he : ∀ u : ℝ, g (-u) = g u) (hc : HasCompactSupport g)
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (σ : ℝ) (hs : 1 < σ)
    (hi :
      MeasureTheory.Integrable
        (fun T : ℝ ↦
          completionNonArithmeticLogDerivative q k G ((σ : ℂ) + T * Complex.I) *
            mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)))
    (hd :
      MeasureTheory.Integrable
        (fun T : ℝ ↦
          star (completionNonArithmeticLogDerivative q k G ((σ : ℂ) + (-T) * Complex.I)) *
            mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I))) :
    (1 / (2 * Real.pi) : ℝ) •
        ((∫ T : ℝ,
            (completionNonArithmeticLogDerivative q k G ((σ : ℂ) + T * Complex.I) -
                Complex.log q / 2) *
              mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) +
          (∫ T : ℝ,
            star
                (completionNonArithmeticLogDerivative q k G ((σ : ℂ) + (-T) * Complex.I) -
                  Complex.log q / 2) *
              mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I))) =
      (2 * (k : ℂ)) * mellin (logarithmicTestWeight g) 1 +
        (1 / (2 * Real.pi) : ℝ) •
          ((∫ T : ℝ,
              logDeriv G ((σ : ℂ) + T * Complex.I) *
                mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) +
            (∫ T : ℝ,
              star (logDeriv G ((σ : ℂ) + (-T) * Complex.I)) *
                mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I))) := by
  rw [integral_completion_remainder_eq_endpoint_add_gamma q k G g he hc hg σ hs
      (integrable_gamma_mellin_of_nonArithmetic q k G g he hc hg σ hs hi),
    integral_reflected_completion_remainder_eq_endpoint_add_gamma q k G g he hc hg σ hs
      (integrable_reflected_gamma_mellin_of_nonArithmetic q k G g he hc hg σ hs hd)]
  simp only [smul_add]
  rw [normalized_integral_regularization_endpoint k g he hc hg σ hs]
  simp only [Complex.real_smul]
  ring

/-- For an entire order-one regularized completion with the stated functional equation,
right-half-plane nonvanishing and coefficient-series identities, an even smooth
compact test gives a completed zero sum plus arithmetic sum equal to log(q)*g(0),
2*k*Mellin(phi)(1), and the paired gamma integrals on real part two. Derive the
non-arithmetic integrability and apply the conductor and endpoint evaluations.
The gamma contour shift and the ordinary L-function zero ledger are still needed
to obtain the source's Mellin explicit formula. -/
theorem mellin_zero_sum_add_arithmetic_eq_conductor_endpoints_gamma {F L : ℂ → ℂ} {ε : ℂ} {q d : ℕ}
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
      ((Real.log q : ℝ) : ℂ) * g 0 + (2 * (k : ℂ)) * mellin (logarithmicTestWeight g) 1 +
        (1 / (2 * Real.pi) : ℝ) •
          ((∫ T : ℝ,
              logDeriv (archimedeanGammaFactor κ) (((2 : ℝ) : ℂ) + T * Complex.I) *
                mellin (logarithmicTestWeight g) (((2 : ℝ) : ℂ) + T * Complex.I)) +
            (∫ T : ℝ,
              star (logDeriv (archimedeanGammaFactor κ) (((2 : ℝ) : ℂ) + (-T) * Complex.I)) *
                mellin (logarithmicTestWeight g) (((2 : ℝ) : ℂ) + T * Complex.I))) := by
  obtain ⟨hi, hd⟩ :=
    integrable_paired_nonArithmetic_of_completion hq k κ hκ hreg hε hfe hright hF h0 horder ha hL
      hdL hlog g he hc hg hs2 hlog2
  rw [mellin_zero_sum_add_arithmetic_eq_conductor_add_remainder hq k κ hκ hreg hε hfe hright hF h0
      horder ha hL hdL hlog g he hc hg ha0 hs2 hlog2,
    normalized_paired_completion_remainder_eq_endpoints_add_gamma q k (archimedeanGammaFactor κ) g
      he hc hg 2 (by norm_num only) hi hd,
    add_assoc]

end PseudoPrime.AnalyticNumberTheory.General

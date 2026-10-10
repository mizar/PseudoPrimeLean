/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.MellinDualArithmetic
public import PseudoPrime.AnalyticNumberTheory.General.CompletedProductBounds

/-!
# Mellin integrals of completion factors

Mellin inversion evaluates constant conductor contributions. The completion
product rule separates the non-arithmetic and ordinary logarithmic derivatives,
with integrability of the remainder derived from the two known integrals.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- For an even smooth compact test, its Mellin transform on any vertical line
has normalized integral g(0). Evaluate the proved Mellin inversion at one.
This is the mass identity for height-independent terms in the explicit formula. -/
theorem normalized_integral_mellin_logarithmicTestWeight (g : ℝ → ℂ) (he : ∀ u : ℝ, g (-u) = g u)
    (hc : HasCompactSupport g) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (σ : ℝ) :
    (1 / (2 * Real.pi) : ℝ) •
        (∫ T : ℝ, mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) =
      g 0 := by
  have hi := mellinInv_mellin_logarithmicTestWeight g he hc hg σ (x := 1) zero_lt_one
  simpa only [mellinInv, Complex.ofReal_one, Complex.one_cpow, one_smul,
    logarithmicTestWeight_one] using hi

/-- For any complex constant and an even smooth compact test, its normalized
weighted Mellin integral equals that constant times g(0). Factor the constant
out of the integral and apply inversion at one. This evaluates conductor terms. -/
theorem normalized_integral_const_mul_mellin_logarithmicTestWeight (c : ℂ) (g : ℝ → ℂ)
    (he : ∀ u : ℝ, g (-u) = g u) (hc : HasCompactSupport g) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
    (σ : ℝ) :
    (1 / (2 * Real.pi) : ℝ) •
        (∫ T : ℝ, c * mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) =
      c * g 0 := by
  rw [MeasureTheory.integral_const_mul, ← mul_smul_comm,
    normalized_integral_mellin_logarithmicTestWeight g he hc hg σ]

/-- For a natural conductor and an even smooth compact test, the original and
dual conductor terms together contribute log(q)*g(0) on any vertical line.
Each is a constant Mellin integral; the real conductor logarithm is fixed
by conjugation. This gives the conductor term of the explicit formula. -/
theorem normalized_integral_paired_conductor_mellin (q : ℕ) (g : ℝ → ℂ) (he : ∀ u : ℝ, g (-u) = g u)
    (hc : HasCompactSupport g) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (σ : ℝ) :
    (1 / (2 * Real.pi) : ℝ) •
        ((∫ T : ℝ,
            ((Real.log q : ℝ) : ℂ) / 2 *
              mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) +
          (∫ T : ℝ,
            star (((Real.log q : ℝ) : ℂ) / 2) *
              mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I))) =
      ((Real.log q : ℝ) : ℂ) * g 0 := by
  rw [smul_add, normalized_integral_const_mul_mellin_logarithmicTestWeight _ g he hc hg σ,
    normalized_integral_const_mul_mellin_logarithmicTestWeight _ g he hc hg σ]
  simp only [Complex.star_def, map_div₀, Complex.conj_ofReal, map_ofNat]
  ring

/-- The logarithmic contribution of endpoint regularization, conductor and gamma
factor to a completion: k*(1/s+1/(s-1))+log(q)/2+G'/G. The complex conductor,
integer endpoint order, gamma function and evaluation point are explicit
inputs. This separates ordinary L'/L in the completion integral. -/
noncomputable def completionNonArithmeticLogDerivative (q : ℂ) (k : ℤ) (G : ℂ → ℂ) (s : ℂ) : ℂ :=
  (k : ℂ) * (1 / s + 1 / (s - 1)) + Complex.log q / 2 + logDeriv G s

/-- For a regularized completion on a vertical line avoiding both endpoints,
with differentiable nonzero gamma and ordinary factors, integrability of
the weighted completed and ordinary logarithmic derivatives implies
integrability of the non-arithmetic contribution. The product rule identifies
it with their difference. No separate gamma integral convergence is assumed. -/
theorem integrable_completionNonArithmetic_mellin {F G L : ℂ → ℂ} {q : ℂ} (hq : q ≠ 0) (k : ℤ)
    (hreg : ∀ z, z ≠ 0 → z ≠ 1 → F z = (z * (1 - z)) ^ k * (q ^ (z / 2) * G z * L z)) (σ : ℝ)
    (W : ℂ → ℂ) (hs : ∀ T : ℝ, (σ : ℂ) + T * Complex.I ≠ 0)
    (h1 : ∀ T : ℝ, (σ : ℂ) + T * Complex.I ≠ 1) (hG : ∀ T : ℝ, G ((σ : ℂ) + T * Complex.I) ≠ 0)
    (hL : ∀ T : ℝ, L ((σ : ℂ) + T * Complex.I) ≠ 0)
    (hdG : ∀ T : ℝ, DifferentiableAt ℂ G ((σ : ℂ) + T * Complex.I))
    (hdL : ∀ T : ℝ, DifferentiableAt ℂ L ((σ : ℂ) + T * Complex.I))
    (hiF :
      MeasureTheory.Integrable
        (fun T : ℝ ↦ logDeriv F ((σ : ℂ) + T * Complex.I) * W ((σ : ℂ) + T * Complex.I)))
    (hiL :
      MeasureTheory.Integrable
        (fun T : ℝ ↦ logDeriv L ((σ : ℂ) + T * Complex.I) * W ((σ : ℂ) + T * Complex.I))) :
    MeasureTheory.Integrable
      (fun T : ℝ ↦
        completionNonArithmeticLogDerivative q k G ((σ : ℂ) + T * Complex.I) *
          W ((σ : ℂ) + T * Complex.I)) := by
  apply (hiF.sub hiL).congr
  exact
    MeasureTheory.ae_of_all _ fun T ↦ by
      dsimp only [Pi.sub_apply]
      rw [logDeriv_regularizedCompletion hq k hreg (hs T) (h1 T) (hG T) (hL T) (hdG T) (hdL T),
        completionNonArithmeticLogDerivative]
      ring

/-- Under the regularization identity and nonzero differentiable factors on a
vertical line avoiding the endpoints, the weighted completed logarithmic
integral splits into its non-arithmetic and ordinary contributions. Derive
integrability of the remainder from the two given integrals, then integrate
the product-rule identity. This connects completion zeros to arithmetic evaluation. -/
theorem integral_logDeriv_completion_eq_nonArithmetic_add {F G L : ℂ → ℂ} {q : ℂ} (hq : q ≠ 0)
    (k : ℤ) (hreg : ∀ z, z ≠ 0 → z ≠ 1 → F z = (z * (1 - z)) ^ k * (q ^ (z / 2) * G z * L z))
    (σ : ℝ) (W : ℂ → ℂ) (hs : ∀ T : ℝ, (σ : ℂ) + T * Complex.I ≠ 0)
    (h1 : ∀ T : ℝ, (σ : ℂ) + T * Complex.I ≠ 1) (hG : ∀ T : ℝ, G ((σ : ℂ) + T * Complex.I) ≠ 0)
    (hL : ∀ T : ℝ, L ((σ : ℂ) + T * Complex.I) ≠ 0)
    (hdG : ∀ T : ℝ, DifferentiableAt ℂ G ((σ : ℂ) + T * Complex.I))
    (hdL : ∀ T : ℝ, DifferentiableAt ℂ L ((σ : ℂ) + T * Complex.I))
    (hiF :
      MeasureTheory.Integrable
        (fun T : ℝ ↦ logDeriv F ((σ : ℂ) + T * Complex.I) * W ((σ : ℂ) + T * Complex.I)))
    (hiL :
      MeasureTheory.Integrable
        (fun T : ℝ ↦ logDeriv L ((σ : ℂ) + T * Complex.I) * W ((σ : ℂ) + T * Complex.I))) :
    (∫ T : ℝ, logDeriv F ((σ : ℂ) + T * Complex.I) * W ((σ : ℂ) + T * Complex.I)) =
      (∫ T : ℝ,
          completionNonArithmeticLogDerivative q k G ((σ : ℂ) + T * Complex.I) *
            W ((σ : ℂ) + T * Complex.I)) +
        (∫ T : ℝ, logDeriv L ((σ : ℂ) + T * Complex.I) * W ((σ : ℂ) + T * Complex.I)) := by
  rw [←
    MeasureTheory.integral_add
      (integrable_completionNonArithmetic_mellin hq k hreg σ W hs h1 hG hL hdG hdL hiF hiL) hiL]
  apply MeasureTheory.integral_congr_ae
  exact
    MeasureTheory.ae_of_all _ fun T ↦ by
      dsimp only [Pi.add_apply]
      rw [logDeriv_regularizedCompletion hq k hreg (hs T) (h1 T) (hG T) (hL T) (hdG T) (hdL T),
        completionNonArithmeticLogDerivative]
      ring

/-- For an even smooth compact test with integrable weighted non-arithmetic
completion derivative, its normalized integral splits into log(q)*g(0)/2
and the endpoint-plus-gamma integral. The remainder is integrable by subtracting
the constant conductor contribution. Inversion at one evaluates that constant.
This removes the conductor integral before evaluating the remaining factors. -/
theorem normalized_integral_nonArithmetic_eq_conductor_add (q : ℂ) (k : ℤ) (G : ℂ → ℂ) (g : ℝ → ℂ)
    (he : ∀ u : ℝ, g (-u) = g u) (hc : HasCompactSupport g) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (σ : ℝ)
    (hi :
      MeasureTheory.Integrable
        (fun T : ℝ ↦
          completionNonArithmeticLogDerivative q k G ((σ : ℂ) + T * Complex.I) *
            mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I))) :
    (1 / (2 * Real.pi) : ℝ) •
        (∫ T : ℝ,
          completionNonArithmeticLogDerivative q k G ((σ : ℂ) + T * Complex.I) *
            mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) =
      (Complex.log q / 2) * g 0 +
        (1 / (2 * Real.pi) : ℝ) •
          (∫ T : ℝ,
            ((k : ℂ) * (1 / ((σ : ℂ) + T * Complex.I) + 1 / (((σ : ℂ) + T * Complex.I) - 1)) +
                logDeriv G ((σ : ℂ) + T * Complex.I)) *
              mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) := by
  have hconst :=
    (verticalIntegrable_mellin_logarithmicTestWeight g he hc hg σ).const_mul (Complex.log q / 2)
  have hrem :
    MeasureTheory.Integrable
      (fun T : ℝ ↦
        ((k : ℂ) * (1 / ((σ : ℂ) + T * Complex.I) + 1 / (((σ : ℂ) + T * Complex.I) - 1)) +
            logDeriv G ((σ : ℂ) + T * Complex.I)) *
          mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) := by
    apply (hi.sub hconst).congr
    exact
      MeasureTheory.ae_of_all _ fun T ↦ by
        dsimp only [Pi.sub_apply, completionNonArithmeticLogDerivative]
        ring
  rw [← normalized_integral_const_mul_mellin_logarithmicTestWeight (Complex.log q / 2) g he hc hg σ,
    ← smul_add, ← MeasureTheory.integral_add hconst hrem]
  congr 1
  apply MeasureTheory.integral_congr_ae
  exact
    MeasureTheory.ae_of_all _ fun T ↦ by
      dsimp only [Pi.add_apply, completionNonArithmeticLogDerivative]
      ring

/-- For an even smooth compact test and integrable original and reflected dual
weighted values of R, subtracting a constant c from both factors removes
(c+conjugate(c))*g(0) from their normalized paired integral. Constant-weight
integrability follows from Mellin decay, and inversion at one evaluates the
two subtracted constants. This isolates the conductor from a completion pair. -/
theorem normalized_integral_paired_eq_const_add_remainder (R : ℂ → ℂ) (c : ℂ) (g : ℝ → ℂ)
    (he : ∀ u : ℝ, g (-u) = g u) (hc : HasCompactSupport g) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (σ : ℝ)
    (hi :
      MeasureTheory.Integrable
        (fun T : ℝ ↦
          R ((σ : ℂ) + T * Complex.I) * mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)))
    (hd :
      MeasureTheory.Integrable
        (fun T : ℝ ↦
          star (R ((σ : ℂ) + (-T) * Complex.I)) *
            mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I))) :
    (1 / (2 * Real.pi) : ℝ) •
        ((∫ T : ℝ,
            R ((σ : ℂ) + T * Complex.I) *
              mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) +
          (∫ T : ℝ,
            star (R ((σ : ℂ) + (-T) * Complex.I)) *
              mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I))) =
      (c + star c) * g 0 +
        (1 / (2 * Real.pi) : ℝ) •
          ((∫ T : ℝ,
              (R ((σ : ℂ) + T * Complex.I) - c) *
                mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) +
            (∫ T : ℝ,
              star (R ((σ : ℂ) + (-T) * Complex.I) - c) *
                mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I))) := by
  have hc₁ := (verticalIntegrable_mellin_logarithmicTestWeight g he hc hg σ).const_mul c
  have hc₂ := (verticalIntegrable_mellin_logarithmicTestWeight g he hc hg σ).const_mul (star c)
  simp only [star_sub, sub_mul, MeasureTheory.integral_sub hi hc₁,
    MeasureTheory.integral_sub hd hc₂]
  rw [smul_add, smul_add, smul_sub, smul_sub,
    normalized_integral_const_mul_mellin_logarithmicTestWeight c g he hc hg σ,
    normalized_integral_const_mul_mellin_logarithmicTestWeight (star c) g he hc hg σ, add_mul]
  abel

end PseudoPrime.AnalyticNumberTheory.General

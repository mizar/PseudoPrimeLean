/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaCentralDigammaSeries
public import PseudoPrime.LLS.TriangularGammaIntegralSeries

/-! # Signed central Gamma archimedean resolvent series

Apply the common parity identity to the actual Gamma kernel before taking norms.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Input: any complex Dirichlet character and positive Mellin scales.
Claim: a common parity base gives the actual central Gamma integral as its baseline plus
an absolutely integrable reciprocal-difference series, with the signed coefficients retained.
Proof: use the parity identity, actual kernel integrability and the proved digamma exchange.
Role: exact archimedean representation for subsequent one-sided sign estimates. -/
theorem gamma_central_archimedean_integral_eq_resolvent_series {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    ∃ b : ℝ,
      1 / 4 ≤ b ∧
        b ≤ 1 ∧
        ∀ x : ℝ,
          0 < x →
            ((1 / (2 * Real.pi) : ℝ) : ℂ) *
                (∫ t : ℝ,
                  logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) * gammaCentralMellinWeight x t) =
              ((-Complex.log Real.pi + Complex.digamma (b : ℂ)) / 2) *
                  (((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, gammaCentralMellinWeight x t)) +
                (((1 / (2 * Real.pi) : ℝ) : ℂ) / 2) *
                  (∑' n : ℕ,
                    ∫ t : ℝ,
                      (1 / ((b + n : ℝ) : ℂ) - 1 / (((b + n : ℝ) : ℂ) + Complex.I * (t / 2))) *
                        gammaCentralMellinWeight x t) := by
  obtain ⟨b, hb, hb1, hp⟩ := gamma_central_eq_complex_digamma χ
  refine ⟨b, hb, hb1, ?_⟩
  intro x hx
  let W := gammaCentralMellinWeight x
  let B := (-Complex.log Real.pi + Complex.digamma (b : ℂ)) / 2
  let D := fun t : ℝ ↦
    (Complex.digamma ((b : ℂ) + Complex.I * (t / 2)) - Complex.digamma (b : ℂ)) * W t
  have hW : MeasureTheory.Integrable W := integrable_gammaCentralMellinWeight hx
  have hG :
    MeasureTheory.Integrable
      (fun t : ℝ ↦ logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) * W t) := by
    have h :=
      MellinKernel.integrable_gammaFactor_power_line gammaMellinKernel χ (c := 0) (x := x)
        (by norm_num only)
        (by
          change (0 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
        (by norm_num only) hx
    simpa only [Complex.ofReal_zero, zero_add, W, gammaCentralMellinWeight, mul_assoc] using h
  have he (t : ℝ) :
    logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) * W t = B * W t + (1 / 2 : ℂ) * D t := by
    rw [hp]
    dsimp only [B, D]
    ring
  have hD : MeasureTheory.Integrable D :=
    ((hG.sub (hW.const_mul B)).const_mul (2 : ℂ)).congr
      (MeasureTheory.ae_of_all _
        (fun t ↦ by
          change 2 * (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) * W t - B * W t) = D t
          rw [he]
          ring))
  have hseries :=
    gamma_central_digamma_vertical_sub_integral_eq_tsum
      (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1 / 4) hb) hx
  change
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) * W t) =
      _
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ he),
    MeasureTheory.integral_add (hW.const_mul B) (hD.const_mul (1 / 2 : ℂ)),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  change
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (B * (∫ t : ℝ, W t) +
          (1 / 2 : ℂ) *
            (∫ t : ℝ,
              (Complex.digamma ((b : ℂ) + Complex.I * (t / 2)) - Complex.digamma (b : ℂ)) *
                gammaCentralMellinWeight x t)) =
      _
  rw [hseries]
  dsimp only [B, W]
  ring

/-- Input: any complex Dirichlet character and positive Mellin scales.
Claim: the signed central Gamma series has the explicit inverse-Mellin baseline density.
Proof: substitute the certified density into the exact resolvent-series identity.
Role: scalar baseline for the subsequent reciprocal inversion and archimedean sign estimate. -/
theorem gamma_central_archimedean_integral_eq_density_series {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ∃ b : ℝ,
      1 / 4 ≤ b ∧
        b ≤ 1 ∧
        ∀ x : ℝ,
          0 < x →
            ((1 / (2 * Real.pi) : ℝ) : ℂ) *
                (∫ t : ℝ,
                  logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) * gammaCentralMellinWeight x t) =
              ((-Complex.log Real.pi + Complex.digamma (b : ℂ)) / 2) *
                  ((Real.sqrt (x⁻¹) * Real.exp (-x⁻¹) : ℝ) : ℂ) +
                (((1 / (2 * Real.pi) : ℝ) : ℂ) / 2) *
                  (∑' n : ℕ,
                    ∫ t : ℝ,
                      (1 / ((b + n : ℝ) : ℂ) - 1 / (((b + n : ℝ) : ℂ) + Complex.I * (t / 2))) *
                        gammaCentralMellinWeight x t) := by
  obtain ⟨b, hb, hb1, h⟩ := gamma_central_archimedean_integral_eq_resolvent_series χ
  refine ⟨b, hb, hb1, ?_⟩
  intro x hx
  have he := h x hx
  rw [gamma_central_kernel_integral_eq_density hx] at he
  exact he

end PseudoPrime.LLS.PaperStatements

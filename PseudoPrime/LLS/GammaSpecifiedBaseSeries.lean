/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaExactParity

/-! # Central Gamma series with a specified positive digamma base -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Given the central digamma identity at a specified positive base, the
actual Gamma integral has the certified density-and-resolvent series.
Integrability follows from the actual kernel and Gamma factor. This helper
allows the exact parity base to be retained throughout the inversion argument. -/
theorem gamma_central_archimedean_integral_eq_density_series_of_base {q : ℕ}
    (χ : DirichletCharacter ℂ q) {b : ℝ} (hb : 0 < b)
    (hp :
      ∀ t : ℝ,
        logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) =
          (-Complex.log Real.pi + Complex.digamma ((b : ℂ) + Complex.I * (t / 2))) / 2)
    {x : ℝ} (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) * gammaCentralMellinWeight x t) =
      ((-Complex.log Real.pi + Complex.digamma (b : ℂ)) / 2) *
          ((Real.sqrt (x⁻¹) * Real.exp (-x⁻¹) : ℝ) : ℂ) +
        (((1 / (2 * Real.pi) : ℝ) : ℂ) / 2) *
          (∑' n : ℕ,
            ∫ t : ℝ,
              (1 / ((b + n : ℝ) : ℂ) - 1 / (((b + n : ℝ) : ℂ) + Complex.I * (t / 2))) *
                gammaCentralMellinWeight x t) := by
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
  have hseries := gamma_central_digamma_vertical_sub_integral_eq_tsum hb hx
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
  rw [← gamma_central_kernel_integral_eq_density hx]
  dsimp only [B, W]
  ring

/-- With a specified positive digamma base, the actual normalized Gamma
integral has the exact real scalar series representation. Apply the certified
reciprocal inversions to the convergent series. The helper retains the exact
parity base supplied by the character identity in the final application. -/
theorem gamma_central_archimedean_integral_re_eq_scalar_series_of_base {q : ℕ}
    (χ : DirichletCharacter ℂ q) {b : ℝ} (hb : 0 < b)
    (hp :
      ∀ t : ℝ,
        logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) =
          (-Complex.log Real.pi + Complex.digamma ((b : ℂ) + Complex.I * (t / 2))) / 2)
    {x : ℝ} (hx : 0 < x) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) * gammaCentralMellinWeight x t)).re =
      ((-Real.log Real.pi + (Complex.digamma (b : ℂ)).re) / 2) * (Real.sqrt x⁻¹ * Real.exp (-x⁻¹)) +
        (1 / 2 : ℝ) *
          (∑' n : ℕ,
            (Real.sqrt x⁻¹ * Real.exp (-x⁻¹) / (b + n) -
              ∫ r : ℝ in Set.Ioi 0, gammaResolventScalarDensity (b + n) x r)) := by
  let C : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  let K : ℝ := Real.sqrt x⁻¹ * Real.exp (-x⁻¹)
  let J := fun n : ℕ ↦
    ∫ t : ℝ,
      (1 / ((b + n : ℝ) : ℂ) - 1 / (((b + n : ℝ) : ℂ) + Complex.I * (t / 2))) *
        gammaCentralMellinWeight x t
  let F := fun n : ℕ ↦ K / (b + n) - ∫ r : ℝ in Set.Ioi 0, gammaResolventScalarDensity (b + n) x r
  have hJ : C * (∑' n : ℕ, J n) = ((∑' n : ℕ, F n) : ℝ) := by
    rw [← tsum_mul_left, Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    simpa only [C, J, F, K, mul_div_assoc] using
      gamma_central_resolvent_difference_integral_eq_real
        (add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg n)) hx
  have he := gamma_central_archimedean_integral_eq_density_series_of_base χ hb hp hx
  have he' :
    C * (∫ t : ℝ, logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) * gammaCentralMellinWeight x t) =
      ((-Complex.log Real.pi + Complex.digamma (b : ℂ)) / 2) * (K : ℂ) +
        (1 / 2 : ℂ) * (C * (∑' n : ℕ, J n)) := by
    rw [he]
    dsimp only [C, K, J]
    ring
  rw [he', hJ]
  norm_num only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero, Complex.div_ofNat_re, Complex.neg_re, ← Complex.ofReal_log Real.pi_pos.le,
    show (1 / 2 : ℂ).re = (1 / 2 : ℝ) from by norm_num only [Complex.div_ofNat_re, Complex.one_re],
    show (1 / 2 : ℂ).im = (0 : ℝ) from by norm_num only [Complex.div_ofNat_im, Complex.one_im],
    Complex.one_re, Complex.one_im]
  rfl

/-- The character selects an exact parity base, one quarter or three quarters,
for which the real scalar series represents the actual central Gamma integral
at every positive scale. The auxiliary base identity is discharged by parity,
so the public result has no extra analytic hypothesis. -/
theorem gamma_central_archimedean_integral_re_eq_scalar_exact_parity {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    ∃ b : ℝ,
      (b = 1 / 4 ∨ b = 3 / 4) ∧
        ∀ x : ℝ,
          0 < x →
            (((1 / (2 * Real.pi) : ℝ) : ℂ) *
                  (∫ t : ℝ,
                    logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
                      gammaCentralMellinWeight x t)).re =
              ((-Real.log Real.pi + (Complex.digamma (b : ℂ)).re) / 2) *
                  (Real.sqrt x⁻¹ * Real.exp (-x⁻¹)) +
                (1 / 2 : ℝ) *
                  (∑' n : ℕ,
                    (Real.sqrt x⁻¹ * Real.exp (-x⁻¹) / (b + n) -
                      ∫ r : ℝ in Set.Ioi 0, gammaResolventScalarDensity (b + n) x r)) := by
  obtain ⟨b, hb, hp⟩ := gamma_central_eq_complex_digamma_exact_parity χ
  have hb0 : 0 < b := by rcases hb with rfl | rfl <;> norm_num only
  refine ⟨b, hb, ?_⟩
  intro x hx
  exact gamma_central_archimedean_integral_re_eq_scalar_series_of_base χ hb0 hp hx

end PseudoPrime.LLS.PaperStatements
